(* Own an external SAT command, including its ordinary shell descendants.
   No signal handlers or process-global cleanup hooks are installed. *)
structure SatProcess :>
  sig val system : string -> OS.Process.status end =
struct

(* Protect the brief inheritable-FD window, including pipe creation.
   The fork fallback participates too, so it cannot inherit fast-path FDs. *)
val spawn_lock = Mutex.mutex ()

(* Retire ownership and close as one cancellation-deferred transition. An
   interrupt must neither lose an open FD nor leave a closed FD registered
   for cleanup: another thread may already have reused its number. Preserve
   the caller's current attributes (also when already inside cleanup). *)
fun close_owned descriptors fd =
  let
    val attributes = Thread.getAttributes ()
    val _ = Thread.setAttributes
      [Thread.InterruptState Thread.InterruptDefer]
    val _ =
      (descriptors := List.filter (fn other => other <> fd) (!descriptors);
       Posix.IO.close fd)
      handle e =>
        ((Thread.setAttributes attributes handle _ => ()); raise e)
  in Thread.setAttributes attributes end

(* Raised only before opening the command gate: retrying the fork route
   cannot run the user's command twice. *)
exception FastUnavailable

(* Poly/ML 5.9.x's Unix.execute uses fork even though it execs in native
   code.  Call POSIX spawn instead: no ML executes in a forked live heap,
   and NULL file actions preserve the caller's actual stdin/stdout (including
   sockets and file offsets).  Unlike Unix.execute there are no unused stdio
   pipes to drain/close.  Only standard POSIX types cross this interface:
   pid_t is int on the supported Unix targets, and argv/envp are terminated
   arrays of strings.  Symbol lookup is lazy; missing spawn support takes
   the unchanged fork route.  The spawn attribute object and the signal sets
   stay opaque: they are only initialised/destroyed by libc, each in a buffer
   larger than its type on every supported target (posix_spawnattr_t is a
   pointer on Darwin and the BSDs, 336 bytes on glibc/musl; sigset_t is at
   most 128 bytes). *)
local
  open Foreign
  val spawn = buildCall6
    (getSymbol (loadExecutable ()) "posix_spawn",
     (cStar cInt,cString,cPointer,cPointer,
      cVectorPointer (cOptionPtr cString),
      cVectorPointer (cOptionPtr cString)),cInt)
    handle Foreign _ => fn _ => raise FastUnavailable
  fun attribute name argument = buildCall2
    (getSymbol (loadExecutable ()) ("posix_spawnattr_" ^ name),
     (cPointer,argument),cInt)
    handle Foreign _ => fn _ => raise FastUnavailable
  val attr_init = buildCall1
    (getSymbol (loadExecutable ()) "posix_spawnattr_init",cPointer,cInt)
    handle Foreign _ => fn _ => raise FastUnavailable
  val attr_destroy = buildCall1
    (getSymbol (loadExecutable ()) "posix_spawnattr_destroy",cPointer,cInt)
    handle Foreign _ => fn _ => raise FastUnavailable
  val attr_setflags = attribute "setflags" cShort
  val attr_setpgroup = attribute "setpgroup" cInt
  val attr_setsigmask = attribute "setsigmask" cPointer
  val attr_setsigdefault = attribute "setsigdefault" cPointer
  fun sigset name = buildCall1
    (getSymbol (loadExecutable ()) name,cPointer,cInt)
    handle Foreign _ => fn _ => raise FastUnavailable
  val sigemptyset = sigset "sigemptyset"
  val sigfillset = sigset "sigfillset"
  val sigdelset = buildCall2
    (getSymbol (loadExecutable ()) "sigdelset",(cPointer,cInt),cInt)
    handle Foreign _ => fn _ => raise FastUnavailable
  (* Every signal whose disposition can be set: OpenBSD's posix_spawn fails
     in the child when the defaults set holds SIGKILL or SIGSTOP. *)
  fun settable_signals set =
    let fun remove signal =
          sigdelset (set,SysWord.toInt (Posix.Signal.toWord signal)) = 0
    in sigfillset set = 0 andalso remove Posix.Signal.kill andalso
       remove Posix.Signal.stop end
  (* POSIX_SPAWN_SETPGROUP is 0x02 on every ABI accepted by setsid_path.
     POSIX_SPAWN_SETSIGDEF and _SETSIGMASK are 0x04 and 0x08 on Linux and
     Darwin, 0x10 and 0x20 on the BSDs. *)
  val setpgroup_flag = 0x02
  fun signal_flags () =
    if List.exists (fn (key,value) => key = "sysname" andalso
         (String.isSuffix "BSD" value orelse value = "DragonFly"))
       (Posix.ProcEnv.uname ())
    then 0x30 else 0x0C
  val attr_bytes = 0w1024
  val wait = buildCall3
    (getSymbol (loadExecutable ()) "waitpid",(cInt,cStar cInt,cInt),cInt)
    handle Foreign _ => fn _ => ~1
  fun strings ss = Vector.fromList (List.map SOME ss @ [NONE])
in
  (* Only used with interrupts deferred, after SIGKILL.  Poly/ML's Basis
     waitpid polls WNOHANG with a 10ms sleep, even for this dying child.
     Keep the interruptible command wait in ML; block natively only to reap
     our exact owned PID.  On EINTR/error use the Basis error/retry path. *)
  fun native_reap pid =
    let
      fun basis () = ignore (Posix.Process.waitpid
        (Posix.Process.W_CHILD pid,[]))
      val number = SysWord.toInt (Posix.Process.pidToWord pid)
    in
      if (wait (number,ref 0,0) handle Foreign _ => ~1) = number
      then () else basis ()
    end

  fun spawn_with attr (path,args) =
    let
      val pid = ref 0
      val error = spawn (pid,path,Memory.null,attr,
        strings (OS.Path.file path :: args),
        strings (Posix.ProcEnv.environ ()))
    in
      if error = 0 then Posix.Process.wordToPid (SysWord.fromInt (!pid))
      else raise FastUnavailable
    end handle Foreign _ => raise FastUnavailable

  (* The process starts with an empty signal mask and every signal at its
     default disposition.  posix_spawn would otherwise pass on the calling
     thread's mask and the parent's ignored signals: Poly/ML blocks almost
     every signal in ML threads and ignores SIGPIPE.  dash clears the mask
     at startup but bash keeps it, and an ignored signal stays ignored in
     every descendant, the solver included.  With group, the process also
     leads a new process group: the fork route's child setpgid, without
     duplicating the live ML heap.  Called with interrupts deferred; the
     attribute is always released. *)
  fun native_spawn group command =
    let
      val block = Memory.malloc (0w3 * attr_bytes)
        handle Foreign _ => raise FastUnavailable
      val attr = block
      val no_signals = Memory.++ (block,attr_bytes)
      val defaults = Memory.++ (block,0w2 * attr_bytes)
      (* Never raise after a successful spawn: its PID must reach owner. *)
      fun release () = Memory.free block handle _ => ()
      val _ = if (attr_init attr handle e => (release (); raise e)) = 0
              then () else (release (); raise FastUnavailable)
      fun finish () = ((ignore (attr_destroy attr) handle _ => ());
                       release ())
      val pid =
        (if sigemptyset no_signals = 0 andalso
            settable_signals defaults andalso
            attr_setflags (attr,signal_flags () +
              (if group then setpgroup_flag else 0)) = 0 andalso
            attr_setsigmask (attr,no_signals) = 0 andalso
            attr_setsigdefault (attr,defaults) = 0 andalso
            (not group orelse attr_setpgroup (attr,0) = 0)
         then spawn_with attr command else raise FastUnavailable)
        handle e => (finish (); raise e)
    in finish (); pid end
    handle Foreign _ => raise FastUnavailable
end

fun retry f = f () handle e as OS.SysErr (_,SOME code) =>
  if code = Posix.Error.intr then retry f else raise e
fun write_all fd bytes =
  let
    fun loop slice = if Word8VectorSlice.length slice = 0 then ()
      else let val n = retry (fn () => Posix.IO.writeVec (fd,slice))
           in if n = 0 then raise Fail "SatProcess: short write"
              else loop (Word8VectorSlice.subslice (slice,n,NONE)) end
  in loop (Word8VectorSlice.full bytes) end
fun fdpath fd = "/dev/fd/" ^
  Int.toString (SysWord.toInt (Posix.FileSys.fdToWord fd))
fun quote s = "'" ^ String.translate
  (fn #"'" => "'\\''" | c => str c) s ^ "'"
fun signal target = retry (fn () =>
  Posix.Process.kill (target,Posix.Signal.kill))
  handle e as OS.SysErr (_,SOME code) =>
    if code = Posix.Error.srch then () else raise e

(* How spawn_system creates the owned supervisor: as the session leader
   via setsid -w, or (no setsid program) as a process group leader. *)
datatype launcher = Session of string | Group

(* Sets every signal to its default disposition in the fork route's child,
   right before its exec, as native_spawn does: a forked child keeps the
   ignored signals (Poly/ML's SIGPIPE) across exec, while Poly/ML's exec
   already empties the mask.  SIG_DFL is the null pointer.  Signals above
   64 (none on Linux or Darwin), and all signals where signal cannot be
   called, keep their dispositions.  prepare_signal_handling, called in the
   parent before the fork, makes the first call: Poly/ML looks the symbol
   up on first use, and the child must not run the dynamic loader. *)
local
  open Foreign
  val set_handler = buildCall2
    (getSymbol (loadExecutable ()) "signal",(cInt,cPointer),cPointer)
    handle Foreign _ => fn _ => Memory.null
  val signals = List.tabulate (64,fn i => i + 1)
in
  (* Signal 0 is invalid, so this call changes no disposition. *)
  fun prepare_signal_handling () =
    ignore (set_handler (0,Memory.null) handle Foreign _ => Memory.null)
  fun default_signal_handling () =
    List.app (fn number => ignore (set_handler (number,Memory.null)
                                   handle Foreign _ => Memory.null))
      signals
end

fun fork_system command =
  let
    val attributes = Thread.getAttributes ()
    fun defer () = Thread.setAttributes
      [Thread.InterruptState Thread.InterruptDefer]
    fun restore () = Thread.setAttributes attributes
    (* Restoring asynchronous interrupts can itself raise.  Never replace an
       exception already being propagated (in particular a timeout). *)
    fun reraise e = ((restore () handle _ => ()); raise e)
    val locked = ref false
    fun unlock () = if !locked then
      (locked := false; Mutex.unlock spawn_lock) else ()
    val descriptors = ref ([] : Posix.IO.file_desc list)
    fun close fd = close_owned descriptors fd
    fun close_all () =
      let val fds = !descriptors
          val _ = descriptors := []
      in List.app (fn fd => Posix.IO.close fd handle _ => ()) fds;
         unlock ()
      end
    val _ = defer ()
    val _ = (Mutex.lock spawn_lock; locked := true)
      handle e => reraise e
    fun pipe () =
      let val p as {infd,outfd} = Posix.IO.pipe ()
      in descriptors := infd :: outfd :: !descriptors;
         Posix.IO.setfd (infd,Posix.IO.FD.cloexec);
         Posix.IO.setfd (outfd,Posix.IO.FD.cloexec);
         p
      end
    val ({infd,outfd},{infd = script,outfd = writer}) =
      ((pipe (),pipe ()) handle e => (close_all (); reraise e))
    (* Like spawn_system: native blocking reap of the killed supervisor,
       not the Basis 10ms WNOHANG polling loop. *)
    fun wait pid = retry (fn () => native_reap pid)
    (* Use a shell, not another ML fork, to supervise the command: a second
       fork in a forked, formerly multithreaded Poly/ML process can deadlock.
       After reporting status the shell stays alive, blocked reading more
       script until cleanup closes writer, pinning the group ID.  Reaping an
       exited leader BEFORE killpg would risk signalling an unrelated, newly
       reused group.  If HOL dies, the kernel closes writer and the shell
       exits: a shell that stopped itself instead could stay stopped forever
       in the orphaned group.

       Pass the script through a pipe: Systeml.exec's macOS fallback uses
       systeml, whose quoting does not protect every shell metacharacter.
       Only a safe /dev/fd path goes through exec.  The original command still
       runs under sh -c, with its original stdin, not as a sourced script.
       /dev/fd is required (available on Linux, macOS and the BSDs). *)
    val wrapper =
      (Byte.stringToBytes
        ("/bin/sh -c " ^ quote command ^ " sh\n" ^
         "case $? in 0) printf 0;; *) printf 1;; esac > " ^
         fdpath outfd ^ "\n")
       handle e => (close_all (); reraise e))
    val _ = prepare_signal_handling ()
    val child = Posix.Process.fork ()
      handle e => (close_all (); reraise e)
  in
    case child of
      NONE =>
        ((Posix.ProcEnv.setpgid {pid = NONE,pgid = NONE};
          (* Already deferred across fork. Do not query thread attributes in
             this forked live heap: another vanished thread may own the
             runtime lock used by getAttributes. Exec/exit retires the child
             registry; only the parent needs cancellation-safe ownership. *)
          Posix.IO.close infd; Posix.IO.close writer;
          (* Clear CLOEXEC only in this child.  Concurrent calls' pipes must
             not stay open in this call's supervisor or command. *)
          Posix.IO.setfd (outfd,Posix.IO.FD.flags []);
          Posix.IO.setfd (script,Posix.IO.FD.flags []);
          default_signal_handling ();
          Systeml.exec ("/bin/sh",["sh",fdpath script]))
         handle _ => Posix.Process.exit 0w127)
    | SOME pid =>
        let
          val _ = unlock ()
          val owned = ref true
          (* Run every cleanup step even if an earlier one fails, remembering
             its first exception.  This runs with interrupts deferred.  The
             direct PID is also killed if group acquisition failed. *)
          fun cleanup () =
            let
              val first = ref (NONE : exn option)
              fun attempt f = f () handle e =>
                (case !first of NONE => first := SOME e | SOME _ => ())
              val _ = if !owned then
                (attempt (fn () => signal (Posix.Process.K_GROUP pid));
                 attempt (fn () => signal (Posix.Process.K_PROC pid));
                 attempt (fn () => (ignore (wait pid); owned := false)))
                else ()
              val _ = close_all ()
            in case !first of NONE => () | SOME e => raise e end
          fun abort e =
            (defer (); (cleanup () handle _ => ()); reraise e)
        in
          (let
             (* Either side can win this race; both establish the SAME group.
                The child cannot exec a command before joining it. *)
             val _ = Posix.ProcEnv.setpgid
               {pid = SOME pid,pgid = SOME pid}
               handle e as OS.SysErr (_,SOME code) =>
                 (* EACCES means the child already exec'd: its setpgid
                    necessarily succeeded first. *)
                 if code = Posix.Error.acces then () else raise e
             val _ = close outfd
             val _ = close script
             val _ = restore ()
             (* Both the script write and result wait must be interruptible. *)
             val _ = write_all writer wrapper
             val message = retry (fn () => Posix.IO.readVec (infd,1))
             val status = if Byte.bytesToString message = "0"
                          then OS.Process.success else OS.Process.failure
             val _ = defer ()
             val _ = cleanup ()
             val _ = restore ()
           in status end
           handle e => abort e)
        end
  end

fun spawn_system launcher command =
  let
    val attributes = Thread.getAttributes ()
    fun defer () = Thread.setAttributes
      [Thread.InterruptState Thread.InterruptDefer]
    fun restore () = Thread.setAttributes attributes
    fun reraise e = ((restore () handle _ => ()); raise e)
    val descriptors = ref ([] : Posix.IO.file_desc list)
    val locked = ref false
    fun unlock () = if !locked then
      (locked := false; Mutex.unlock spawn_lock) else ()
    fun close fd = close_owned descriptors fd
    fun close_all () =
      let val fds = !descriptors
          val _ = descriptors := []
      in List.app (fn fd => Posix.IO.close fd handle _ => ()) fds end
    fun pipe () =
      let val {infd,outfd} = Posix.IO.pipe ()
          (* Register both before either setfd can fail. *)
          val _ = descriptors := infd :: outfd :: !descriptors
          val _ = Posix.IO.setfd (infd,Posix.IO.FD.cloexec)
          val _ = Posix.IO.setfd (outfd,Posix.IO.FD.cloexec)
      in {infd=infd,outfd=outfd} end
    val process = ref NONE
    val group = ref NONE
    (* The session/group leader remains alive after completion, blocked
       reading gate until cleanup closes start, so its group number cannot
       be recycled before killpg.  If HOL dies, the kernel closes start and
       the leader exits once the command it runs finishes.  setsid -w
       retains ownership even on implementations that fork a session leader;
       a Group launch makes the direct process itself the leader. *)
    fun cleanup () =
      let
        val first = ref (NONE : exn option)
        fun attempt f = f () handle e =>
          (case !first of NONE => first := SOME e | SOME _ => ())
        val _ = case !group of NONE => () | SOME pid =>
          attempt (fn () => signal (Posix.Process.K_GROUP pid))
        (* If group PID acquisition was interrupted, the gate is still shut.
           Closing its sole writer makes an orphaned supervisor exit without
           ever launching the command.  No other spawn inherits this writer. *)
        val _ = close_all ()
        val _ = case !process of NONE => () | SOME pid =>
          (attempt (fn () => signal (Posix.Process.K_PROC pid));
           attempt (fn () =>
             (retry (fn () => native_reap pid);
              process := NONE; group := NONE)))
        val _ = unlock ()
      in case !first of NONE => () | SOME e => raise e end
    fun abort e =
      (defer (); (cleanup () handle _ => ());
       case e of FastUnavailable => (restore (); raise e) | _ => reraise e)
    val _ = defer ()
  in
    (let
       val _ = Mutex.lock spawn_lock
       val _ = locked := true
       val {infd=status,outfd=result} = pipe ()
       val {infd=gate,outfd=start} = pipe ()
       (* Native argv needs no Systeml.exec quoting workaround.  Include the
          command directly: no script pipe or intermediate shell.  E2BIG is
          still safe to retry via the fork route, before the gate opens. *)
       val wrapper =
         "printf '%s\\n' \"$$\" > " ^ fdpath result ^ " || exit 1\n" ^
         "IFS= read -r go < " ^ fdpath gate ^ " || exit 1\n" ^
         "[ \"$go\" = go ] || exit 1\n" ^
         "/bin/sh -c " ^ quote command ^ " sh\n" ^
         "case $? in 0) printf 0;; *) printf 1;; esac > " ^
         fdpath result ^ "\n" ^
         "IFS= read -r go < " ^ fdpath gate ^ "\n"
       val inherited = [result,gate]
       val _ = List.app (fn fd =>
         Posix.IO.setfd (fd,Posix.IO.FD.flags [])) inherited
       (* Defer through acquisition AND recording the direct PID.  An async
          exception at the return boundary must not lose the process owner. *)
       val pid = case launcher of
           Session setsid =>
             native_spawn false (setsid,["-w","/bin/sh","-c",wrapper])
         | Group => native_spawn true ("/bin/sh",["-c",wrapper])
       val _ = process := SOME pid
       val _ = List.app (fn fd =>
         Posix.IO.setfd (fd,Posix.IO.FD.cloexec)) inherited
       val _ = List.app close inherited
       val _ = unlock ()
       val _ = restore ()
       fun read_bytes n = Byte.bytesToString
         (retry (fn () => Posix.IO.readVec (status,n)))
       (* Read only the bounded PID line.  Until it is recorded and the gate
          is opened, killing the direct process and closing start suffices.
          In particular no command can escape cancellation of this read. *)
       fun read_pid remaining chars =
         if remaining = 0 then raise FastUnavailable
         else
           case String.explode (read_bytes remaining) of
             [] => raise FastUnavailable
           | chunk => scan_pid chunk remaining chars
       and scan_pid [] remaining chars = read_pid remaining chars
         | scan_pid (c :: rest) remaining chars =
             if c = #"\n" then String.implode (rev chars)
             else if Char.isDigit c then
               scan_pid rest (remaining - 1) (c :: chars)
             else raise FastUnavailable
       val pid_text = read_pid 21 []
       val pid = case Int.fromString pid_text of
           SOME n => if n > 0 then
             Posix.Process.wordToPid (SysWord.fromInt n)
             else raise FastUnavailable
         | NONE => raise FastUnavailable
       val _ = defer ()
       val _ = group := SOME pid
       val _ = restore ()
       val _ = write_all start (Byte.stringToBytes "go\n")
       val message = read_bytes 1
       val status = if message = "0" then OS.Process.success
                    else OS.Process.failure
       val _ = defer ()
       val _ = cleanup ()
       val _ = restore ()
     in status end
     handle e => abort e)
  end

fun setsid_path () =
  (* Limit the FFI to known pid_t=int ABIs.  Other Unix targets retain the
     existing implementation rather than making assumptions about C types.
     Without a setsid program (e.g. stock macOS), still spawn natively, as a
     process group leader: forking the live ML heap per call costs far more
     system time than the supervisor itself. *)
  if not (List.exists (fn (key,value) => key = "sysname" andalso
    List.exists (fn name => value = name)
      ["Linux","Darwin","FreeBSD","NetBSD","OpenBSD","DragonFly"])
    (Posix.ProcEnv.uname () handle OS.SysErr _ => [])) then NONE
  else SOME (case List.find (fn path =>
                    OS.FileSys.access (path,[OS.FileSys.A_EXEC])
                    handle OS.SysErr _ => false)
                  ["/usr/bin/setsid","/bin/setsid"] of
               SOME setsid => Session setsid
             | NONE => Group)

fun system command =
  if not Systeml.isUnix then Systeml.system_ps command
  else case setsid_path () of
    NONE => fork_system command
  | SOME launcher => spawn_system launcher command
      handle FastUnavailable => fork_system command

end
