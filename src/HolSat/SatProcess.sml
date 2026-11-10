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
    fun retry f = f () handle e as OS.SysErr (_,SOME code) =>
      if code = Posix.Error.intr then retry f else raise e
    fun wait pid = retry (fn () =>
      #2 (Posix.Process.waitpid (Posix.Process.W_CHILD pid,[])))
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
    (* Use a shell, not another ML fork, to supervise the command: a second
       fork in a forked, formerly multithreaded Poly/ML process can deadlock.
       After reporting status the shell stays alive (stopped), pinning the
       group ID until cleanup.  Reaping an exited leader BEFORE killpg would
       risk signalling an unrelated, newly reused group.

       Pass the script through a pipe: Systeml.exec's macOS fallback uses
       systeml, whose quoting does not protect every shell metacharacter.
       Only a safe /dev/fd path goes through exec.  The original command still
       runs under sh -c, with its original stdin, not as a sourced script.
       /dev/fd is required (available on Linux, macOS and the BSDs). *)
    val wrapper =
      (Byte.stringToBytes
        ("/bin/sh -c " ^ quote command ^ " sh\n" ^
         "case $? in 0) printf 0;; *) printf 1;; esac > " ^
         fdpath outfd ^ "\n" ^
         "while :; do kill -STOP $$; done\n")
       handle e => (close_all (); reraise e))
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
          Systeml.exec ("/bin/sh",["sh",fdpath script]))
         handle _ => Posix.Process.exit 0w127)
    | SOME pid =>
        let
          val _ = unlock ()
          val owned = ref true
          fun signal target = retry (fn () =>
            Posix.Process.kill (target,Posix.Signal.kill))
            handle e as OS.SysErr (_,SOME code) =>
              if code = Posix.Error.srch then () else raise e
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
             val _ = close writer
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
   the unchanged fork route. *)
local
  open Foreign
  val spawn = buildCall6
    (getSymbol (loadExecutable ()) "posix_spawn",
     (cStar cInt,cString,cPointer,cPointer,
      cVectorPointer (cOptionPtr cString),
      cVectorPointer (cOptionPtr cString)),cInt)
    handle Foreign _ => fn _ => raise FastUnavailable
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

  fun native_spawn (path,args) =
    let
      val pid = ref 0
      val error = spawn (pid,path,Memory.null,Memory.null,
        strings (OS.Path.file path :: args),
        strings (Posix.ProcEnv.environ ()))
    in
      if error = 0 then Posix.Process.wordToPid (SysWord.fromInt (!pid))
      else raise FastUnavailable
    end handle Foreign _ => raise FastUnavailable
end

fun spawn_system setsid command =
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
    fun retry f = f () handle e as OS.SysErr (_,SOME code) =>
      if code = Posix.Error.intr then retry f else raise e
    fun write_all fd text =
      let
        fun loop slice = if Word8VectorSlice.length slice = 0 then ()
          else let val n = retry (fn () => Posix.IO.writeVec (fd,slice))
               in if n = 0 then raise Fail "SatProcess: short write"
                  else loop (Word8VectorSlice.subslice (slice,n,NONE)) end
      in loop (Word8VectorSlice.full (Byte.stringToBytes text)) end
    fun fdpath fd = "/dev/fd/" ^
      Int.toString (SysWord.toInt (Posix.FileSys.fdToWord fd))
    fun quote s = "'" ^ String.translate
      (fn #"'" => "'\\''" | c => str c) s ^ "'"
    val process = ref NONE
    val group = ref NONE
    fun signal target = retry (fn () =>
      Posix.Process.kill (target,Posix.Signal.kill))
      handle e as OS.SysErr (_,SOME code) =>
        if code = Posix.Error.srch then () else raise e
    (* The session leader remains alive (STOPped after completion), so its
       group number cannot be recycled before killpg.  setsid -w retains
       ownership even on implementations that fork a session leader. *)
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
         "while :; do kill -STOP $$; done\n"
       val inherited = [result,gate]
       val _ = List.app (fn fd =>
         Posix.IO.setfd (fd,Posix.IO.FD.flags [])) inherited
       (* Defer through acquisition AND recording the direct PID.  An async
          exception at the return boundary must not lose the process owner. *)
       val pid = native_spawn (setsid,["-w","/bin/sh","-c",wrapper])
       val _ = process := SOME pid
       val _ = List.app (fn fd =>
         Posix.IO.setfd (fd,Posix.IO.FD.cloexec)) inherited
       val _ = List.app close inherited
       val _ = unlock ()
       val _ = restore ()
       fun read_byte () = Byte.bytesToString
         (retry (fn () => Posix.IO.readVec (status,1)))
       (* Read only the bounded PID line.  Until it is recorded and the gate
          is opened, killing the direct process and closing start suffices.
          In particular no command can escape cancellation of this read. *)
       fun read_pid (chars,n) =
         if n > 20 then raise FastUnavailable
         else case read_byte () of
           "\n" => String.implode (rev chars)
         | "" => raise FastUnavailable
         | s => if Char.isDigit (String.sub (s,0)) then
                  read_pid (String.sub (s,0)::chars,n+1)
                else raise FastUnavailable
       val pid_text = read_pid ([],0)
       val pid = case Int.fromString pid_text of
           SOME n => if n > 0 then
             Posix.Process.wordToPid (SysWord.fromInt n)
             else raise FastUnavailable
         | NONE => raise FastUnavailable
       val _ = defer ()
       val _ = group := SOME pid
       val _ = restore ()
       val _ = write_all start "go\n"
       val _ = close start
       val message = read_byte ()
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
     existing implementation rather than making assumptions about C types. *)
  if not (List.exists (fn (key,value) => key = "sysname" andalso
    List.exists (fn name => value = name)
      ["Linux","Darwin","FreeBSD","NetBSD","OpenBSD","DragonFly"])
    (Posix.ProcEnv.uname () handle OS.SysErr _ => [])) then NONE
  else List.find (fn path => OS.FileSys.access (path,[OS.FileSys.A_EXEC])
                             handle OS.SysErr _ => false)
                 ["/usr/bin/setsid","/bin/setsid"]

fun system command =
  if not Systeml.isUnix then Systeml.system_ps command
  else case setsid_path () of
    NONE => fork_system command
  | SOME setsid => spawn_system setsid command
      handle FastUnavailable => fork_system command

end
