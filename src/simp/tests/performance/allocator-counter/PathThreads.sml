(* OS thread inventory shared by the three path launchers. The count is
 * followed by the sorted comm names of /proc/self/task. A launcher records
 * it before and after its measured region; the protocol demands identical
 * inventories. This observes the threads that exist when it is called. It
 * does not show that no foreign thread ever ran: the runtime counter of
 * foreign-created threads entering PolyArm64GetThreadData (path word 30)
 * and the shim's import list address that.
 *)
structure PathThreads =
struct
fun insert x [] = [x]
  | insert x (y :: ys) = if String.compare (x, y) = GREATER
                         then y :: insert x ys else x :: y :: ys

fun threads () = let
  val dir = OS.FileSys.openDir "/proc/self/task"
  fun names acc = case OS.FileSys.readDir dir of
      NONE => acc
    | SOME tid => let
        val s = TextIO.openIn ("/proc/self/task/" ^ tid ^ "/comm")
        val comm = case TextIO.inputLine s of
                       SOME l => String.translate
                         (fn #"\n" => "" | c => str c) l
                     | NONE => ""
        val _ = TextIO.closeIn s
      in names (comm :: acc) end
  val all = names []
  val _ = OS.FileSys.closeDir dir
in Int.toString (length all) ::
   List.foldl (fn (x, a) => insert x a) [] all end
end
