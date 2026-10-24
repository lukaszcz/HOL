(* Pure interpreted SML, compiled ONLY in the fresh RootInterpreted table.
 * No Foreign calls: native interpreter_host.sml owns every C endpoint.
 * Dynamic count, action and escaping roots are shared by precompiled entry
 * declarations. Preparation and retained-result inspection are never timed.
 *)
structure Task29Interpreter =
struct
fun check label yes = if yes then () else raise Fail label
val count = ref 0
val refsRoot = ref ([] : int ref list)
val wordsRoot = ref (Array.array (0, 0w0 : word))
fun makeRefs n = let
  fun loop left acc =
    if left = 0 then acc else loop (left - 1) (ref left :: acc)
in loop n [] end
fun noop () = ()
fun refsWork () = refsRoot := makeRefs (!count)
fun wordsWork () = wordsRoot := Array.array (!count, 0wx25)
fun gcWork () = PolyML.fullGC ()
val action = ref noop
fun work () = (!action) ()
fun prepare n = count := n
fun prepareRefs n = (prepare n; action := refsWork)
fun prepareWords n = (prepare n; action := wordsWork)
fun emitResult label kind n checksum =
  print ("@@TASK29_INTERPRETER_RESULT_V1\t" ^ label ^ "\t" ^ kind ^
         "\t" ^ Int.toString n ^ "\t" ^ Int.toString checksum ^ "\n")
fun verifyRefs label n = let
  fun consume [] next acc =
        (check "ref list length" (next = n + 1); acc)
    | consume (r :: rs) next acc =
        (check "ref list contents" (!r = next);
         consume rs (next + 1) (acc + !r))
  val checksum = consume (!refsRoot) 1 0
in emitResult label "refs" n checksum end
fun verifyWords label n = let
  val a = !wordsRoot
  val _ = check "word array length" (Array.length a = n)
  fun consume i acc = if i = n then acc else let
    val w = Array.sub (a, i)
    val _ = check "word array contents" (w = 0wx25)
  in consume (i + 1) (acc + Word.toInt w) end
in emitResult label "words" n (consume 0 0) end
end;
