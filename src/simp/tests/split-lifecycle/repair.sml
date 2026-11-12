(* A small independently mutable regression for explicit dispatcher repair. *)
open HolKernel testutils

fun split_attribute_now () =
  ThmAttribute.attribute_fns_of (Context.snapshot ()) "split"

fun check label ok = (tprint label; if ok then OK () else die label)
val _ = Theory.new_theory "split_listener_repair"
val name = "splitLib.persistence.onload"
fun init () = SplitData.initialize {validate=fn _ => ()}
val _ = init ()
val attribute = valOf (split_attribute_now ())
val _ = ThmAttribute.local_attribute
  {name="local",attrname="split",args=[],thm=boolTheory.TRUTH}
val entry = Context.snapshot ()
val dispatcher = valOf (Listener.remove_listener Theory.delta_hook name)
val _ = init ()
val _ = List.app (fn (file,dir) =>
  print ("OBS repair.loaded.path=" ^ OS.Path.concat (dir,file) ^ "\n"))
  (Binarymap.listItems (Meta.fileDirMap ()))
val _ = check "explicit initialization repairs missing dispatcher identity"
  (case List.find (fn (n,_) => n = name)
     (Listener.listeners Theory.delta_hook) of
       SOME (_,f) => Portable.pointer_eq (f,dispatcher)
     | NONE => false)
val _ = check "dispatcher repair preserves exact Context and live rules"
  (Portable.pointer_eq (entry,Context.snapshot ()) andalso
   Portable.pointer_eq (attribute,
     valOf (split_attribute_now ())) andalso
   (case SplitData.named_rules () of
        [(key,th)] => key = "split_listener_repair$local" andalso
          Portable.pointer_eq (th,boolTheory.TRUTH)
      | _ => false))
val _ = Listener.remove_listener Theory.delta_hook name
val foreign_calls = ref 0
fun foreign _ = foreign_calls := !foreign_calls + 1
val _ = Theory.register_hook (name,foreign)
val result = Exn.capture init ()
val _ = check "repair never replaces a foreign dispatcher"
  ((case result of Exn.Exn (HOL_ERR e) =>
      Feedback.top_structure_of e = "SplitData" andalso
      Feedback.top_function_of e = "initialize"
    | _ => false) andalso
   Portable.pointer_eq (entry,Context.snapshot ()) andalso
   (case List.find (fn (n,_) => n = name)
      (Listener.listeners Theory.delta_hook) of
        SOME (_,f) => Portable.pointer_eq (f,foreign)
      | _ => false) andalso !foreign_calls = 0)
(* Ownership checks (initialize preflight, persistent removal) only read the
   handler record: a replacement "split" handler is never called. The foreign
   dispatcher above is removed first, so only the attribute conflict is in
   play. *)
val replacement_calls = ref 0
fun replacement_attr _ = replacement_calls := !replacement_calls + 1
val _ = Listener.remove_listener Theory.delta_hook name
val _ = Context.restore entry
val _ = ThmAttribute.register_attribute
  ("split",{localf=replacement_attr,storedf=replacement_attr})
val replaced = Context.snapshot ()
val replaced_result = Exn.capture init ()
(* repair.sml must import nothing from src/simp/src except SplitData, so the
   TASK23 source-isolated negative stays isolated; hence SplitData.exclude,
   not splitLib.exclude_split. *)
val replaced_exclusion =
  Exn.capture SplitData.exclude "split_listener_repair$local"
fun conflict_of f msg (Exn.Exn (HOL_ERR e)) =
      Feedback.top_structure_of e = "splitLib" andalso
      Feedback.top_function_of e = f andalso
      Feedback.message_of e = msg
  | conflict_of _ _ _ = false
val _ = check "ownership checks never call a replacement handler"
  (conflict_of "enable_split_attribute"
      "settype or attribute split already exists" replaced_result andalso
   conflict_of "exclude_split"
      "persistent split registration not owned" replaced_exclusion andalso
   null (SplitData.named_rules ()) andalso
   Portable.pointer_eq (replaced,Context.snapshot ()) andalso
   !replacement_calls = 0)
val _ = print "OBS repair=pass\n"
val _ = OS.Process.exit OS.Process.success
