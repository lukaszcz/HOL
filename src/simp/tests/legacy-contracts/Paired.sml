(* Native reporter for the unchanged differential assertion inputs. *)
structure Paired =
struct
  val checks = ref 0
  fun check name passed =
    (testutils.tprint name;
     if passed then (testutils.OK (); checks := !checks + 1)
     else testutils.die name)
end
