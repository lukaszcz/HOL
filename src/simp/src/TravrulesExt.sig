signature TravrulesExt =
sig
  type preorder = Travrules.preorder
  type travrules = Travrules.travrules
  val mk_threaded_travrules : preorder list -> Thm.thm list -> travrules
end
