#include <iostream>

#include "ast/array_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_smt_pp_compact.h"
#include "util/memory_manager.h"

int main()
{
  memory::initialize(0);
  int result = 0;
  {
    ast_manager manager(PGM_ENABLED);
    manager.register_plugin(symbol("array"), alloc(array_decl_plugin));
    sort* boolean = manager.mk_bool_sort();
    sort_ref fake_proof(
        manager.mk_uninterpreted_sort(symbol("Proof")), manager);
    proof_ref proof(manager.mk_asserted(manager.mk_true()), manager);
    sort* domains[1] = {boolean};
    symbol names[1] = {symbol("x")};
    expr_ref inner(
        manager.mk_lambda(1, domains, names, proof.get()), manager);
    expr_ref outer(
        manager.mk_lambda(1, domains, names, inner.get()), manager);
    array_util arrays(manager);
    sort_ref semantic(arrays.mk_array_sort(boolean, boolean), manager);
    sort_ref fake_closure(
        arrays.mk_array_sort(boolean, fake_proof.get()), manager);

    if (!is_proof_closure_sort(manager, inner->get_sort())
        || !is_proof_closure_sort(manager, outer->get_sort())
        || is_proof_closure_sort(manager, proof->get_sort())
        || is_proof_closure_sort(manager, semantic.get())
        || is_proof_closure_sort(manager, fake_closure.get()))
    {
      std::cerr << "proof-closure sort classification failed\n";
      result = 1;
    }
  }
  memory::finalize();
  return result;
}
