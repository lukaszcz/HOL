#!/usr/bin/env python3
"""TASK_13 fail-closed in-memory mutation controls; no HOL execution."""
import unittest

import audit_task13 as audit


class StructuralControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = audit.read_sources()
        audit.structural(cls.sources)

    def reject(self, path, old, new, diagnostic):
        source = self.sources[path]
        self.assertIn(old, source, "mutation must actually change the input")
        self.assertNotEqual(old, new)
        changed = dict(self.sources)
        changed[path] = source.replace(old, new, 1)
        with self.assertRaisesRegex(ValueError, diagnostic):
            audit.structural(changed)

    def test_current_sources(self):
        seals = audit.structural(self.sources)
        self.assertEqual(set(seals), set(self.sources))
        for path, text in self.sources.items():
            self.assertEqual(seals[path], audit.seal(text))

    def test_entire_legacy_files_are_pinned(self):
        # Not merely the public declarations or a selection of body tokens.
        for path in audit.PINNED:
            with self.subTest(path=path):
                self.reject(path, "\n", "\n(* changed *)\n", "pinned develop")

    def test_legacy_work_mutations(self):
        mutations = (
            ("Opening.sml", "HO_PART_MATCH", "PART_MATCH"),
            ("Opening.sml", "process_subgoals", "changed_subgoals"),
            ("Travrules.sml", "map", "rev o map"),
            ("Traverse.sml", "UNCHANGED", "Fail \"unchanged\""),
            ("congLib.sml", "CONGPROC", "OpeningExt.THREADED_CONGPROC"))
        for name, old, new in mutations:
            with self.subTest(name=name, old=old):
                self.reject(audit.SRC + name, old, new, "pinned develop")

    def test_legacy_extension_dependencies(self):
        for name in audit.ORDINARY:
            with self.subTest(name=name):
                self.reject(audit.SRC + name + ".sml", "\n",
                            "\nopen OpeningExt TravrulesExt;\n",
                            "pinned develop")

    def test_entire_threaded_core_work(self):
        mutations = (
            ("GSPEC (GEN_ALL congrule)", "SPEC_ALL congrule"),
            ("HO_PART_MATCH", "PART_MATCH"),
            ("can (match_term l) r andalso can (match_term r) l", "true"),
            ("map (map reprocess_flag", "map (map (K false)"),
            ("applicable (rand conc) []", "[]"),
            ("val rhs_genvars = filter is_genvar (free_vars (rand conc))",
             "val rhs_genvars = []"),
            ("free_vars (concl match_thm)", "free_vars (rand conc)"),
            ("orelse\n                     op_mem",
             "andalso\n                     op_mem"),
            ("val all_genvars = ref NONE", "val all_genvars = ref (SOME [])"),
            ("strip_imp_until_rel is_result bdy1", "([],bdy1)"),
            ("depther (reprocessed_assum_thms,oper) orig",
             "depther ([],oper) orig"),
            ("list_eq aconv sfx ho_vars", "true"),
            ("itlist DISCH assums abs_rewr_thm", "abs_rewr_thm"),
            ("SPEC gen_abs_res (GEN genv match_thm)", "match_thm"),
            ("if may_leave_redex genv then", "if false then"),
            ("beta_reduce_rebuilt (n - 1) gen_abs_res rebuilt_thm",
             "rebuilt_thm"),
            ("RAND_CONV (DEPTH_CONV reduce)", "DEPTH_CONV reduce"),
            ("allunch andalso not changed", "allunch"),
            ("solver condition", "ASSUME condition"),
            ("raise UNCHANGED", "raise Fail \"unchanged\""))
        for old, new in mutations:
            with self.subTest(old=old):
                self.reject(audit.SRC + "OpeningExt.sml", old, new,
                            "OpeningExt core/prefix")

    def test_unspecialized_mixed_opening_rejected(self):
        original = audit.git_source(audit.START, audit.SRC + "Opening.sml")
        mixed = audit.between(original, "fun strip_n_imp",
                              "\nval CONGPROC = gen_CONGPROC")
        self.reject(audit.SRC + "OpeningExt.sml", audit.threaded_core(),
                    mixed, "OpeningExt core/prefix")

    def test_threaded_false_adapter_rejected(self):
        self.reject(audit.SRC + "OpeningExt.sml",
                    "fun THREADED_CONGPROC refl congrule =",
                    "fun THREADED_CONGPROC refl congrule =\n"
                    "Opening.CONGPROC refl congrule\n"
                    "fun unused refl congrule =", "OpeningExt core/prefix")

    def test_opening_prefix_has_only_shared_imports_type_and_helper(self):
        mutations = (
            ("Trace Opening;", "Trace;"),
            ("type congproc = Opening.congproc", "type congproc = unit"),
            ("fun dest_binop", "val registry = ref [];\nfun dest_binop"),
            ("fun dest_binop", "val tracing = ref 0;\nfun dest_binop"),
            ("fun dest_binop", "exception UNCHANGED;\nfun dest_binop"),
            ("fun dest_binop", "exception HOL_ERR;\nfun dest_binop"),
            ("fun dest_binop", "fun samerel x y = true;\nfun dest_binop"),
            ("fun dest_binop", "val slot = ThreadLocal.new ();\n"
             "fun dest_binop"),
            ("  (f,x,y)", "  (f,y,x)"),
            ("\nend\n", "\nend\nval duplicate_registry = ref []\n"))
        for old, new in mutations:
            with self.subTest(old=old, new=new):
                self.reject(audit.SRC + "OpeningExt.sml", old, new,
                            "OpeningExt core/prefix")

    def test_opening_signature_identity(self):
        self.reject(audit.SRC + "OpeningExt.sig",
                    "type congproc = Opening.congproc", "type congproc",
                    "shared congproc identity")
        self.reject(audit.SRC + "OpeningExt.sig", "val THREADED_CONGPROC",
                    "exception UNCHANGED\n  val THREADED_CONGPROC",
                    "shared congproc identity")

    def test_travrules_aliases_and_shared_lookup(self):
        mutations = (
            ("type preorder = Travrules.preorder", "type preorder = unit"),
            ("type travrules = Travrules.travrules", "type travrules = unit"),
            ("Opening.rel_of_congrule th", "OpeningExt.rel_of_congrule th"),
            ("Travrules.PREORDER", "PREORDER"),
            ("Travrules.find_relation r relns", "hd relns"),
            ("OpeningExt.THREADED_CONGPROC refl th",
             "Opening.CONGPROC refl th"),
            ("Travrules.TRAVRULES", "TRAVRULES"),
            ("map threaded_cong2proc congs",
             "map threaded_cong2proc (rev congs)"),
            ("weakenprocs=[]", "weakenprocs=map threaded_cong2proc congs"),
            ("  fun mk_threaded_travrules", "  val registry = ref []\n"
             "  fun mk_threaded_travrules"),
            ("  fun mk_threaded_travrules", "  exception UNCHANGED\n"
             "  fun mk_threaded_travrules"))
        for old, new in mutations:
            with self.subTest(old=old):
                self.reject(audit.SRC + "TravrulesExt.sml", old, new,
                            "TravrulesExt aliases/lookup/map/threaded routing")

    def test_travrules_signature_identities(self):
        for alias in ("preorder", "travrules"):
            with self.subTest(alias=alias):
                self.reject(audit.SRC + "TravrulesExt.sig",
                            "type " + alias + " = Travrules." + alias,
                            "type " + alias, "shared type identities")

    def test_each_congext_constructor_must_be_explicit_threaded(self):
        for old in ("OpeningExt.THREADED_CONGPROC gen_refl",
                    "OpeningExt.THREADED_CONGPROC "
                    "(fn {Rinst,arg} => REFL arg)"):
            for target in ("CONGPROC", "Opening.CONGPROC",
                           "THREADED_CONGPROC", "Opening.THREADED_CONGPROC"):
                with self.subTest(old=old, target=target):
                    self.reject(audit.SRC + "congExtLib.sml", old,
                                old.replace("OpeningExt.THREADED_CONGPROC",
                                            target), "two explicit threaded")

    def test_congext_work_and_identity_mutations(self):
        mutations = (
            ("flatten (map BODY_CONJUNCTS congs)", "congs"),
            ("find_relation preorderTerm preorders", "hd preorders"),
            ("Travrules.EQ_preorder", "mk_preorder (TRUTH,TRUTH)"),
            ("Travrules.PREORDER", "PREORDER"),
            ("exception CONVNET", "exception COPIED_CONVNET"),
            ("Traverse.REDUCER", "TraverseExt.REDUCER"),
            ("STRUCT_ERR \"congLib\"", "STRUCT_ERR \"congExtLib\""))
        for old, new in mutations:
            with self.subTest(old=old):
                self.reject(audit.SRC + "congExtLib.sml", old, new,
                            "congExtLib must retain work/identities")

    def test_simp_extension_explicit_threaded_route(self):
        for target in ("mk_threaded_travrules",
                       "Travrules.mk_threaded_travrules",
                       "Travrules.mk_travrules"):
            with self.subTest(target=target):
                self.reject(audit.SRC + "simpExtLib.sml",
                            "TravrulesExt.mk_threaded_travrules relations",
                            target + " relations", "explicit threaded call")

    def test_simp_extension_work_and_branch(self):
        mutations = (
            ("if null threaded_congs then reltravs", "if true then reltravs"),
            ("threaded_congs::reltravs", "congs::reltravs"),
            ("travrules::mk_travrules relations congs::",
             "travrules::mk_travrules relations []::"),
            ("Cond_rewrExt.prepare (nm,th) tag",
             "Cond_rewrExt.prepare (nm,th) BoundedRewrites.UNBOUNDED"))
        for old, new in mutations:
            with self.subTest(old=old):
                self.reject(audit.SRC + "simpExtLib.sml", old, new,
                            "simpExtLib work/shared identities")

    def test_ordinary_mixed_compiler_changes_only_m3_route(self):
        for old, new in (
                ("TravrulesExt.mk_threaded_travrules", "mk_travrules"),
                ("threaded_congs::reltravs", "congs::reltravs"),
                ("Cond_rewrExt.COND_REWR_CONVS", "Cond_rewr.COND_REWR_CONV")):
            with self.subTest(old=old):
                self.reject(audit.SRC + "simpLib.sml", old, new,
                            "simpLib temporary M3 route/work")

    def test_native_and_selftests_untouched(self):
        self.assertIn(audit.SRC + "selftest.sml", audit.native_paths())
        self.assertTrue(any("contracts/TraversalContracts.sml" in p
                            for p in audit.native_paths()))
        for path in audit.native_paths():
            with self.subTest(path=path):
                self.reject(path, "\n", "\n(* changed *)\n", "native/selftest")

    def test_missing_sources_fail_closed(self):
        for path in self.sources:
            with self.subTest(path=path):
                changed = dict(self.sources)
                del changed[path]
                with self.assertRaisesRegex(ValueError, "missing audited"):
                    audit.structural(changed)

    def test_ambiguous_or_reversed_anchors_rejected(self):
        for text in ("start start stop", "stop start", "no anchors"):
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    audit.between(text, "start", "stop")
        with self.assertRaisesRegex(ValueError, "missing/ambiguous"):
            audit.replace_once("twice twice", "twice", "once")


if __name__ == "__main__":
    unittest.main()
