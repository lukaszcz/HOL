#!/usr/bin/env python3
"""Offline matrix admission mutations; no builds or measurements."""
import copy
import hashlib
from pathlib import Path
import unittest
from unittest.mock import patch

import audit_evidence as ae
import test_acceptance


HERE = Path(__file__).resolve().parent


def stamp(text):
    data = text.encode()
    return dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def command_record(command, stdout):
    info = stamp(stdout)
    return dict(command=command, cwd="/archive/repo", exit=0,
                timed_out=False, stdout=stdout, stdout_sha256=info["sha256"],
                stdout_bytes=info["bytes"])


class ArchiveProvenance(unittest.TestCase):
    def setUp(self):
        # Reuse actual ordered observations/telemetry, not a summary stub.
        self.fixture = test_acceptance.ArchivedAcceptanceTests(
            "test_complete_archive_passes_per_metric")
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.manifest = self.fixture.manifest
        self.receipt = self.fixture.first()
        self.shared = "/archive/repo/src/portableML/prelude.sml"
        self.product = "/archive/repo/src/portableML/.hol/objs/prelude.uo"
        for receipt in self.fixture.receipts.values():
            receipt["result"]["paths"][self.shared]["related_products"] = {
                self.product: copy.deepcopy(self.fixture.hash)}
        self.manifest["shared_inputs"] = {
            self.shared: copy.deepcopy(self.receipt["result"]["paths"][
                self.shared])}

    def reject(self):
        with self.assertRaises((ValueError, KeyError)):
            ae.audit(self.manifest, self.receipt)

    def test_complete_archive_reaches_acceptance_automatically(self):
        self.fixture.persist()
        report = self.fixture.analyze()
        self.assertEqual({r["decision"] for r in report["metrics"].values()},
                         {"pass"})

    def test_offline_validation_never_reads_live_roots(self):
        with patch.object(Path, "read_bytes", side_effect=AssertionError), \
                patch.object(Path, "resolve", side_effect=AssertionError):
            ae.audit_manifest(self.manifest)
            ae.audit(self.manifest, self.receipt)

    def test_every_shared_fingerprint_and_product_field_is_required(self):
        original = copy.deepcopy(self.receipt)
        for field in ("physical", "sha256", "bytes", "related_products"):
            with self.subTest(field=field):
                self.receipt = copy.deepcopy(original)
                del self.receipt["result"]["paths"][self.shared][field]
                self.reject()

    def test_changed_shared_source_hash_and_byte_count(self):
        info = self.receipt["result"]["paths"][self.shared]
        for field, value in (("sha256", "0" * 64), ("bytes", 999)):
            old = info[field]
            info[field] = value
            self.reject()
            info[field] = old

    def test_changed_missing_or_added_related_products(self):
        info = self.receipt["result"]["paths"][self.shared]
        original = copy.deepcopy(info["related_products"])
        for products in ({}, {self.product: dict(sha256="0" * 64, bytes=5)},
                         {**original, self.product[:-2] + "ui":
                          self.fixture.hash}):
            with self.subTest(products=products):
                info["related_products"] = products
                self.reject()

    def test_shared_inventory_cannot_be_omitted(self):
        for value in (None, {}):
            self.manifest["shared_inputs"] = value
            self.reject()
        del self.manifest["shared_inputs"]
        self.reject()

    def test_unknown_shared_logical_source(self):
        self.manifest["shared_inputs"] = {self.shared + "x":
            self.manifest["shared_inputs"][self.shared]}
        self.reject()

    def test_changed_inventory_source_and_product_rejected(self):
        info = self.manifest["shared_inputs"][self.shared]
        info["sha256"] = "0" * 64
        self.reject()
        info["sha256"] = self.fixture.hash["sha256"]
        info["related_products"][self.product]["bytes"] += 1
        self.reject()

    def test_conflicting_alias_and_input_fingerprints(self):
        entry = self.manifest["shared_inputs"][self.shared]
        alias = "/archive/repo/sigobj/prelude.sml"
        self.manifest["shared_inputs"][alias] = copy.deepcopy(entry)
        ae.audit_manifest(self.manifest)
        self.manifest["shared_inputs"][alias]["sha256"] = "0" * 64
        self.reject()
        del self.manifest["shared_inputs"][alias]
        self.manifest["inputs"]["src/portableML/prelude.sml"] = dict(
            sha256="0" * 64, bytes=5)
        self.reject()

    def test_shared_fingerprint_must_agree_across_processes(self):
        last = list(self.fixture.receipts.values())[-1]
        last["result"]["paths"][self.shared]["sha256"] = "0" * 64
        self.fixture.persist()
        with self.assertRaisesRegex(ValueError, "shared source/product"):
            self.fixture.analyze()

    def test_path_normalization(self):
        for path in ("relative/file.sml", "/archive/repo/../foreign/file.sml",
                     "/archive/repo/./file.sml", "/archive//repo/file.sml",
                     "//archive/repo/file.sml", "/archive/repo/file.sml/"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                ae.archived_path(path)
        for path in ("../file", "sub/../file", "sub/./file", "/absolute"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                ae.archived_path(path, relative=True)

    def test_shared_and_private_receipt_escapes(self):
        for logical in (self.shared, "/archive/baseline/Traverse.sml"):
            info = self.receipt["result"]["paths"][logical]
            old = info["physical"]
            for physical in ("/archive/repo/../foreign/prelude.sml",
                             "/archive/baseline/../candidate/Traverse.sml",
                             "src/portableML/prelude.sml"):
                info["physical"] = physical
                self.reject()
            info["physical"] = old

    def test_manifest_escapes(self):
        original = copy.deepcopy(self.manifest)
        changes = [(["repo"], "/archive/repo/../foreign"),
            (["selections", "baseline", "private"],
             "/archive/baseline/../candidate"),
            (["selections", "baseline", "sources", 0, "private_path"],
             "/archive/baseline/../candidate/Traverse.sml"),
            (["shared_inputs", self.shared, "physical"],
             "/archive/repo/../foreign/prelude.sml")]
        for keys, value in changes:
            self.manifest = copy.deepcopy(original)
            target = self.manifest
            for key in keys[:-1]:
                target = target[key]
            target[keys[-1]] = value
            with self.subTest(keys=keys):
                self.reject()

    def test_related_product_escape_or_unrelated_module(self):
        for path in ("/archive/repo/../foreign/prelude.uo",
                     "/foreign/prelude.uo",
                     "/archive/repo/src/simp/prelude.uo",
                     "/archive/repo/src/portableML/unrelated.uo"):
            self.manifest["shared_inputs"][self.shared]["related_products"] = {
                path: self.fixture.hash}
            with self.subTest(path=path):
                self.reject()

    def test_private_related_product_binding(self):
        info = self.receipt["result"]["paths"][
            "/archive/baseline/Traverse.sml"]
        product = "/archive/baseline/.hol/objs/Traverse.uo"
        info["related_products"] = {product: self.fixture.hash}
        self.reject()
        self.manifest["selections"]["baseline"]["products"][
            ".hol/objs/Traverse.uo"] = self.fixture.hash
        ae.audit(self.manifest, self.receipt)
        info["related_products"][product] = dict(sha256="0" * 64, bytes=5)
        self.reject()
        info["related_products"] = {}
        self.reject()

    def test_runtime_options_are_exact(self):
        for options in ([], ["--gcthreads=99", "run",
                             "--holstate=/foreign/heap"],
                        self.manifest["runtime_options"] + ["--extra"]):
            self.manifest["runtime_options"] = options
            self.reject()

    def test_required_tools_and_compiler_are_mandatory(self):
        original = copy.deepcopy(self.manifest["tools"])
        for name in original:
            self.manifest["tools"] = copy.deepcopy(original)
            del self.manifest["tools"][name]
            with self.subTest(name=name):
                self.reject()
        self.manifest["tools"] = {"unrelated": {}}
        self.reject()

    def test_fingerprint_shape(self):
        for value in ({}, dict(sha256="not-a-hash", bytes=5),
                      dict(sha256="b" * 64, bytes=True),
                      dict(sha256="b" * 64, bytes=-1),
                      dict(sha256="b" * 64, bytes=5.0)):
            self.manifest["tools"]["bin/hol"] = value
            with self.subTest(value=value):
                self.reject()

    def test_compiler_and_library_command_provenance(self):
        for key in ("poly_version", "dynamic_libraries"):
            original = copy.deepcopy(self.manifest[key])
            for field, value in (("exit", 1), ("timed_out", True),
                                 ("cwd", "/foreign"),
                                 ("command", ["/foreign/tool"]),
                                 ("stdout_sha256", "0" * 64),
                                 ("stdout_bytes", -1)):
                self.manifest[key] = copy.deepcopy(original)
                self.manifest[key][field] = value
                with self.subTest(key=key, field=field):
                    self.reject()
            self.manifest[key] = original
        self.manifest["poly_version"] = command_record(
            ["/tools/poly", "--version"], "unrelated executable\n")
        self.reject()

    def test_library_discovery_cannot_be_empty_or_unresolved(self):
        for output in ("", "libpolyml.so => not found\n",
                       "libpolyml.so => /unsealed/library.so (0x123)\n"):
            self.manifest["dynamic_libraries"] = command_record(
                ["ldd", "/archive/repo/bin/hol"], output)
            self.reject()

    def test_launcher_options_and_bytes_are_bound(self):
        selected = self.manifest["selections"]["baseline"]
        original = selected["launcher"]
        for text in (original.replace("gcthreads=1", "gcthreads=99"),
                     original.replace("bin/hol.state0", "bin/hol.state.min"),
                     original + "echo extra\n"):
            selected["launcher"] = text
            # Even a self-consistent product seal cannot bypass option checks.
            selected["products"]["paired.exe"] = stamp(text)
            self.reject()
        selected["launcher"] = original
        self.reject()


if __name__ == "__main__":
    unittest.main()
