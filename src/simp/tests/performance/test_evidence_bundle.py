import gzip
import json
from pathlib import Path
import tempfile
import unittest

import evidence_bundle as bundle


class BundleTests(unittest.TestCase):
    def test_roundtrip_original_bytes_including_gzip_headers(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source"
            source.mkdir()
            values = {"manifest.json": b'{"x":1}\n',
                      "receipt.json.gz": gzip.compress(b'{"x":2}\n', mtime=0),
                      "header.gz": gzip.compress(b"header", mtime=123),
                      "binary": bytes(range(256))}
            for name, data in values.items():
                (source / name).write_bytes(data)
            archive = root / "bundle.gz"
            self.assertEqual(bundle.pack(source, archive), 4)
            target = root / "target"
            self.assertEqual(bundle.unpack(archive, target), 4)
            for name, data in values.items():
                self.assertEqual((target / name).read_bytes(), data)
            with self.assertRaises(FileExistsError):
                bundle.unpack(archive, target)
            with self.assertRaises(FileExistsError):
                bundle.pack(source, archive)
            xz = root / "bundle.json.xz"
            bundle.pack(source, xz)
            bundle.unpack(xz, root / "xz-target")
            for name, data in values.items():
                self.assertEqual((root / "xz-target" / name).read_bytes(), data)

    def test_corruption_and_path_escape_fail_without_partial_output(self):
        for name in ("ok", "../outside", "/absolute"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                payload = dict(schema="task28-lossless-evidence-v1", files={
                    name: dict(encoding="text", content="data",
                               bytes=4, sha256="0" * 64)})
                archive = root / "bundle.gz"
                archive.write_bytes(gzip.compress(json.dumps(payload).encode()))
                with self.assertRaises(ValueError):
                    bundle.unpack(archive, root / "target")
                self.assertFalse((root / "target").exists())


if __name__ == "__main__":
    unittest.main()
