"""Checks for mathematical guide provenance, review gates, and static navigation.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
"""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
from xml.etree import ElementTree as ET

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import build_guides as guides


def fixture():
    return {
        "slug": "pro-c-groups", "repository": "ProCGroups", "title": "Pro-C Groups",
        "summary": "An example.", "overview": ["Finite quotients."], "scopeNote": "Selected results.",
        "references": [{"id": "example", "type": "book", "author": "A. Author", "title": "Groups",
                        "year": "2026", "url": "https://example.org/groups"}],
        "entries": [{"slug": "example", "title": "A result", "kind": "theorem", "summary": "Reflexivity.",
                     "statement": [r"For $n\in\mathbb N$, $$n=n.$$"], "discussion": ["An example."],
                     "history": ["Context."], "references": ["example"],
                     "lean": [{"path": "Nyll/Example.lean", "name": "Example.result"}]}],
    }


def parsed(source):
    return guides.parse_module(source, "Nyll.Example", "Nyll/Example.lean", "https://example.org/blob/" + "a" * 40)


def published_files():
    return {
        "Nyll/Example.lean": b"import Nyll.Dependency\nnamespace Example\ntheorem result : True := by trivial\nend Example\n",
        "Nyll/Dependency.lean": b"import Nyll.Leaf\nimport Mathlib.Data.Nat.Basic\ndef helper : Nat := 1\n",
        "Nyll/Leaf.lean": b"/- import Nyll.CommentOnly -/\ndef leaf : Nat := 2\n",
        "Nyll/Unrelated.lean": b"def unrelated : Nat := 3\n",
        "lake-manifest.json": b'{"packages":[{"name":"mathlib","rev":"old"}]}\n',
        "lean-toolchain": b"leanprover/lean4:v4.35.0-rc2\n",
    }


def publication(files):
    return {"source_commit": "b" * 40, "canonical_repository": "n-yamaguchi-0729/NYLL",
            "repository": "n-yamaguchi-0729/ProCGroups",
            "source_hashes": {name: hashlib.sha256(blob).hexdigest() for name, blob in files.items()}}


class GuideTests(unittest.TestCase):
    def test_declaration_diagnostic_distinguishes_context_from_proof_changes(self):
        # The separate dependency lock deliberately guards the whole file too.
        first = parsed("namespace Example\nvariable (n : Nat)\ntheorem result : n = n := by rfl\nend Example\n")
        proof = parsed("namespace Example\nvariable (n : Nat)\ntheorem result : n = n := by\n  simp\nend Example\n")
        hypothesis = parsed("namespace Example\nvariable (n : Int)\ntheorem result : n = n := by rfl\nend Example\n")
        fp = lambda m: guides.declaration_fingerprint(m["declarations"][0], m["imports"])
        self.assertEqual(fp(first), fp(proof))
        self.assertNotEqual(fp(first), fp(hypothesis))
        self.assertNotEqual(fp(first), guides.declaration_fingerprint(first["declarations"][0], ["Mathlib"]))

    def test_definition_body_changes_require_review(self):
        first = parsed("def value : Nat := 2\n")["declarations"][0]
        second = parsed("def value : Nat := 3\n")["declarations"][0]
        self.assertNotEqual(guides.declaration_fingerprint(first, []), guides.declaration_fingerprint(second, []))

    def test_math_and_raw_html_are_preserved_as_text(self):
        rendered = guides.inline(r"$x_1 < x_2$ <script>alert(1)</script> **text** `code`")
        self.assertIn("$x_1 &lt; x_2$", rendered)
        self.assertNotIn("<script>", rendered)
        self.assertIn("<strong>text</strong>", rendered)
        with self.assertRaises(guides.SourceError):
            guides.safe_url("javascript:alert(1)")

    def test_source_block_preserves_and_escapes_original_notices(self):
        module = parsed("/- Copyright (c) 2025 A. Author.\nAuthors: A. Author <script>\nApache-2.0. -/\n"
                        "theorem result : True := by trivial\n")
        block = guides.source_block({"declaration": module["declarations"][0], "module": module,
                                     "nyllUrl": "https://example.org/source"})
        self.assertIn("Source credits and license", block)
        self.assertIn("Copyright (c) 2025 A. Author.", block)
        self.assertIn("Authors: A. Author &lt;script&gt;", block)
        self.assertNotIn("<script>", block)

    def test_invalid_targets_and_missing_references_are_rejected(self):
        data = fixture()
        guides.validate_guide(data)
        data["entries"][0]["lean"][0]["path"] = "Nyll/../../secrets.lean"
        with self.assertRaises(guides.SourceError):
            guides.validate_guide(data)
        data = fixture()
        data["entries"][0]["references"] = ["missing"]
        with self.assertRaises(guides.SourceError):
            guides.validate_guide(data)

    def test_extract_checks_published_hash_and_missing_or_unfinished_declaration(self):
        source = "namespace Example\ntheorem result : True := by trivial\nend Example\n"
        def run(text, name="Example.result", correct_hash=True):
            data = fixture()
            data["entries"][0]["lean"][0]["name"] = name
            files = published_files()
            files["Nyll/Example.lean"] = text.encode()
            manifest = publication(files)
            if not correct_hash:
                manifest["source_hashes"]["Nyll/Example.lean"] = "0" * 64
            def read(_path, _sha, names):
                return {path: files[path] for path in names}
            with patch.object(guides, "git", return_value="a" * 40), \
                    patch.object(guides, "source_text", return_value=json.dumps(manifest)), \
                    patch.object(guides, "source_blobs", side_effect=read):
                return guides.extract(data, Path("unused"), False)
        entries, _ = run(source)
        self.assertIn("/blob/" + "b" * 40, entries[0]["selected"][0]["nyllUrl"])
        with self.assertRaises(guides.SourceError):
            run(source, "Missing")
        with self.assertRaises(guides.SourceError):
            run(source.replace("trivial", "sorry"))
        with self.assertRaises(guides.SourceError):
            run(source, correct_hash=False)

    def test_header_reads_comments_modifiers_and_multiline_imports_only(self):
        source = """/- license /- nested import Nyll.Fake -/ -/
module
prelude
public /- split -/ meta import
  Nyll.First
meta import all Nyll.Second -- trailing import Nyll.Fake
import Mathlib.Data.Nat.Basic
/-! Documentation mentioning import Nyll.Fake. -/
@[expose] public section
def body := "unterminated string ignored by the header reader
"""
        self.assertEqual(guides.header_imports(source, "test.lean"),
                         ["Nyll.First", "Nyll.Second", "Mathlib.Data.Nat.Basic"])
        self.assertEqual(guides.header_imports("import Nyll.A import Nyll.B\nnamespace X\n", "test.lean"),
                         ["Nyll.A", "Nyll.B"])
        self.assertEqual(guides.header_imports("-- import Nyll.Fake", "test.lean"), [])
        self.assertEqual(guides.header_imports("\ufeffprelude\nimport Init\n", "test.lean"), ["Init"])

    def test_header_rejects_unsupported_or_malformed_imports(self):
        bad_headers = [
            "import", "import\nnamespace X", "import Nyll.A Nyll.B", "import Nyll.A.",
            "import Nyll.Δ", "import Nyll.«A.B»", 'import "Nyll.A"',
            "private import Nyll.A", "public import Nyll.A", "meta import Nyll.A",
            "import all Nyll.A", "module\npublic import all Nyll.A",
            "module\nmeta public import Nyll.A", "import Nyll.A\nprelude",
            "module\nmodule\nimport Nyll.A", "/- unfinished", "new_header_form Nyll.A",
        ]
        for source in bad_headers:
            with self.subTest(source=source), self.assertRaisesRegex(guides.SourceError, "Lean header"):
                guides.header_imports(source, "test.lean")

    def test_git_batch_reads_exact_bytes_and_rejects_missing_or_truncated_blobs(self):
        names, blobs = ["Nyll/A.lean", "lean-toolchain"], ["-- α\r\n".encode(), b"lean\n"]
        response = b"".join(b"a" * 40 + b" blob " + str(len(blob)).encode() + b"\n" + blob + b"\n"
                            for blob in blobs)
        with patch.object(guides.subprocess, "check_output", return_value=response) as read:
            self.assertEqual(guides.source_blobs(Path("repo"), "a" * 40, names), dict(zip(names, blobs)))
            self.assertEqual(read.call_count, 1)
            self.assertEqual(read.call_args.kwargs["input"],
                             b"".join(("a" * 40 + ":" + path + "\n").encode() for path in names))
        for bad in [b"a:Nyll/A.lean missing\n", b"a tree 2\nab\n", b"a blob 5\nab\n", response + b"extra"]:
            with self.subTest(response=bad), patch.object(guides.subprocess, "check_output", return_value=bad), \
                    self.assertRaises(guides.SourceError):
                guides.source_blobs(Path("repo"), "a" * 40, names)

    def test_dependency_closure_excludes_unrelated_files_and_never_parses_bodies(self):
        files = published_files()
        # A cyclic import in this isolated fixture must not cause repeated reads.
        files["Nyll/Leaf.lean"] = b"import Nyll.Dependency\ndef leaf := \"not scanned\n"
        reads = []
        def read(_path, _sha, names):
            reads.extend(names)
            return {path: files[path] for path in names}
        with patch.object(guides, "source_blobs", side_effect=read), \
                patch.object(guides, "parse_module", side_effect=AssertionError("must not parse bodies")):
            sources, hashes = guides.dependency_sources(Path("ProCGroups"), "a" * 40,
                                                       publication(files), {"Nyll/Example.lean"})
        expected = set(files) - {"Nyll/Unrelated.lean"}
        self.assertEqual(set(hashes), expected)
        self.assertEqual(set(reads), expected)
        self.assertEqual(len(reads), len(expected))
        self.assertEqual(set(sources), {"Nyll/Example.lean"})

    def test_dependency_and_configuration_blobs_are_verified_against_publication(self):
        files = published_files()
        for bad_path in ["Nyll/Dependency.lean", "Nyll/Leaf.lean", *guides.DEPENDENCY_CONFIG]:
            for missing in [False, True]:
                manifest = publication(files)
                if missing:
                    del manifest["source_hashes"][bad_path]
                else:
                    manifest["source_hashes"][bad_path] = "0" * 64
                with self.subTest(path=bad_path, missing=missing), \
                        patch.object(guides, "source_blobs", side_effect=lambda _p, _s, names: {p: files[p] for p in names}), \
                        self.assertRaisesRegex(guides.SourceError, "publication source hash|Publication source hash"):
                    guides.dependency_sources(Path("ProCGroups"), "a" * 40, manifest, {"Nyll/Example.lean"})

    def test_build_guard_blocks_changed_dependencies_but_allows_unrelated_updates(self):
        parent = Path(os.environ.get("NYLL_SITE_TEST_OUTPUT", ROOT / "tmp" / "site-tests"))
        parent.mkdir(parents=True, exist_ok=True)
        files = published_files()
        with tempfile.TemporaryDirectory(dir=parent) as temporary:
            root = Path(temporary)
            editorial = root / "site/guides"
            editorial.mkdir(parents=True)
            (editorial / "pro-c-groups.json").write_text(json.dumps(fixture()), encoding="utf-8")
            with patch.dict(guides.REPOSITORIES, {"pro-c-groups": "ProCGroups"}, clear=True), \
                    patch.object(guides, "git", return_value="a" * 40), \
                    patch.object(guides, "source_text", side_effect=lambda *_: json.dumps(publication(files))), \
                    patch.object(guides, "source_blobs", side_effect=lambda _p, _s, names: {p: files[p] for p in names}):
                guides.build(root, root / "output", root / "sources", write_lock=True)
                lock = json.loads((editorial / "review-lock.json").read_text(encoding="utf-8"))
                self.assertEqual(lock["schemaVersion"], 2)
                self.assertNotIn("Nyll/Unrelated.lean", lock["dependencyHashes"]["pro-c-groups"])
                # Even a proof-only change is guarded, as are transitive helpers
                # and the pinned Mathlib/Lean environment.
                changes = {
                    "Nyll/Example.lean": files["Nyll/Example.lean"].replace(b"by trivial", b"by exact True.intro"),
                    "Nyll/Dependency.lean": files["Nyll/Dependency.lean"].replace(b":= 1", b":= 5"),
                    "Nyll/Leaf.lean": files["Nyll/Leaf.lean"].replace(b":= 2", b":= 4"),
                    "lake-manifest.json": files["lake-manifest.json"].replace(b"old", b"new"),
                    "lean-toolchain": b"leanprover/lean4:v4.36.0\n",
                }
                for path, changed in changes.items():
                    original, files[path] = files[path], changed
                    with self.subTest(path=path), self.assertRaisesRegex(guides.SourceError, "review required"):
                        guides.build(root, root / "failed-output", root / "sources")
                    self.assertFalse((root / "failed-output").exists())
                    files[path] = original
                files["Nyll/Unrelated.lean"] = b"def unrelated : Nat := 99\n"
                guides.build(root, root / "output", root / "sources")
                lock["schemaVersion"] = 1
                del lock["dependencyHashes"]
                (editorial / "review-lock.json").write_text(json.dumps(lock), encoding="utf-8")
                with self.assertRaisesRegex(guides.SourceError, "missing or outdated"):
                    guides.build(root, root / "failed-output", root / "sources")
                self.assertFalse((root / "failed-output").exists())

    def test_static_pages_sitemap_and_review_failure_before_writing(self):
        parent = Path(os.environ.get("NYLL_SITE_TEST_OUTPUT", ROOT / "tmp" / "site-tests"))
        parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=parent) as temporary:
            root = Path(temporary)
            editorial = root / "site/guides"
            editorial.mkdir(parents=True)
            data = fixture()
            (editorial / "pro-c-groups.json").write_text(json.dumps(data), encoding="utf-8")
            module = parsed("namespace Example\nvariable (n : Nat)\ntheorem result : n = n := by rfl\nend Example\n")
            selected = {"declaration": module["declarations"][0], "module": module, "nyllUrl": "https://example.org/source"}
            entries = [{**data["entries"][0], "selected": [selected]}]
            snapshot = {"repository": "ProCGroups", "revision": "a" * 40, "nyllRevision": "b" * 40,
                        "fingerprints": {"pro-c-groups/example/Example.result": "reviewed"},
                        "dependencyHashes": {"Nyll/Example.lean": "c" * 64}}
            with patch.dict(guides.REPOSITORIES, {"pro-c-groups": "ProCGroups"}, clear=True), patch.object(guides, "extract", return_value=(entries, snapshot)):
                guides.build(root, root / "output", root / "sources", write_lock=True)
                result = root / "output/libraries/pro-c-groups/example/index.html"
                html = result.read_text(encoding="utf-8")
                self.assertIn('href="../"', html)
                self.assertIn("variable (n : Nat)", html)
                self.assertIn("Full declaration and proof", html)
                self.assertIn('href="https://example.org/groups"', html)
                self.assertNotIn(".bib", html)
                sitemap = ET.parse(root / "output/sitemap.xml")
                self.assertEqual(len(sitemap.getroot()), 3)
                guides.build(root, root / "output", root / "sources")
                snapshot["fingerprints"]["pro-c-groups/example/Example.result"] = "changed"
                with self.assertRaisesRegex(guides.SourceError, "review required"):
                    guides.build(root, root / "failed-output", root / "sources")
                self.assertFalse((root / "failed-output").exists())


if __name__ == "__main__":
    unittest.main()
