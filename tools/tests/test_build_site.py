"""Regression checks for the source browser's indexing boundaries and provenance."""

import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
import uuid


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("build_site", ROOT / "tools" / "build_site.py")
site = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = site
SPEC.loader.exec_module(site)


class SourceIndexTests(unittest.TestCase):
    def parse(self, source):
        return site.parse_module(source, "Nyll.Example.Basic", "Nyll/Example/Basic.lean",
                                 "https://github.com/example/NYLL/blob/" + "a" * 40)

    def test_nested_comments_strings_and_quoted_syntax_do_not_create_entries(self):
        source = '''/-!
# Example

An explanation with `theorem fake`.
-/
/- theorem hidden : False := by sorry
  /- nested -/
-/
namespace Example
/-- This result is documented. -/
theorem real : True := by
  trivial
def text : String := "theorem string_fake : False := by sorry"
def raw : String := r###"theorem raw_fake : False := by sorry"###
def syntaxExample := `(command|
theorem quoted_fake : True := by trivial)
end Example
'''
        module = self.parse(source)
        self.assertEqual([d["name"] for d in module["declarations"]],
                         ["Example.real", "Example.text", "Example.raw", "Example.syntaxExample"])
        self.assertFalse(any(d["hasSorry"] for d in module["declarations"]))
        self.assertEqual(module["declarations"][0]["doc"], "This result is documented.")
        self.assertEqual(module["source"], source)

    def test_namespace_sections_escaped_names_attributes_and_root_names(self):
        source = '''namespace Outer
section Work
namespace Inner
/-- A declaration spanning lines. -/
@[simp,
  nolint unusedArguments]
private theorem «a b» (x : Nat := 4) : x = x := by
  rfl
end Inner
  theorem other : True := by trivial
end Work
def _root_.outside : Nat := 1
end Outer
'''
        declarations = self.parse(source)["declarations"]
        self.assertEqual([d["name"] for d in declarations],
                         ["Outer.Inner.«a b»", "Outer.other", "outside"])
        self.assertEqual(declarations[0]["statement"], 'theorem «a b» (x : Nat := 4) : x = x')
        self.assertIn("@[simp,", declarations[0]["source"])
        self.assertNotIn("end Inner", declarations[0]["source"])
        self.assertEqual(declarations[0]["line"], 7)
        self.assertTrue(declarations[0]["sourceUrl"].endswith("Nyll/Example/Basic.lean#L7"))

    def test_source_body_and_only_explicit_sorry_are_reported(self):
        source = '''/-- The word sorry in documentation is harmless. -/
theorem finished : True := by
  -- sorry
  trivial
/-- Work remains here. -/
theorem unfinished : False := by
  sorry
instance : Inhabited Nat := ⟨0⟩
structure Data where
  /-- A field with a default. -/
  value : Nat := 0
'''
        entries = self.parse(source)["declarations"]
        self.assertEqual([d["hasSorry"] for d in entries], [False, True, False, False])
        self.assertNotIn("Work remains", entries[0]["source"])
        self.assertNotIn("trivial", entries[0]["statement"])
        self.assertIn("trivial", entries[0]["source"])
        self.assertEqual(entries[2]["name"], "(anonymous instance)")
        self.assertIn("value : Nat := 0", entries[3]["statement"])

    def test_multiline_imports_and_unicode_names(self):
        module = self.parse('''public import Nyll.Example.Basic
import Mathlib.Data.Nat.Basic
namespace α₁
def β' : Nat := 1
end α₁
''')
        self.assertEqual(module["imports"], ["Nyll.Example.Basic", "Mathlib.Data.Nat.Basic"])
        self.assertEqual(module["declarations"][0]["name"], "α₁.β'")

    def test_section_assumptions_mutual_and_local_instances_remain_source_context(self):
        source = '''universe u
namespace A
section Arguments
variable {R : Type u} [Monoid R]
local instance (priority := low) exampleInst : Inhabited R := ⟨1⟩
theorem result (x : R) : x * 1 = x := by exact mul_one x
mutual
def odd : Nat → Bool
  | 0 => false
  | n + 1 => even n
def even : Nat → Bool
  | 0 => true
  | n + 1 => odd n
end
end Arguments
theorem outside : True := by trivial
end A
'''
        entries = self.parse(source)["declarations"]
        self.assertEqual([entry["name"] for entry in entries],
                         ["A.exampleInst", "A.result", "A.odd", "A.even", "A.outside"])
        context = "\n".join(item["source"] for item in entries[1]["context"])
        self.assertIn("variable {R : Type u} [Monoid R]", context)
        self.assertIn("local instance", context)
        outside_context = "\n".join(item["source"] for item in entries[-1]["context"])
        self.assertIn("namespace A", outside_context)
        self.assertNotIn("variable", outside_context)
        self.assertNotIn("local instance", outside_context)

    def test_malformed_input_fails_instead_of_publishing_partial_index(self):
        for source in ['/- unclosed', 'def x := "unclosed', 'def x := (3']:
            with self.subTest(source=source), self.assertRaises(site.SourceError):
                self.parse(source)

    def test_scoped_named_instance_and_anonymous_binder(self):
        module = self.parse('''namespace A
scoped instance (priority := low) inst : Inhabited Nat := ⟨0⟩
local instance (x : Nat) : Inhabited Nat := ⟨x⟩
end A
''')
        self.assertEqual([d["name"] for d in module["declarations"]],
                         ["A.inst", "(anonymous instance)"])

    def test_let_bound_result_types_never_hide_the_conclusion(self):
        for result_type in [
            "let n := 1; n = 1",
            "let n := 1; let m := n; m = n",
            "letI : Inhabited Nat := ⟨0⟩; (default : Nat) = 0",
            "have h : True := by trivial; True",
            "if True then (let n := 1; n = n) else False",
            "match 0 with | 0 => True | _ => False",
        ]:
            with self.subTest(result_type=result_type):
                declaration = "theorem result : " + result_type + " := by sorry"
                entry = self.parse(declaration)["declarations"][0]
                self.assertEqual(entry["statement"], declaration)
                self.assertTrue(entry["statementIncludesBody"])
        simple = self.parse("theorem simple : True := by\n  let n := 1\n  trivial\n")["declarations"][0]
        self.assertEqual(simple["statement"], "theorem simple : True")
        self.assertFalse(simple["statementIncludesBody"])

    def test_compound_scope_names_follow_lean_scope_components(self):
        source = '''namespace Outer
namespace A
namespace B
theorem inside : True := by trivial
end A.B
theorem outside : True := by trivial
namespace X.Y
theorem xy : True := by trivial
end Y
theorem x : True := by trivial
end X
section S.T
variable (n : Nat)
theorem inSection : n = n := by rfl
end T
theorem afterSection : True := by trivial
end S
namespace «name.with.dot»
theorem dotted : True := by trivial
end «name.with.dot»
end Outer
'''
        entries = self.parse(source)["declarations"]
        self.assertEqual([d["name"] for d in entries],
                         ["Outer.A.B.inside", "Outer.outside", "Outer.X.Y.xy", "Outer.X.x",
                          "Outer.inSection", "Outer.afterSection", "Outer.«name.with.dot».dotted"])
        self.assertNotIn("variable", "\n".join(c["source"] for c in entries[5]["context"]))

    def test_weak_namespace_and_open_in_are_scoped_to_their_command(self):
        source = '''namespace Original
section
theorem first : True := by trivial
end
with_weak_namespace _root_.Alternative
open Nat in
with_weak_namespace Nested
theorem wrapped : True := by trivial
theorem normal : True := by trivial
with_weak_namespace _root_.Other
open scoped Nat
theorem afterOpen : True := by trivial
end Original
'''
        entries = self.parse(source)["declarations"]
        self.assertEqual([d["name"] for d in entries],
                         ["Original.first", "Alternative.Nested.wrapped", "Original.normal", "Original.afterOpen"])
        wrapped_context = "\n".join(c["source"] for c in entries[1]["context"])
        self.assertIn("open Nat in", wrapped_context)
        normal_context = "\n".join(c["source"] for c in entries[2]["context"])
        self.assertNotIn("open Nat in", normal_context)

    def test_inline_command_wrappers_and_following_command_boundaries(self):
        source = '''namespace A
variable (n : Nat)
omit n in lemma first : True := by trivial
omit n in open Nat in theorem second : True := by trivial
alias aliasSecond := second
local notation3 "fortyTwo" => (42 : Nat)
scoped[A] notation "fortyThree" => (43 : Nat)
theorem third : True := by trivial
/-- info: True.intro : True -/
#guard_msgs in
#check True.intro
end A
'''
        entries = self.parse(source)["declarations"]
        self.assertEqual([d["name"] for d in entries], ["A.first", "A.second", "A.third"])
        self.assertNotIn("alias", entries[1]["source"])
        self.assertNotIn("info:", entries[2]["source"])
        self.assertIn("omit n in", "\n".join(c["source"] for c in entries[0]["context"]))
        self.assertIn("open Nat in", "\n".join(c["source"] for c in entries[1]["context"]))

    def test_deriving_clause_is_part_of_an_inductive_source(self):
        source = '''inductive Choice where
  | first
  | second
deriving DecidableEq, Repr
deriving instance Inhabited for Choice
def value : Choice := .first
'''
        entries = self.parse(source)["declarations"]
        self.assertIn("deriving DecidableEq, Repr", entries[0]["source"])
        self.assertNotIn("deriving instance", entries[0]["source"])


class BuildTests(unittest.TestCase):
    def setUp(self):
        # Scratch is local to the checkout's generated/ignored output directory.
        self.scratch = ROOT / "_site" / ("test-" + uuid.uuid4().hex)
        self.project = self.scratch / "project"
        (self.project / "Nyll" / "Example").mkdir(parents=True)
        (self.project / "site").mkdir()
        (self.project / "site" / "index.html").write_text("<h1>NYLL</h1>")
        (self.project / "Nyll.lean").write_text("import Nyll.Example.All\n")
        (self.project / "Nyll" / "Example" / "All.lean").write_text(
            "import Nyll.Example.Basic\n/-! # Examples\n\nA library description. -/\n")
        (self.project / "Nyll" / "Example" / "Basic.lean").write_text(
            "/-- A tiny result. -/\nnamespace Sample\ntheorem yes : True := by trivial\nend Sample\n")
        subprocess.run(["git", "init", "-q", str(self.project)], check=True)
        subprocess.run(["git", "-C", str(self.project), "add", "Nyll", "Nyll.lean", "site"], check=True)
        subprocess.run(["git", "-C", str(self.project), "-c", "user.name=NYLL tests", "-c",
                        "user.email=tests@example.invalid", "commit", "-qm", "Fixture"], check=True)

    def tearDown(self):
        resolved = self.scratch.resolve()
        self.assertTrue(resolved.is_relative_to((ROOT / "_site").resolve()))
        shutil.rmtree(resolved)

    def test_build_all_sources_graph_and_commit_links(self):
        output = self.scratch / "output"
        manifest = site.build(self.project, output, "https://github.com/example/NYLL")
        self.assertEqual(manifest["counts"], {"libraries": 1, "modules": 3, "declarations": 1})
        self.assertEqual(manifest["libraries"][0]["doc"], "A library description.")
        module_path = next(m["dataUrl"] for m in manifest["modules"] if m["name"] == "Nyll.Example.Basic")
        module = json.loads((output / module_path).read_text())
        self.assertEqual(module["importedBy"], ["Nyll.Example.All"])
        commit = subprocess.check_output(["git", "-C", str(self.project), "rev-parse", "HEAD"], text=True).strip()
        self.assertIn("/blob/" + commit + "/", module["declarations"][0]["sourceUrl"])
        self.assertIn(commit, module_path)
        self.assertIn(commit, manifest["searchUrl"])
        self.assertTrue((output / manifest["searchUrl"]).is_file())
        self.assertEqual((output / "index.html").read_text(), "<h1>NYLL</h1>")
        self.assertTrue((output / ".nojekyll").exists())

    def test_missing_local_module_blocks_publishing(self):
        (self.project / "Nyll.lean").write_text("import Nyll.DoesNotExist\n")
        with self.assertRaisesRegex(site.SourceError, "missing local module"):
            site.build(self.project, self.scratch / "output", "https://github.com/example/NYLL")

    def test_rebuild_replaces_old_generated_data_but_refuses_unowned_data(self):
        output = self.scratch / "output"
        site.build(self.project, output, "https://github.com/example/NYLL")
        stale = output / "data" / "stale.json"
        stale.write_text("old generated content")
        site.build(self.project, output, "https://github.com/example/NYLL")
        self.assertFalse(stale.exists())
        (output / "data" / "manifest.json").unlink()
        with self.assertRaisesRegex(site.SourceError, "valid NYLL generated manifest"):
            site.build(self.project, output, "https://github.com/example/NYLL")


if __name__ == "__main__":
    unittest.main()
