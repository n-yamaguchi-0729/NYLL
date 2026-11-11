"""Regression checks for source-rule scanning and baseline accounting."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_lean_rules import findings, new_findings


class LeanRulesTest(unittest.TestCase):
    def test_comments_literals_attributes_and_explicit_simplification(self):
        source = '''/- simp /- set_option maxHeartbeats 0 -/ sorry -/
-- #check Nat
def text := "sorry mkPrivateName"
@[simp] theorem f : True := by simp only [True.intro]
@[reassoc (attr := simp)] theorem g : True := by exact True.intro
attribute [local simp] f
example : True := by
  simp
    only [True.intro]
'''
        self.assertEqual(findings(source), [])

    def test_prohibited_syntax_and_positions(self):
        source = '''example : True := by simp
set_option maxHeartbeats 0
#check Nat
def x := sorry
run_cmd discard scopedEnvExtensionsRef.get
'''
        self.assertEqual([(f.rule, f.line) for f in findings(source)], [
            ('unbounded-simplification', 1), ('source-option', 2),
            ('diagnostic-command', 3), ('unproved-term', 4),
            ('environment-internals', 5)])

    def test_moving_debt_does_not_hide_an_additional_occurrence(self):
        old = '  simp [foo]\n'
        moved = '-- comment\n\n  simp [foo]\n'
        self.assertEqual(new_findings(moved, old), [])
        self.assertEqual(len(new_findings(moved + old, old)), 1)
        self.assertEqual(new_findings('simp only [foo]\n', old), [])

    def test_diagnostic_suggestions_cannot_enter_formal_source(self):
        source = 'example : True := by simp?\nexample : True := by simpa?\n'
        self.assertEqual([(f.rule, f.line) for f in findings(source)], [
            ('search-tactic', 1), ('search-tactic', 2)])

    def test_deprecated_conditional_aliases_and_canonical_names(self):
        source = '''-- if_pos is mentioned in a comment
def note := "dif_neg"
example := if_pos h
example := if_neg h
example := dif_pos h
example := dif_neg h
example := ite_eq_left h
example := ite_eq_right h
example := dite_eq_left h
example := dite_eq_right h
example := ite_true
example := dite_false
'''
        self.assertEqual([(f.rule, f.line) for f in findings(source)], [
            ('deprecated-conditional-lemma', line) for line in range(3, 7)])


if __name__ == '__main__':
    unittest.main()
