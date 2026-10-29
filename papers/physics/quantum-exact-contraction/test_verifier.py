"""Failure controls for the transitive axiom report gate."""
import unittest
from verify import check_axioms

class AxiomReportTests(unittest.TestCase):
    expected = {'Example.first', 'Example.second'}
    valid = "'Example.first' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Example.second' does not depend on any axioms\n"

    def test_complete_report(self):
        check_axioms(self.valid, self.expected)

    def test_missing_or_wrong_names(self):
        for text in ['', self.valid.splitlines()[0], self.valid.replace('Example.second', 'Example.other')]:
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                check_axioms(text, self.expected)

    def test_duplicate_report(self):
        with self.assertRaises(RuntimeError):
            check_axioms(self.valid + self.valid.splitlines()[0], self.expected)

    def test_untrusted_axiom(self):
        for name in ['sorryAx', 'Lean.ofReduceBool', 'customAxiom']:
            with self.subTest(name=name), self.assertRaises(RuntimeError):
                check_axioms(self.valid.replace('Quot.sound', name), self.expected)

    def test_empty_request(self):
        with self.assertRaises(RuntimeError):
            check_axioms('', set())

if __name__ == '__main__':
    unittest.main()
