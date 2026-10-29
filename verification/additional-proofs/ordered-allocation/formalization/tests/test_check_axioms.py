import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("allocation_axioms", Path(__file__).resolve().parents[1] / "check_axioms.py")
parser = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parser)

class AuditCoverageTests(unittest.TestCase):
    def reports(self):
        return [f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in sorted(parser.EXPECTED)]

    def test_exact_coverage(self):
        self.assertEqual(set(parser.validate("\n".join(self.reports()))), parser.EXPECTED)

    def test_multiline(self):
        output = "\n".join(self.reports()).replace("[propext, Classical.choice, Quot.sound]", "[propext,\n Classical.choice,\n Quot.sound]")
        self.assertEqual(len(parser.validate(output)), 4)

    def test_missing_duplicate_forbidden_unknown_and_truncated_fail(self):
        lines = self.reports()
        variants = ["", "\n".join(lines[:-1]), "\n".join(lines + [lines[0]]),
                    "\n".join(lines).replace("propext", "sorryAx", 1),
                    "\n".join(lines).replace(sorted(parser.EXPECTED)[0], "Other.endpoint", 1),
                    "\n".join(lines).replace("[propext, Classical.choice, Quot.sound]", "[propext,", 1)]
        for output in variants:
            with self.subTest(output=output), self.assertRaises(ValueError):
                parser.validate(output)

if __name__ == "__main__":
    unittest.main()
