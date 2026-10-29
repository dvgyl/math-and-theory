"""Failure controls for exact manuscript text and page coverage."""
import subprocess
import unittest
from unittest.mock import patch

import check_manuscripts


class ManuscriptTextTests(unittest.TestCase):
    def test_unknown_manuscript_engine_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "Unsupported manuscript engine"):
            check_manuscripts.manuscript_engine({"manuscript_engine": "unchecked"})

    def compare(self, left, right, left_pages=2, right_pages=2):
        outputs = [
            subprocess.CompletedProcess([], 0, stdout=left),
            subprocess.CompletedProcess([], 0, stdout=f"Pages: {left_pages}\n"),
            subprocess.CompletedProcess([], 0, stdout=right),
            subprocess.CompletedProcess([], 0, stdout=f"Pages: {right_pages}\n"),
        ]
        with patch.object(check_manuscripts.subprocess, "run", side_effect=outputs) as run:
            check_manuscripts.check_pdf_text("rebuilt.pdf", "committed.pdf")
            self.assertEqual(run.call_args_list[0].args[0],
                             ["pdftotext", "-raw", "rebuilt.pdf", "-"])
            self.assertTrue(all(call.kwargs["check"] for call in run.call_args_list))

    def test_exact_text_and_page_breaks_pass(self):
        self.compare(b"Theorem x + y\fProof\f", b"Theorem x + y\fProof\f")

    def test_changed_mathematical_symbol_fails(self):
        with self.assertRaises(ValueError):
            self.compare(b"x + y\fProof\f", b"x - y\fProof\f")

    def test_unicode_is_not_normalized(self):
        with self.assertRaises(ValueError):
            self.compare("fi\fProof\f".encode(), "\ufb01\fProof\f".encode())

    def test_whitespace_is_not_normalized(self):
        with self.assertRaises(ValueError):
            self.compare(b"x y\fProof\f", b"x  y\fProof\f")

    def test_moved_page_break_fails(self):
        with self.assertRaises(ValueError):
            self.compare(b"A\fB\f", b"AB\f\f")

    def test_pdf_page_count_mismatch_fails(self):
        with self.assertRaises(ValueError):
            self.compare(b"A\fB\f", b"A\fB\f", right_pages=3)

    def test_empty_content_fails(self):
        with self.assertRaises(ValueError):
            self.compare(b"\f\f", b"\f\f")

    def test_invalid_page_metadata_fails(self):
        with self.assertRaises(ValueError):
            self.compare(b"A\fB\f", b"A\fB\f", left_pages="unknown")

    def test_extractor_failure_propagates(self):
        failure = subprocess.CalledProcessError(42, ["pdftotext"])
        with patch.object(check_manuscripts.subprocess, "run", side_effect=failure):
            with self.assertRaises(subprocess.CalledProcessError) as caught:
                check_manuscripts.check_pdf_text("rebuilt.pdf", "committed.pdf")
        self.assertEqual(caught.exception.returncode, 42)


if __name__ == "__main__":
    unittest.main()
