import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from build_edition import scan_urls


class ScanUrlTests(unittest.TestCase):
    def test_internet_archive_page_urls_are_deterministic(self):
        urls = scan_urls("https://archive.org/details/in.ernet.dli.2015.449496", 14)
        self.assertEqual(
            urls["page"],
            "https://archive.org/details/in.ernet.dli.2015.449496/page/n14/mode/1up",
        )
        self.assertEqual(
            urls["display"],
            "https://archive.org/download/in.ernet.dli.2015.449496/page/n14_w1400.jpg",
        )
        self.assertEqual(urls["zoom"], urls["display"])
        self.assertEqual(urls["file"], "https://archive.org/details/in.ernet.dli.2015.449496")

    def test_internet_archive_route_rejects_host_and_identifier_mutations(self):
        for source in (
            "https://www.archive.org/details/in.ernet.dli.2015.449496",
            "https://archive.org.evil.example/details/in.ernet.dli.2015.449496",
            "https://archive.org/details/in.ernet.dli.2015.449496/extra",
            "https://archive.org/details/in.ernet.dli.2015.449496?output=1",
            "https://archive.org/details/../in.ernet.dli.2015.449496",
            "https://archive.org/details/in.ernet.dli.2015.449496%2Fescape",
        ):
            with self.subTest(source=source):
                with self.assertRaisesRegex(ValueError, "unsupported canonical scan URL"):
                    scan_urls(source, 14)

    def test_internet_archive_route_rejects_nonpositive_or_nonintegral_leaf(self):
        for leaf in (0, -1, "not-a-leaf"):
            with self.subTest(leaf=leaf):
                with self.assertRaises((ValueError, TypeError)):
                    scan_urls("https://archive.org/details/in.ernet.dli.2015.449496", leaf)


if __name__ == "__main__":
    unittest.main()
