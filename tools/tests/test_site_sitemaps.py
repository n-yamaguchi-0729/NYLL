"""Check that independently rebuilt site sections remain discoverable.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
import os
from pathlib import Path
import sys
import tempfile
import unittest
from xml.etree import ElementTree as ET

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from site_sitemaps import NAMESPACE, write_sitemap

BASE = "https://example.org/NYLL/"


class SitemapTests(unittest.TestCase):
    def setUp(self):
        parent = Path(os.environ.get("NYLL_SITE_TEST_OUTPUT", ROOT / "tmp" / "site-tests"))
        parent.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(dir=parent)
        self.addCleanup(self.temporary.cleanup)
        self.output = Path(self.temporary.name)

    def urls(self, filename):
        return [x.text for x in ET.parse(self.output / filename).findall(f".//{{{NAMESPACE}}}loc")]

    def test_rebuilding_either_section_keeps_the_other_discoverable(self):
        for first, second in [("sitemap-source.xml", "sitemap-guides.xml"),
                              ("sitemap-guides.xml", "sitemap-source.xml")]:
            with self.subTest(first=first):
                write_sitemap(self.output, first, [BASE, BASE + "old/"], BASE)
                write_sitemap(self.output, second, [BASE + "kept/"], BASE)
                write_sitemap(self.output, first, [BASE, BASE + "new/", BASE + "new/"], BASE)
                self.assertEqual(self.urls(first), [BASE, BASE + "new/"])
                self.assertEqual(self.urls(second), [BASE + "kept/"])
                self.assertEqual(self.urls("sitemap.xml"),
                                 [BASE + "sitemap-source.xml", BASE + "sitemap-guides.xml"])
                self.assertEqual(ET.parse(self.output / "sitemap.xml").getroot().tag,
                                 f"{{{NAMESPACE}}}sitemapindex")

    def test_rejects_query_fragment_and_foreign_urls_before_writing(self):
        for invalid in [BASE + "?q=groups", BASE + "#declaration", "https://example.org/other/",
                        "https://foreign.example/NYLL/"]:
            with self.subTest(url=invalid), self.assertRaises(ValueError):
                write_sitemap(self.output, "sitemap-source.xml", [invalid], BASE)
        self.assertFalse((self.output / "sitemap.xml").exists())

    def test_rejects_mixed_deployment_bases(self):
        write_sitemap(self.output, "sitemap-source.xml", [BASE], BASE)
        before = (self.output / "sitemap.xml").read_bytes()
        with self.assertRaises(ValueError):
            write_sitemap(self.output, "sitemap-guides.xml", ["https://example.org/elsewhere/"],
                          "https://example.org/elsewhere/")
        self.assertEqual((self.output / "sitemap.xml").read_bytes(), before)
        self.assertFalse((self.output / "sitemap-guides.xml").exists())


if __name__ == "__main__":
    unittest.main()
