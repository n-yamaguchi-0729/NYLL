"""Keep the source browser and mathematical guides in one sitemap index.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from pathlib import Path
from urllib.parse import urlsplit
from xml.etree import ElementTree as ET

NAMESPACE = "http://www.sitemaps.org/schemas/sitemap/0.9"
COMPONENTS = ("sitemap-source.xml", "sitemap-guides.xml")


def write_sitemap(output: Path, filename: str, urls: list[str], site_url: str) -> None:
    """Replace one generated sitemap without dropping the other builder's URLs."""
    if filename not in COMPONENTS:
        raise ValueError("Unknown generated sitemap")
    site_url = site_url.rstrip("/") + "/"
    base = urlsplit(site_url)
    if (base.scheme not in {"http", "https"} or not base.netloc or base.username
            or base.password or base.query or base.fragment):
        raise ValueError("Sitemap base must be an absolute site URL")

    def validate(values: list[str]) -> None:
        if len(values) > 50_000:
            raise ValueError("Split sitemaps with more than 50,000 URLs before publishing")
        for url in values:
            parsed = urlsplit(url)
            if (parsed.scheme != base.scheme or parsed.netloc != base.netloc
                    or not parsed.path.startswith(base.path) or parsed.query or parsed.fragment):
                raise ValueError(f"Sitemap URL is not a canonical page within {site_url}: {url}")

    urls = list(dict.fromkeys(urls))
    validate(urls)
    present = []
    for component in COMPONENTS:
        path = output / component
        if component == filename:
            present.append(component)
        elif path.is_file():
            existing = ET.parse(path)
            if existing.getroot().tag != f"{{{NAMESPACE}}}urlset":
                raise ValueError(f"Unexpected sitemap format: {component}")
            validate([loc.text or "" for loc in existing.findall(f".//{{{NAMESPACE}}}loc")])
            present.append(component)
    sitemap = ET.Element("urlset", xmlns=NAMESPACE)
    for url in urls:
        ET.SubElement(ET.SubElement(sitemap, "url"), "loc").text = url
    output.mkdir(parents=True, exist_ok=True)
    ET.ElementTree(sitemap).write(output / filename, encoding="utf-8", xml_declaration=True)
    index = ET.Element("sitemapindex", xmlns=NAMESPACE)
    for component in present:
        ET.SubElement(ET.SubElement(index, "sitemap"), "loc").text = site_url + component
    ET.ElementTree(index).write(output / "sitemap.xml", encoding="utf-8", xml_declaration=True)
