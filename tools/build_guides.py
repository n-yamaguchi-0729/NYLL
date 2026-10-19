#!/usr/bin/env python3
"""Build reviewed mathematical guides from immutable published Lean sources.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import quote, urlparse
from xml.etree import ElementTree as ET
from site_sitemaps import NAMESPACE, write_sitemap

from build_site import parse_module, SourceError, SITE_URL, COMMANDS, MODIFIERS

OWNER = "n-yamaguchi-0729"
NYLL = f"https://github.com/{OWNER}/NYLL"
REPOSITORIES = {
    "pro-c-groups": "ProCGroups",
    "class-field-theory": "ClassFieldTheory",
    "sawin-totally-real-towers": "SawinTotallyRealTowers",
    "etale-fundamental-groups-and-cohomology": "EtaleFundamentalGroupsAndCohomology",
    "jacobian-varieties": "JacobianVarieties",
    "research-papers": "YamaguchiPapersFormalization",
    "anabelian-geometry": "AnabelianGeometry",
}
SLUG = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
HEADER_WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
BODY_COMMANDS = (COMMANDS - MODIFIERS - {"import", "prelude", "module"}) | {
    "assert_not_exists", "assert_not_imported",
}
DEPENDENCY_CONFIG = ("lake-manifest.json", "lean-toolchain")
e = html.escape


def git(path: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(path), *args], text=True, encoding="utf-8") .strip()


def source_text(path: Path, revision: str, relative: str) -> str:
    # Never execute or import code from a published repository.
    return subprocess.check_output(["git", "-C", str(path), "show", f"{revision}:{relative}"],
                                   text=True, encoding="utf-8")


def source_blobs(path: Path, revision: str, relatives: list[str]) -> dict[str, bytes]:
    """Read one import frontier in one Git process, retaining exact blob bytes."""
    relatives = list(dict.fromkeys(relatives))
    if any("\n" in name or "\r" in name or "\0" in name for name in relatives):
        raise SourceError("Invalid path in Git batch request")
    request = "".join(f"{revision}:{name}\n" for name in relatives).encode("utf-8")
    output = subprocess.check_output(["git", "-C", str(path), "cat-file", "--batch"], input=request)
    blobs, position = {}, 0
    for name in relatives:
        end = output.find(b"\n", position)
        if end < 0:
            raise SourceError(f"Incomplete Git batch response: {name}")
        fields = output[position:end].split()
        if len(fields) != 3 or fields[1] != b"blob" or not fields[2].isdigit():
            raise SourceError(f"Missing or non-blob published source: {name}")
        start, size = end + 1, int(fields[2])
        position = start + size + 1
        if position > len(output) or output[position - 1:position] != b"\n":
            raise SourceError(f"Incomplete Git blob: {name}")
        blobs[name] = output[start:start + size]
    if position != len(output):
        raise SourceError("Unexpected trailing Git batch output")
    return blobs


def header_imports(source: str, path: str) -> list[str]:
    """Read only Lean's header; reject syntax we cannot classify safely.

    The supported header is `[module] [prelude] ([public] [meta] import
    [all] Module.Name)*`, as in Lean 4's Parser.Module.Syntax. Module names
    use the ASCII subset present in these publications. Escaped/Unicode names
    require an explicit parser update instead of silently losing dependencies.
    """
    position, size = (1 if source.startswith("\ufeff") else 0), len(source)

    def fail(message: str) -> None:
        raise SourceError(f"Unsupported or malformed Lean header in {path}: {message}")

    def token() -> str:
        nonlocal position
        while position < size:
            if source[position].isspace():
                position += 1
            elif source.startswith("--", position):
                end = source.find("\n", position + 2)
                position = size if end < 0 else end + 1
            elif source.startswith("/-", position):
                depth, position = 1, position + 2
                while depth and position < size:
                    if source.startswith("/-", position):
                        depth, position = depth + 1, position + 2
                    elif source.startswith("-/", position):
                        depth, position = depth - 1, position + 2
                    else:
                        position += 1
                if depth:
                    fail("unterminated comment")
            else:
                break
        if position == size:
            return ""
        match = HEADER_WORD.match(source, position)
        if match:
            position = match.end()
            return match.group()
        if source.startswith("@[", position):
            position += 2
            return "@["
        value = source[position]
        position += 1
        return value

    word = token()
    modular = word == "module"
    if modular:
        word = token()
    if word == "prelude":
        word = token()
    imports = []
    while word:
        modifiers = []
        while word in MODIFIERS:
            modifiers.append(word)
            word = token()
        if word != "import":
            if word in BODY_COMMANDS or (not modifiers and word in {"@[", "#"}):
                return imports
            fail(f"unexpected token {word!r}")
        if modifiers not in ([], ["public"], ["meta"], ["public", "meta"]):
            fail("unsupported import modifiers")
        if modifiers and not modular:
            fail("import modifiers require 'module'")
        word = token()
        if word == "all":
            if not modular or "public" in modifiers:
                fail("'import all' requires 'module' and cannot be public")
            word = token()
        if not MODULE_NAME.fullmatch(word) or word in COMMANDS or word == "all":
            fail(f"expected a supported module name, found {word!r}")
        imports.append(word)
        word = token()
    return imports


def dependency_sources(checkout: Path, revision: str, publication: dict,
                       selected: set[str]) -> tuple[dict[str, str], dict[str, str]]:
    """Verify and lock exactly the selected files' transitive Nyll imports."""
    sources, hashes = {}, {}
    pending = set(selected) | set(DEPENDENCY_CONFIG)
    while pending:
        frontier = sorted(pending)
        pending = set()
        for path, blob in source_blobs(checkout, revision, frontier).items():
            expected = publication["source_hashes"].get(path)
            if not isinstance(expected, str) or not SHA256.fullmatch(expected):
                raise SourceError(f"Missing publication source hash: {checkout.name}/{path}")
            if hashlib.sha256(blob).hexdigest() != expected:
                raise SourceError(f"Publication source hash mismatch: {checkout.name}/{path}")
            hashes[path] = expected
            if not path.endswith(".lean"):
                continue
            source = blob.decode("utf-8")
            if path in selected:
                sources[path] = source
            for name in header_imports(source, path):
                if name == "Nyll" or name.startswith("Nyll."):
                    dependency = name.replace(".", "/") + ".lean"
                    if dependency not in hashes and dependency not in frontier:
                        pending.add(dependency)
    return sources, dict(sorted(hashes.items()))


def safe_url(value: str) -> str:
    parsed = urlparse(value)
    if parsed.scheme not in {"https", "http"} or not parsed.netloc or parsed.username or parsed.password:
        raise SourceError(f"Expected an HTTP(S) reference URL: {value}")
    return value


def inline(value: str) -> str:
    """Escape raw HTML; preserve math before interpreting small Markdown syntax."""
    pattern = re.compile(r"(\$\$[\s\S]*?\$\$|(?<!\\)\$[^$\n]+\$|\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\])|`([^`]+)`|\*\*([^*]+)\*\*|\[([^\]]+)\]\((https?://[^\s)]+)\)")
    result, pos = [], 0
    for match in pattern.finditer(value):
        result.append(e(value[pos:match.start()]))
        if match[1]:
            result.append(e(match[1]))
        elif match[2]:
            result.append(f"<code>{e(match[2])}</code>")
        elif match[3]:
            result.append(f"<strong>{e(match[3])}</strong>")
        else:
            result.append(f'<a href="{e(safe_url(match[5]))}">{e(match[4])}</a>')
        pos = match.end()
    result.append(e(value[pos:]))
    return "".join(result)


def paragraphs(values: list[str]) -> str:
    return "\n".join(f"<p>{inline(p)}</p>" for value in values for p in value.split("\n\n") if p.strip())


def validate_guide(data: dict) -> None:
    slug = data["slug"]
    if REPOSITORIES.get(slug) != data["repository"]:
        raise SourceError(f"Unknown library or mismatched repository: {slug}")
    refs = [r["id"] for r in data["references"]]
    if len(refs) != len(set(refs)):
        raise SourceError(f"Duplicate bibliography keys in {slug}")
    for ref in data["references"]:
        if not SLUG.fullmatch(ref["id"]) or not isinstance(ref.get("type"), str) or not ref["type"]:
            raise SourceError(f"Invalid bibliography entry in {slug}: {ref['id']}")
        for key in ("author", "title", "year", "url"):
            if not ref.get(key):
                raise SourceError(f"Missing {key} for {slug}/{ref['id']}")
        safe_url(ref["url"])
    seen = set()
    for entry in data["entries"]:
        name = entry["slug"]
        if not SLUG.fullmatch(name) or name in seen:
            raise SourceError(f"Invalid or duplicate entry slug: {slug}/{name}")
        seen.add(name)
        for key in ("title", "summary", "statement", "history", "lean", "references"):
            if not entry.get(key):
                raise SourceError(f"Missing {key} in {slug}/{name}")
        if not set(entry["references"]) <= set(refs):
            raise SourceError(f"Unknown reference in {slug}/{name}")
        if entry["kind"] not in {"theorem", "definition"}:
            raise SourceError(f"Invalid entry kind in {slug}/{name}")
        for target in entry["lean"]:
            relative = Path(target["path"])
            if relative.is_absolute() or ".." in relative.parts or not target["path"].startswith("Nyll/") or relative.suffix != ".lean":
                raise SourceError(f"Invalid source path: {target['path']}")
            if "show" in target and not isinstance(target["show"], bool):
                raise SourceError(f"Expected a boolean show flag: {target['name']}")


def declaration_fingerprint(declaration: dict, imports: list[str]) -> str:
    # Keep focused declaration diagnostics alongside the more conservative file
    # dependency guard, which also requires review for proof-only changes.
    text = declaration["statement"] if declaration["kind"] in {"theorem", "lemma"} else declaration["source"]
    payload = {"declaration": text, "context": [c["source"] for c in declaration["context"]], "imports": imports}
    return hashlib.sha256(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def extract(guide: dict, sources: Path, fetch: bool) -> tuple[list[dict], dict]:
    repo = guide["repository"]
    checkout = sources / repo
    remote = f"https://github.com/{OWNER}/{repo}"
    if fetch:
        if not checkout.exists():
            checkout.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "clone", "--depth", "1", remote + ".git", str(checkout)], check=True)
            revision = git(checkout, "rev-parse", "HEAD")
        else:
            if git(checkout, "remote", "get-url", "origin").removesuffix(".git") != remote:
                raise SourceError(f"Unexpected source remote in {checkout}")
            subprocess.run(["git", "-C", str(checkout), "fetch", "--depth", "1", "origin", "HEAD"], check=True)
            revision = git(checkout, "rev-parse", "FETCH_HEAD")
    else:
        revision = git(checkout, "rev-parse", "HEAD")
    if not SHA.fullmatch(revision):
        raise SourceError(f"Invalid published revision: {repo}")
    publication = json.loads(source_text(checkout, revision, ".github/verification/publication.json"))
    origin = publication["source_commit"]
    if not SHA.fullmatch(origin) or publication["canonical_repository"] != f"{OWNER}/NYLL" or publication["repository"] != f"{OWNER}/{repo}":
        raise SourceError(f"Invalid source provenance: {repo}")
    selected_paths = {target["path"] for entry in guide["entries"] for target in entry["lean"]}
    sources_by_path, dependency_hashes = dependency_sources(checkout, revision, publication, selected_paths)
    modules = {}
    entries, fingerprints = [], {}
    for entry in guide["entries"]:
        selected = []
        for target in entry["lean"]:
            path = target["path"]
            if path not in modules:
                source = sources_by_path[path]
                modules[path] = parse_module(source, path.removesuffix(".lean").replace("/", "."), path,
                                             f"{remote}/blob/{revision}")
            module = modules[path]
            matches = [d for d in module["declarations"] if d["name"] == target["name"]]
            if len(matches) != 1:
                raise SourceError(f"Expected one published declaration: {repo}/{path}: {target['name']} (found {len(matches)})")
            decl = matches[0]
            if decl["hasSorry"] or decl["kind"] == "axiom":
                raise SourceError(f"Selected declaration is unfinished: {target['name']}")
            key = f"{guide['slug']}/{entry['slug']}/{target['name']}"
            fingerprints[key] = declaration_fingerprint(decl, module["imports"])
            selected.append({"declaration": decl, "module": module, "show": target.get("show", False),
                             "nyllUrl": f"{NYLL}/blob/{origin}/{quote(path)}#L{decl['line']}-L{decl['endLine']}"})
        entries.append({**entry, "selected": selected})
    return entries, {"repository": repo, "revision": revision, "nyllRevision": origin,
                     "fingerprints": fingerprints, "dependencyHashes": dependency_hashes}


def bibliography(refs: list[dict]) -> str:
    rows = []
    for ref in refs:
        publication = ", ".join(str(ref[key]) for key in ("journal", "publisher", "volume", "pages", "year") if ref.get(key))
        note = f" <span class=\"muted\">{e(ref['note'])}</span>" if ref.get("note") else ""
        rows.append(f'<li id="ref-{e(ref["id"])}"><span>{e(ref["author"])}</span>. '
                    f'<a href="{e(safe_url(ref["url"]))}"><cite>{e(ref["title"])}</cite></a>. {e(publication)}.{note}</li>')
    return '<ol class="references">' + "\n".join(rows) + '</ol>'


def page(title: str, description: str, content: str, depth: int, route: str, site_url: str) -> str:
    base = "../" * depth
    return f'''<!doctype html>
<!-- Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729 -->
<html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="color-scheme" content="light dark">
<title>{e(title)} · NYLL</title><meta name="description" content="{e(description)}">
<link rel="canonical" href="{e(site_url + route)}">
<meta property="og:title" content="{e(title)} · NYLL"><meta property="og:description" content="{e(description)}">
<meta property="og:type" content="article"><meta property="og:url" content="{e(site_url + route)}">
<link rel="icon" href="{base}assets/favicon.svg" type="image/svg+xml">
<link rel="stylesheet" href="{base}assets/site.css"><link rel="stylesheet" href="{base}assets/guides.css">
<script defer src="{base}assets/guides.js"></script>
</head><body class="guide-body {'guide-overview' if depth == 2 else 'guide-entry'}">
<a class="skip-link" href="#main">Skip to content</a>
<header class="site-header guide-header"><a class="brand" href="{base}">NYLL</a>
<nav aria-label="Main navigation"><a href="{base}#published-libraries">Libraries</a><a href="{base}browse/">All source code</a><a href="{NYLL}">GitHub ↗</a></nav></header>
<div class="guide-layout"><main id="main" class="guide-main">{content}</main>
<footer class="guide-footer">© 2026 Naganori Yamaguchi · Apache-2.0<br>Original code is written by OpenAI Codex. Source-specific credits and licenses are preserved in the linked repositories.<br><a href="{NYLL}#ai-written-code-and-verification">Authorship and verification</a> · <a href="{base}">NYLL home</a></footer>
</div></body></html>'''


def source_block(selected: dict) -> str:
    decl, module = selected["declaration"], selected["module"]
    context = "\n\n".join(c["source"] for c in decl["context"])
    notices = "\n\n".join(n["text"] for n in module.get("attribution", {}).get("notices", []))
    # Definition values carry mathematical content, unlike theorem proofs.
    code = decl["source"] if decl["kind"] in {"def", "abbrev"} else decl["statement"]
    details = f'<details><summary>In-scope Lean context</summary><pre><code class="language-lean">{e(context)}</code></pre></details>' if context else ""
    full = "" if code.strip() == decl["source"].strip() else f'<details><summary>Full declaration and proof</summary><pre><code class="language-lean">{e(decl["source"])}</code></pre></details>'
    credits = f'<details><summary>Source credits and license</summary><pre>{e(notices)}</pre></details>' if notices else ""
    return f'''<article class="lean-source"><h3><code>{e(decl['name'])}</code></h3>
<p class="source-links"><a href="{e(decl['sourceUrl'])}">Published library source ↗</a><a href="{e(selected['nyllUrl'])}">Same source in NYLL ↗</a></p>
<pre><code class="language-lean">{e(code)}</code></pre>{details}{full}{credits}</article>'''


def entry_page(guide: dict, entry: dict, snapshot: dict, site_url: str) -> str:
    repo_url = f"https://github.com/{OWNER}/{guide['repository']}"
    related = ""
    visible = [s for i, s in enumerate(entry["selected"]) if i == 0 or s.get("show")]
    linked = [s for s in entry["selected"][1:] if not s.get("show")]
    if linked:
        links = "".join(f'<li><a href="{e(s["declaration"]["sourceUrl"])}"><code>{e(s["declaration"]["name"])}</code></a></li>'
                        for s in linked)
        related = f'<details class="related-sources"><summary>Related Lean sources</summary><ul>{links}</ul></details>'
    content = f'''<header class="guide-hero"><h1>{e(entry['title'])}</h1><p class="lead">{inline(entry['summary'])}</p></header>
<section id="statement" class="guide-section mathematical-statement"><h2>Mathematical statement</h2>{paragraphs(entry['statement'])}</section>
<section id="lean" class="guide-section"><h2>Lean code</h2>{''.join(source_block(s) for s in visible)}{related}</section>
<p class="source-version">Published source: <a href="{repo_url}/commit/{snapshot['revision']}">{snapshot['revision'][:8]}</a>.</p>
<p class="back-link"><a href="../">← All selected results in {e(guide['title'])}</a></p>'''
    return page(entry["title"], entry["summary"], content, 3, f"libraries/{guide['slug']}/{entry['slug']}/", site_url)


def overview_page(guide: dict, entries: list[dict], site_url: str) -> str:
    cards = "\n".join(f'''<li><a href="{x['slug']}/"><h3>{e(x['title'])}<span aria-hidden="true"> →</span></h3><p>{inline(x['summary'])}</p></a></li>''' for x in entries)
    used = {ref for entry in entries for ref in entry["references"]}
    refs = [ref for ref in guide["references"] if ref["id"] in used]
    content = f'''<header class="guide-hero"><h1>{e(guide['title'])}</h1><div class="overview">{paragraphs(guide['overview'])}</div>
<div class="guide-actions"><a class="primary" href="https://github.com/{OWNER}/{guide['repository']}">{e(guide['repository'])} on GitHub ↗</a></div></header>
<section class="guide-section"><h2>Selected results</h2><ul class="result-grid">{cards}</ul></section>
<section class="guide-section"><h2>References used in these guides</h2>{bibliography(refs)}</section>'''
    return page(guide["title"], guide["summary"], content, 2, f"libraries/{guide['slug']}/", site_url)


def checked_output_path(output: Path, relative: str) -> Path:
    """Confine generated files without following an existing symlink."""
    target = output / relative
    if not target.is_relative_to(output) or ".." in Path(relative).parts:
        raise SourceError(f"Guide output path escapes its directory: {relative}")
    for path in (target, *target.parents):
        if path.is_symlink():
            raise SourceError(f"Symlink in guide output path: {path}")
        if path == output:
            break
    if not target.resolve().is_relative_to(output):
        raise SourceError(f"Guide output path escapes its directory: {relative}")
    if target.exists() and not target.is_file():
        raise SourceError(f"Expected a generated file: {target}")
    return target


def previous_entry_pages(output: Path, site_url: str) -> set[Path]:
    """Read only entry pages recorded by this generator's previous sitemap."""
    sitemap = checked_output_path(output, "sitemap-guides.xml")
    if not sitemap.exists():
        return set()
    try:
        tree = ET.parse(sitemap)
    except ET.ParseError as error:
        raise SourceError(f"Invalid guide sitemap: {error}") from error
    if tree.getroot().tag != f"{{{NAMESPACE}}}urlset":
        raise SourceError("Unexpected guide sitemap format")
    entries = set()
    for row in tree.getroot():
        locations = row.findall(f"{{{NAMESPACE}}}loc")
        if row.tag != f"{{{NAMESPACE}}}url" or len(locations) != 1:
            raise SourceError("Unexpected guide sitemap entry")
        url = locations[0].text or ""
        if not url.startswith(site_url):
            raise SourceError(f"Guide sitemap URL is outside {site_url}: {url}")
        parts = url[len(site_url):].split("/")
        if (len(parts) not in {3, 4} or parts[0] != "libraries" or parts[-1]
                or any(not SLUG.fullmatch(part) for part in parts[1:-1])):
            raise SourceError(f"Invalid guide sitemap page: {url}")
        if len(parts) == 4:
            entries.add(checked_output_path(output, "/".join(parts) + "index.html"))
    return entries


def build(root: Path, output: Path, sources: Path, fetch: bool = False, write_lock: bool = False,
          site_url: str = SITE_URL) -> dict:
    # Check before resolving: otherwise a symlink would lose its identity.
    output = output.absolute()
    if any(path.is_symlink() for path in (output, *output.parents)):
        raise SourceError(f"Symlink in guide output directory: {output}")
    root, output, sources = root.resolve(), output.resolve(), sources.resolve()
    if output == root or output.is_relative_to(root / "Nyll") or output.is_relative_to(root / "site"):
        raise SourceError("Guide output must be separate from source files")
    safe_url(site_url)
    site_url = site_url.rstrip("/") + "/"
    guides_dir = root / "site" / "guides"
    guides = [json.loads((guides_dir / f"{slug}.json").read_text(encoding="utf-8")) for slug in REPOSITORIES]
    all_entries, snapshots, fingerprints, dependency_hashes = {}, {}, {}, {}
    for guide in guides:
        validate_guide(guide)
        entries, snapshot = extract(guide, sources, fetch)
        all_entries[guide["slug"]] = entries
        snapshots[guide["slug"]] = snapshot
        fingerprints.update(snapshot["fingerprints"])
        dependency_hashes[guide["slug"]] = snapshot["dependencyHashes"]
    lock_path = guides_dir / "review-lock.json"
    lock = {"schemaVersion": 2, "fingerprints": fingerprints, "dependencyHashes": dependency_hashes}
    if not write_lock:
        previous = json.loads(lock_path.read_text(encoding="utf-8"))
        if previous.get("schemaVersion") != 2 or not isinstance(previous.get("dependencyHashes"), dict):
            raise SourceError("Mathematical guide review required: dependency review lock is missing or outdated. "
                              "Review the prose and dependencies before --write-lock.")
        changed = sorted(key for key in fingerprints.keys() | previous["fingerprints"].keys()
                         if fingerprints.get(key) != previous["fingerprints"].get(key))
        for slug in sorted(dependency_hashes.keys() | previous["dependencyHashes"].keys()):
            current = dependency_hashes.get(slug, {})
            old = previous["dependencyHashes"].get(slug, {})
            changed.extend(f"{slug}/{path}" for path in sorted(current.keys() | old.keys())
                           if current.get(path) != old.get(path))
        if changed:
            raise SourceError("Mathematical guide review required: selected declarations or their dependencies changed. "
                              "Review the prose and source before --write-lock.\n" + "\n".join(changed))
    # Finish review, rendering, and path checks before changing any output.
    pages, entry_pages, urls = {}, set(), []
    for guide in guides:
        route = f"libraries/{guide['slug']}/"
        entries = all_entries[guide["slug"]]
        pages[checked_output_path(output, route + "index.html")] = overview_page(guide, entries, site_url)
        urls.append(site_url + route)
        for entry in entries:
            entry_route = route + entry["slug"] + "/"
            target = checked_output_path(output, entry_route + "index.html")
            pages[target] = entry_page(guide, entry, snapshots[guide["slug"]], site_url)
            entry_pages.add(target)
            urls.append(site_url + entry_route)
    obsolete = previous_entry_pages(output, site_url) - entry_pages
    for relative in ("sitemap-guides.xml", "sitemap-source.xml", "sitemap.xml", "guide-sources.json"):
        checked_output_path(output, relative)
    if write_lock:
        lock_path.write_text(json.dumps(lock, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    output.mkdir(parents=True, exist_ok=True)
    for target, content in pages.items():
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content, encoding="utf-8")
    for target in sorted(obsolete):
        # Never remove a directory recursively: unrelated files survive.
        if target.exists():
            target.unlink()
        if target.parent.is_dir() and not any(target.parent.iterdir()):
            target.parent.rmdir()
    write_sitemap(output, "sitemap-guides.xml", urls, site_url)
    (output / "guide-sources.json").write_text(json.dumps({k: {a: b for a, b in v.items() if a not in {"fingerprints", "dependencyHashes"}} for k, v in snapshots.items()}, indent=2) + "\n", encoding="utf-8")
    counts = {"libraries": len(guides), "entries": sum(len(x) for x in all_entries.values())}
    print(json.dumps(counts))
    return counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--sources", type=Path, required=True)
    parser.add_argument("--fetch", action="store_true", help="Fetch the current public repository revisions")
    parser.add_argument("--write-lock", action="store_true", help="Record reviewed declarations and dependencies; never use in unattended CI")
    parser.add_argument("--site-url", default=SITE_URL)
    args = parser.parse_args()
    try:
        build(args.root, args.output, args.sources, args.fetch, args.write_lock, args.site_url)
    except (SourceError, OSError, KeyError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Guide build failed: {error}\n")


if __name__ == "__main__":
    main()
