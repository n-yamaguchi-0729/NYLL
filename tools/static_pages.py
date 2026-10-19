"""Crawlable source-browser pages, sharing the interactive browser's HTML shell.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
"""
from __future__ import annotations

import hashlib
from html import escape
import json
from pathlib import Path
import re
from urllib.parse import quote, urljoin, urlsplit


INVENTORY = ".source-pages.json"
SCHEMA = "nyll.source-pages.v1"
MARKER = "<!-- Generated NYLL source-browser page. -->"


def route(kind: str, name: str) -> str:
    if kind not in {"modules", "browse"} or not name or name in {".", ".."} or re.search(r"[/\\\x00-\x1f\x7f]", name):
        raise ValueError("Unsafe source-browser route")
    return f"{kind}/{quote(name, safe='')}/"


def safe_url(value: str, context: str) -> str:
    try:
        resolved = urljoin(context, value)
        parsed = urlsplit(resolved)
        if parsed.scheme in {"http", "https", "mailto"} and not parsed.username and not parsed.password:
            return resolved
    except ValueError:
        pass
    return ""


def inline(value: str, context: str) -> str:
    # Math is recognized before emphasis; source HTML is always escaped text.
    pattern = re.compile(r"(\$\$[\s\S]*?\$\$|(?<!\\)\$[^$\n]+\$|\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\])|`([^`\n]+)`|\[([^\]\n]+)\]\(([^\s)]+)(?:\s+\"[^\"]*\")?\)|\*\*([^*\n]+)\*\*|(?<!\*)\*([^*\n]+)\*(?!\*)")
    result, end = [], 0
    for match in pattern.finditer(value):
        result.append(escape(value[end:match.start()]))
        if match[1] is not None:
            result.append(escape(match[1]))
        elif match[2] is not None:
            result.append(f"<code>{escape(match[2])}</code>")
        elif match[3] is not None:
            link = safe_url(match[4], context)
            result.append(f'<a href="{escape(link)}">{escape(match[3])}</a>' if link else escape(match[3]))
        elif match[5] is not None:
            result.append(f"<strong>{escape(match[5])}</strong>")
        else:
            result.append(f"<em>{escape(match[6])}</em>")
        end = match.end()
    return "".join(result) + escape(value[end:])


def markdown(value: str, context: str) -> str:
    """The source browser's small Markdown subset, without executable raw HTML."""
    output, paragraph, quoted, code = [], [], [], []
    listing, fenced = "", False

    def flush() -> None:
        nonlocal listing
        if paragraph:
            output.append(f'<p>{inline(" ".join(paragraph), context)}</p>')
            paragraph.clear()
        if listing:
            output.append(f"</{listing}>")
            listing = ""
        if quoted:
            output.append(f'<blockquote>{inline(" ".join(quoted), context)}</blockquote>')
            quoted.clear()

    for line in value.strip().splitlines():
        if re.match(r"\s*```", line):
            flush()
            if fenced:
                output.append("<pre><code>" + escape("\n".join(code)) + "</code></pre>")
                code.clear()
            fenced = not fenced
        elif fenced:
            code.append(line)
        elif not line.strip():
            flush()
        elif heading := re.match(r"\s{0,3}(#{1,6})\s+(.+)", line):
            flush()
            level = 4 if len(heading[1]) > 2 else 3
            output.append(f"<h{level}>{inline(heading[2], context)}</h{level}>")
        elif item := re.match(r"\s*(?:([-*+])|(\d+)\.)\s+(.+)", line):
            kind = "ul" if item[1] else "ol"
            if paragraph or quoted or listing != kind:
                flush()
            if not listing:
                output.append(f"<{kind}>")
                listing = kind
            output.append(f"<li>{inline(item[3], context)}</li>")
        elif quotation := re.match(r"\s*>\s?(.*)", line):
            if paragraph or listing:
                flush()
            quoted.append(quotation[1])
        else:
            if listing or quoted:
                flush()
            paragraph.append(line.strip())
    flush()
    if code:
        output.append("<pre><code>" + escape("\n".join(code)) + "</code></pre>")
    return "\n".join(output)


def excerpt(value: str, limit: int = 160) -> str:
    value = re.sub(r"^\s*#{1,6}\s+.*$", "", value, flags=re.M)
    value = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", value)
    value = re.sub(r"[`*_]", "", value)
    value = " ".join(value.split())
    return value if len(value) <= limit else value[:limit].rstrip() + "…"


def library_name(library: dict) -> str:
    value = library.get("displayName") or library.get("name") or library["id"]
    value = re.sub(r"([a-z])([A-Z])", r"\1 \2", value)
    value = re.sub(r"([A-Z])([A-Z][a-z])", r"\1 \2", value)
    return re.sub(r"(Yamaguchi)26 ", r"\1 2026 ", value)


def count(value: int, singular: str, plural: str | None = None) -> str:
    return f"{value:,} {singular if value == 1 else plural or singular + 's'}"


def link(href: str, label: str, attributes: str = "") -> str:
    return f'<a href="{escape(href)}" data-route {attributes}>{label}</a>'


def source_link(url: str, label: str = "View source ↗", cls: str = "") -> str:
    return f'<a class="{escape(cls)}" href="{escape(url)}">{escape(label)}</a>'


def sidebar(manifest: dict, prefix: str, active_library: str = "", active_module: str = "") -> str:
    parts = ['<ul class="tree"><li class="tree-root">' + link(prefix + "browse/", "All source code") + "</li>"]
    for library in manifest["libraries"]:
        active = library["id"] == active_library
        current = ' aria-current="page"' if active and not active_module else ""
        parts.append(f'<li><details{" open" if active else ""}><summary>{escape(library_name(library))}</summary><ul><li>' +
                     link(prefix + route("browse", library["id"]), "Library overview", f'class="tree-overview"{current}') + "</li></ul></details></li>")
    for module in manifest["modules"]:
        if not module["library"]:
            current = ' aria-current="page"' if module["name"] == active_module else ""
            parts.append("<li>" + link(prefix + route("modules", module["name"]), escape(module["name"] + ".lean"), f'class="tree-module"{current}') + "</li>")
    return "".join(parts) + "</ul>"


def source_catalog(manifest: dict) -> str:
    rows = []
    for index, library in enumerate(manifest["libraries"], 1):
        name = library_name(library)
        href = "../" + route("browse", library["id"])
        rows.append(f'<article class="library-row"><span class="row-number" aria-hidden="true">{index:02}</span><div><h3>' +
                    link(href, escape(name)) + '</h3>' +
                    f'<div class="row-meta"><span>{count(library["moduleCount"], "module")}</span><code>{escape(library["rootModule"])}</code></div></div>' +
                    link(href, "↗", f'class="row-arrow" aria-label="Browse {escape(name)}"') + "</article>")
    return ('<header class="page-head"><h1 class="page-title">All source code</h1><p>The complete published NYLL collection, organized by source library.</p></header>' +
            '<section aria-labelledby="libraries-heading"><div class="catalog-intro"><h2 id="libraries-heading">Source libraries</h2>' +
            f'<span class="count">{count(len(rows), "library", "libraries")} · {count(manifest["counts"]["modules"], "module")}</span></div>' +
            "".join(rows) + "</section>")


def module_rows(items: list[dict], library: dict, prefix: str) -> str:
    base = f'Nyll.{library["id"]}.'
    rows = []
    for module in items:
        label = module["name"].removeprefix(base)
        description = excerpt(module["doc"], 220)
        rows.append('<article class="module-row"><div class="module-row-head">' +
                    link(prefix + route("modules", module["name"]), escape(label + ".lean")) +
                    f'<span class="count">{count(module["declarationCount"], "declaration")}</span></div>' +
                    (f'<p class="math-summary">{escape(description)}</p>' if description else "") + "</article>")
    return "".join(rows)


def library_content(library: dict, modules: dict[str, dict], prefix: str) -> str:
    items = [m for m in modules.values() if m["library"] == library["id"]]
    root = modules[library["rootModule"]]
    description = root["doc"] or library["doc"]
    return ('<header class="page-head"><span class="eyebrow">Library</span>' +
            f'<h1 class="page-title">{escape(library_name(library))}</h1><div class="page-actions"><span>{count(len(items), "module")}</span>' +
            link(prefix + route("modules", root["name"]), "Root module") + source_link(root["sourceUrl"]) + "</div></header>" +
            (f'<section class="module-overview"><h2 class="section-label">Library documentation</h2><div class="documentation">{markdown(description, root["sourceUrl"])}</div></section>' if description else "") +
            '<section aria-labelledby="modules-heading"><div class="catalog-toolbar"><h2 id="modules-heading">Modules</h2></div><div id="module-list">' +
            module_rows(items, library, prefix) + "</div></section>")


def imports(label: str, names: list[str], modules: dict[str, dict], prefix: str) -> str:
    rows = "".join("<li>" + (link(prefix + route("modules", name), escape(name)) if name in modules else escape(name)) + "</li>" for name in names)
    return f'<details class="dependency-details"><summary>{label}<span>{len(names):,}</span></summary>' + (f"<ul>{rows}</ul>" if rows else '<p class="muted">None.</p>') + "</details>"


def declaration_content(entry: dict, module: dict, prefix: str) -> str:
    name, identity = entry["name"], entry["id"]
    short = name.rsplit(".", 1)[-1]
    href = prefix + route("modules", module["name"]) + "#" + quote("declaration-" + identity, safe="")
    context = "\n".join(command["source"] for command in entry["context"])
    return (f'<article class="declaration" data-declaration="{escape(identity)}" id="declaration-{escape(identity)}"><div class="declaration-heading"><div class="declaration-title">' +
            f'<span class="kind">{escape(entry["kind"])}</span><h3>{link(href, escape(short))}</h3>' +
            ('<span class="unproved">Contains sorry</span>' if entry["hasSorry"] else "") + "</div>" +
            source_link(entry["sourceUrl"], f'L{entry["line"]} ↗', "source-link") + "</div>" +
            (f'<div class="qualified-name">{escape(name)}</div>' if name != short else "") +
            (f'<section class="declaration-doc"><span class="content-label">Documentation</span><div class="documentation">{markdown(entry["doc"], entry["sourceUrl"])}</div></section>' if entry["doc"] else "") +
            (f'<details class="context-details"><summary>Source context <span>{count(len(entry["context"]), "command")}</span></summary><div class="context-mount"><p class="context-note">Surrounding namespaces, section variables, and local commands at this declaration.</p><pre class="statement"><code>{escape(context)}</code></pre></div></details>' if context else "") +
            '<div class="formal-statement"><span class="content-label">Lean source · ' +
            ("full declaration" if entry["statementIncludesBody"] else "statement") + '</span><pre class="statement' +
            (" source-complete" if entry["statementIncludesBody"] else "") + f'"><code>{escape(entry["statement"])}</code></pre></div></article>')


def module_content(module: dict, modules: dict[str, dict], prefix: str) -> str:
    declarations = module["declarations"]
    return ('<header class="page-head"><span class="eyebrow">Module</span>' +
            f'<h1 class="page-title module-title">{escape(module["name"].rsplit(".", 1)[-1])}.lean</h1><div class="qualified-module">{escape(module["name"])}</div>' +
            f'<div class="page-actions"><span>{count(len(declarations), "declaration")} indexed from source</span>{source_link(module["sourceUrl"])}</div></header>' +
            (f'<section class="module-overview"><h2 class="section-label">Module documentation</h2><div class="documentation">{markdown(module["doc"], module["sourceUrl"])}</div></section>' if module["doc"] else "") +
            f'<div class="dependencies">{imports("Imports", module["imports"], modules, prefix)}{imports("Imported by", module["importedBy"], modules, prefix)}</div>' +
            '<section aria-labelledby="declarations-heading"><div class="catalog-toolbar"><h2 id="declarations-heading">Declarations</h2></div>' +
            ("".join(declaration_content(entry, module, prefix) for entry in declarations) if declarations else '<p class="empty">This module has no indexed declarations. Its imports and full source are available here.</p>') +
            '</section><p class="page-footer">Statements and documentation are read from the Lean source at the revision shown. Source entries are not a measure of mathematical completeness.</p>')


def replace_one(pattern: str, value, source: str) -> str:
    updated, number = re.subn(pattern, value, source, count=1, flags=re.S)
    if number != 1:
        raise ValueError("Source-browser shell is missing an expected page element")
    return updated


def page(shell: str, manifest: dict, site_url: str, title: str, description: str,
         canonical: str, content: str | None, kind: str, identity: str = "", library: str = "") -> str:
    prefix = "./" if kind == "home" else "../" if kind == "catalog" else "../../"
    rendered = shell
    if content is not None:
        rendered = replace_one(r'(<main\b[^>]*\bid="main"[^>]*>).*?(</main>)', lambda m: m[1] + content + m[2], rendered)
    rendered = replace_one(r'(<nav\b[^>]*\bid="file-tree"[^>]*>).*?(</nav>)', lambda m: m[1] + sidebar(manifest, "./", library, identity if kind == "module" else "") + m[2], rendered)
    revision = manifest["source"]
    rendered = replace_one(r'(<div id="revision"[^>]*>).*?(</div>)', lambda m: m[1] + '<p>Source revision ' + source_link(revision["repo"] + "/tree/" + revision["commit"], revision["commitShort"]) + "</p>" + m[2], rendered)
    if kind == "home":
        # The landing page is a guide catalog, not a hidden source browser.
        for pattern in (r'<aside\b[^>]*\bid="sidebar"[^>]*>.*?</aside>',
                        r'<button\b[^>]*\bid="tree-toggle"[^>]*>.*?</button>',
                        r'<button\b[^>]*\bid="sidebar-backdrop"[^>]*>.*?</button>',
                        r'<form\b[^>]*\bclass="search-form"[^>]*>.*?</form>',
                        r'<noscript>.*?</noscript>'):
            rendered = replace_one(pattern, "", rendered)
    # Relative shell assets, home links and form action must work at either root.
    rendered = re.sub(r'\b(href|src|action)="\./([^\"]*)"', lambda m: f'{m[1]}="{prefix}{m[2]}"', rendered)
    rendered = replace_one(r'<title>.*?</title>', lambda _: f"<title>{escape(title)}</title>", rendered)
    rendered = replace_one(r'<meta name="description"[^>]*>', lambda _: f'<meta name="description" content="{escape(description)}">', rendered)
    rendered = re.sub(r'\s*<link\b[^>]*rel="canonical"[^>]*>', "", rendered)
    rendered = re.sub(r'\s*<meta\b[^>]*property="og:[^"]+"[^>]*>', "", rendered)
    tags = (f'\n  <link rel="canonical" href="{escape(canonical)}">' +
            f'\n  <meta property="og:type" content="website">\n  <meta property="og:site_name" content="NYLL">' +
            f'\n  <meta property="og:title" content="{escape(title)}">\n  <meta property="og:description" content="{escape(description)}">' +
            f'\n  <meta property="og:url" content="{escape(canonical)}">\n')
    rendered = rendered.replace("</head>", tags + "</head>", 1)
    rendered = replace_one(r'<body\b[^>]*>', lambda _: f'<body data-page="{kind}" data-static-page="{kind}" data-static-id="{escape(identity)}" data-site-root="{escape(site_url)}">', rendered)
    rendered = re.sub(r'<noscript>.*?</noscript>', '<noscript><p class="noscript">Browse the libraries and modules using the links on this page. Search and expandable proof source need JavaScript.</p></noscript>', rendered, flags=re.S)
    return MARKER + "\n" + rendered


def generated_path(output: Path, relative: str) -> Path:
    path = Path(relative)
    if relative == "browse/index.html":
        pass
    elif len(path.parts) != 3 or path.parts[0] not in {"modules", "browse"} or path.parts[2] != "index.html":
        raise ValueError("Invalid generated source-page inventory path")
    else:
        route(path.parts[0], path.parts[1])
    target = output / path
    if any(part.is_symlink() for part in (target, target.parent, target.parent.parent)):
        raise ValueError("Refusing a redirected generated source page")
    if not target.resolve().is_relative_to(output.resolve()):
        raise ValueError("Generated source page escapes its output")
    return target


def write_pages(output: Path, shell: str, manifest: dict, modules: dict[str, dict], site_url: str) -> list[str]:
    """Write source pages, deleting only unchanged stale pages in our inventory."""
    # A changed renderer or stylesheet must not reuse the previous deployment's
    # cached asset. Hash once per build, before rendering the shared shell.
    def version_asset(match: re.Match) -> str:
        asset = output / "assets" / match[2]
        digest = hashlib.sha256(asset.read_bytes()).hexdigest()[:16]
        return f'{match[1]}="./assets/{match[2]}?v={digest}"'

    shell = re.sub(r'\b(href|src)="\./assets/([\w.-]+\.(?:css|js))"', version_asset, shell)
    inventory = output / INVENTORY
    previous = {}
    if inventory.is_symlink():
        raise ValueError("Refusing a redirected source-page inventory")
    if inventory.exists():
        data = json.loads(inventory.read_text(encoding="utf-8"))
        if data.get("schema") != SCHEMA or not isinstance(data.get("pages"), dict):
            raise ValueError("Invalid generated source-page inventory")
        previous = data["pages"]
    names = {"browse/index.html"} | {f'modules/{name}/index.html' for name in modules} | {f'browse/{library["id"]}/index.html' for library in manifest["libraries"]}
    # Validate all preimages before changing or removing any source-page files.
    for relative in names | previous.keys():
        target = generated_path(output, relative)
        if target.exists():
            if relative not in previous or hashlib.sha256(target.read_bytes()).hexdigest() != previous[relative]:
                raise ValueError("Refusing to overwrite an unrelated or modified source page: " + relative)
    updated, urls = {}, [site_url]

    def write(relative: str, rendered: str, canonical: str) -> None:
        target = generated_path(output, relative)
        target.parent.mkdir(parents=True, exist_ok=True)
        payload = rendered.encode("utf-8")
        target.write_bytes(payload)
        updated[relative] = hashlib.sha256(payload).hexdigest()
        urls.append(canonical)

    catalog_url = site_url + "browse/"
    write("browse/index.html", page(shell, manifest, site_url, "All source code · NYLL",
          "Browse all NYLL source libraries, modules, and Lean declarations.", catalog_url,
          source_catalog(manifest), "catalog"), catalog_url)
    libraries = {library["id"]: library for library in manifest["libraries"]}
    for library in manifest["libraries"]:
        name = library_name(library)
        root = modules[library["rootModule"]]
        description = excerpt(root["doc"] or library["doc"]) or f"{name}: Lean source modules, mathematical statements, and documentation."
        canonical = site_url + route("browse", library["id"])
        write(f'browse/{library["id"]}/index.html', page(shell, manifest, site_url, f"{name} · NYLL", description, canonical,
              library_content(library, modules, "../../"), "library", library["id"], library["id"]), canonical)
    for name, module in modules.items():
        library = library_name(libraries[module["library"]]) if module["library"] else "Library"
        title = f"{name} · NYLL"
        description = excerpt(module["doc"]) or f"{name}: Lean source, declarations, and documentation in {library}."
        canonical = site_url + route("modules", name)
        write(f"modules/{name}/index.html", page(shell, manifest, site_url, title, description, canonical,
              module_content(module, modules, "../../"), "module", name, module["library"]), canonical)
    for relative in previous.keys() - names:
        target = generated_path(output, relative)
        target.unlink(missing_ok=True)
        if target.parent.exists() and not any(target.parent.iterdir()):
            target.parent.rmdir()
    # The root shell is maintained input, not part of stale-page ownership.
    title_match = re.search(r"<title>(.*?)</title>", shell, re.S)
    description_match = re.search(r'<meta name="description" content="([^"]*)"', shell)
    from html import unescape
    home = page(shell, manifest, site_url, unescape(title_match[1]) if title_match else "NYLL",
                unescape(description_match[1]) if description_match else manifest["description"], site_url, None, "home")
    (output / "index.html").write_text(home, encoding="utf-8")
    inventory.write_text(json.dumps({"schema": SCHEMA, "pages": updated}, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    return urls
