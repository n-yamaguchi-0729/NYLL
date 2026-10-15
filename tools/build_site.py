#!/usr/bin/env python3
# Copyright (c) 2026 Naganori Yamaguchi. Released under Apache 2.0.
# Author: Naganori Yamaguchi (assisted by OpenAI Codex).
# https://github.com/n-yamaguchi-0729
"""Build NYLL's static source browser using only Python's standard library.

The index records explicit, source-written declarations. It is a lexical source
index, not an elaborated Lean environment: generated declarations, implicit
arguments and type inference are deliberately not invented. Full module source
is always available alongside the index. Nested comments, strings, quotation
brackets, attributes and namespace scopes are tokenized before indexing.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from collections import defaultdict
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from urllib.parse import quote, urlsplit

from site_sitemaps import write_sitemap
from static_pages import write_pages


DECLARATIONS = {"theorem", "lemma", "def", "abbrev", "instance", "structure",
                "class", "inductive", "axiom", "opaque"}
SITE_URL = "https://n-yamaguchi-0729.github.io/NYLL/"
MODIFIERS = {"noncomputable", "private", "protected", "unsafe", "partial",
             "nonrec", "public", "meta", "local", "scoped"}
COMMANDS = DECLARATIONS | MODIFIERS | {
    "import", "prelude", "module", "namespace", "section", "end", "universe",
    "universes", "variable", "variables", "open", "export", "attribute",
    "include", "omit", "local", "scoped", "set_option", "syntax", "macro",
    "macro_rules", "elab", "elab_rules", "initialize", "builtin_initialize",
    "example", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
    "run_cmd", "mutual", "deriving", "declare_syntax_cat", "register_option",
    "with_weak_namespace", "alias", "notation3", "unif_hint",
}


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int
    line: int
    column: int
    depth: int
    kind: str = "code"


class SourceError(ValueError):
    """A source cannot be indexed without silently dropping content."""


def lex(source: str) -> list[Token]:
    """Tokenize source, retaining doc comments and exact character positions."""
    lines = [0] + [m.end() for m in re.finditer("\n", source)]
    tokens: list[Token] = []
    brackets: list[str] = []
    i, n = 0, len(source)

    def emit(start: int, end: int, kind: str = "code") -> None:
        row = bisect_right(lines, start) - 1
        tokens.append(Token(source[start:end], start, end, row + 1,
                            start - lines[row], len(brackets), kind))

    while i < n:
        c = source[i]
        if c.isspace():
            i += 1
            continue
        start = i
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = n if end < 0 else end
            continue
        if source.startswith("/-", i):
            level, i = 1, i + 2
            while level and i < n:
                if source.startswith("/-", i):
                    level, i = level + 1, i + 2
                elif source.startswith("-/", i):
                    level, i = level - 1, i + 2
                else:
                    i += 1
            if level:
                raise SourceError(f"Unclosed comment at character {start}")
            if source.startswith("/--", start):
                emit(start, i, "doc")
            elif source.startswith("/-!", start):
                emit(start, i, "module_doc")
            continue
        # Raw strings permit quote characters until the matching hash delimiter.
        raw = re.match(r'r(#+)?"', source[i:]) if c == "r" else None
        if raw:
            hashes = raw.group(1) or ""
            end = source.find('"' + hashes, i + len(raw.group()))
            if end < 0:
                raise SourceError(f"Unclosed raw string at character {start}")
            i = end + 1 + len(hashes)
            emit(start, i, "string")
            continue
        if c == '"':
            i += 1
            while i < n:
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise SourceError(f"Unclosed string at character {start}")
            emit(start, i, "string")
            continue
        if c == "«":
            end = source.find("»", i + 1)
            if end < 0:
                raise SourceError(f"Unclosed escaped identifier at character {start}")
            i = end + 1
            emit(start, i, "identifier")
            continue
        if c == "'":
            # A character literal is distinct from a prime in an identifier.
            char = re.match(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", source[i:])
            if char:
                i += len(char.group())
                emit(start, i, "string")
                continue
        if c.isalpha() or c == "_":
            i += 1
            while i < n and (source[i].isalnum() or source[i] in "_'!?" or
                             "\u2080" <= source[i] <= "\u209f"):
                i += 1
            emit(start, i, "identifier")
            continue
        if source.startswith(":=", i) or source.startswith("=>", i):
            i += 2
            emit(start, i)
            continue
        i += 1
        if c in ")]}⟩⦄":
            matching = {")": "(", "]": "[", "}": "{", "⟩": "⟨", "⦄": "⦃"}[c]
            if not brackets or brackets[-1] != matching:
                raise SourceError(f"Unmatched {c!r} at character {start}")
            brackets.pop()
            emit(start, i)
        else:
            emit(start, i)
            if c in "([{⟨⦃":
                brackets.append(c)
    if brackets:
        raise SourceError("Unclosed source brackets")
    return tokens


def identifier(tokens: list[Token], start: int) -> tuple[str, int]:
    """Read a dotted source identifier, including escaped components."""
    if start >= len(tokens) or tokens[start].kind != "identifier":
        return "", start
    result, i = tokens[start].text, start + 1
    while i + 1 < len(tokens) and tokens[i].text == "." and tokens[i + 1].kind == "identifier":
        # Whitespace ends an identifier: `f . projection` is not a qualified name.
        if tokens[i - 1].end != tokens[i].start or tokens[i].end != tokens[i + 1].start:
            break
        result += "." + tokens[i + 1].text
        i += 2
    return result, i


def identifier_parts(tokens: list[Token], start: int) -> list[str]:
    """Name components; a dot inside an escaped identifier is not a separator."""
    name, end = identifier(tokens, start)
    return [tokens[i].text for i in range(start, end) if tokens[i].kind == "identifier"] if name else []


def doc_text(token: Token) -> str:
    return token.text[3:-2].strip()


def summary(markdown: str, limit: int = 240) -> str:
    paragraphs = re.split(r"\n\s*\n", markdown.strip())
    for paragraph in paragraphs:
        if paragraph.lstrip().startswith("#"):
            continue
        text = " ".join(paragraph.split())
        if text:
            return text if len(text) <= limit else text[:limit - 1].rstrip() + "…"
    return ""


def command_prefix(tokens: list[Token], start: int) -> tuple[int, str, str] | None:
    """Find a command after its doc comment, attributes and modifiers."""
    i, doc = start, ""
    if tokens[i].kind == "doc":
        doc = doc_text(tokens[i])
        i += 1
    while i < len(tokens):
        if tokens[i].text == "@" and i + 1 < len(tokens) and tokens[i + 1].text == "[":
            i += 2
            while i < len(tokens) and not (tokens[i].text == "]" and tokens[i].depth == 0):
                i += 1
            i += 1
        elif tokens[i].text in MODIFIERS:
            modifier = tokens[i].text
            i += 1
            if modifier == "scoped" and i < len(tokens) and tokens[i].text == "[":
                i += 1
                while i < len(tokens) and not (tokens[i].text == "]" and tokens[i].depth == 0):
                    i += 1
                i += 1
        else:
            break
    if i < len(tokens) and tokens[i].depth == 0 and tokens[i].text in COMMANDS:
        return i, tokens[i].text, doc
    return None


def source_attribution(source: str, path: str, source_base: str,
                       provenance: dict | None = None) -> dict:
    """Keep source notices and their scope; never infer an external holder.

    Ordinary leading comments supply the evidence. Lean imports and prose later
    in a proof do not identify the source's authors. The only fallback concerns
    original NYLL documentation and is explicitly labelled as a project default.
    """
    blocks, i = [], 0
    while i < len(source):
        while i < len(source) and (source[i].isspace() or source[i] == "\ufeff"):
            i += 1
        start = i
        if source.startswith("--", i):
            parts = []
            while source.startswith("--", i):
                end = source.find("\n", i)
                end = len(source) if end < 0 else end
                parts.append(source[i + 2:end].lstrip())
                i = end + 1
                while i < len(source) and source[i] in " \t":
                    i += 1
            text = "\n".join(parts)
        elif source.startswith("/-", i):
            is_doc = source.startswith(("/--", "/-!"), i)
            level, i = 1, i + 2
            while level and i < len(source):
                if source.startswith("/-", i):
                    level, i = level + 1, i + 2
                elif source.startswith("-/", i):
                    level, i = level - 1, i + 2
                else:
                    i += 1
            if level:
                raise SourceError(f"Unclosed attribution comment at character {start}")
            text = source[start + (3 if is_doc else 2):i - 2].strip()
        else:
            break
        if re.search(r"copyright|\bauthors?\b|licen[cs]e|attribution|\bnotice\b|"
                     r"upstream|adapt(?:ed|ation)|\bpi1\b|(?:copied|ported|derived)\s+from|"
                     r"original\s+(?:mathlib\s+)?source|based\s+on", text, re.IGNORECASE):
            blocks.append({"text": text, "line": source.count("\n", 0, start) + 1})
    header = "\n\n".join(block["text"] for block in blocks)
    external_path = any(part.lower() in {"pi1", "flt", "mathlib"} for part in Path(path).parts)
    external = external_path or bool(provenance and provenance.get("upstream_paths")) or bool(
        re.search(r"github\.com/(?:chrisflav/pi1|anthropics/fermats-last-theorem|"
                  r"leanprover-community/mathlib4)|\bupstream\b|\bpi1\b|\bAnthropic\b|"
                  r"(?:adapted|copied|derived|ported|based)\s+from|based\s+on|"
                  r"original\s+mathlib\s+source", header, re.IGNORECASE))
    notice_lines = list(dict.fromkeys(
        line.strip() for line in header.splitlines()
        if re.search(r"Copyright\s+(?:\(c\)|©|\d{4})|^\s*Authors?(?: of [^:]*)?:",
                     line, re.IGNORECASE)))
    # Existing source notices always take precedence, including notices that name
    # a non-NYLL author without an upstream URL. Absent external notices stay absent.
    default = None
    if not blocks and not external and (path.startswith("Nyll/") or path == "Nyll.lean"):
        default = "Original NYLL documentation: Copyright (c) 2026 Naganori Yamaguchi (project default)."
    return {
        "notices": blocks, "noticeLines": notice_lines, "externalSource": external,
        "defaultNotice": default,
        "missingNotice": bool(external and not blocks),
        "provenanceUrl": (f"{source_base}/Nyll/EtaleFundamentalGroups/Pi1/ATTRIBUTION.md"
                          if provenance is not None else ""),
    }


def pi1_provenance(root: Path) -> dict[str, dict]:
    """Read mapped source ownership, without treating source hashes as build evidence."""
    path = root / "Nyll/EtaleFundamentalGroups/Pi1/UPSTREAM.json"
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if data["schema"] != "nyll.pi1.provenance.v1":
            raise ValueError("Unsupported pi1 provenance schema")
        files = data["local_source_snapshot"]["files"]
        result = {entry["path"]: entry for entry in files}
        if len(result) != len(files):
            raise ValueError("Duplicate pi1 provenance path")
        return result
    except (ValueError, KeyError, TypeError) as error:
        raise SourceError(f"Invalid pi1 provenance manifest: {error}") from error


def parse_module(source: str, module: str, path: str, source_base: str,
                 provenance: dict | None = None) -> dict:
    """Extract explicit source entries without assuming elaboration succeeded."""
    tokens = lex(source)
    commands: list[tuple[int, int, str, str]] = []
    consumed = -1
    first_by_line: dict[int, int] = {}
    for i, token in enumerate(tokens):
        first_by_line.setdefault(token.line, i)
        if i <= consumed or token.depth != 0:
            continue
        if token.kind == "module_doc":
            commands.append((i, i, "module_doc", doc_text(token)))
            continue
        inline_wrapper = i > 0 and tokens[i - 1].text == "in" and tokens[i - 1].depth == 0
        if first_by_line[token.line] != i and not inline_wrapper:
            continue
        prefix = command_prefix(tokens, i)
        if prefix is None:
            if token.kind == "doc" and i + 1 < len(tokens) and tokens[i + 1].text == "#":
                commands.append((i, i, "comment_doc", ""))
            if token.column == 0 and token.text.startswith("#"):
                commands.append((i, i, "command", ""))
            continue
        keyword_at, kind, doc = prefix
        if kind == "deriving" and keyword_at + 1 < len(tokens) and tokens[keyword_at + 1].text != "instance":
            continue
        # Explicit declarations may have incidental indentation. Other commands
        # inside a proof (e.g. `open ... in`) must not truncate its source.
        if token.column != 0 and kind not in DECLARATIONS and not inline_wrapper:
            continue
        commands.append((i, keyword_at, kind, doc))
        consumed = keyword_at

    scopes: list[tuple[str, str]] = []
    contexts: list[tuple[int, dict]] = []
    pending_namespace: str | None = None
    pending_context: list[dict] = []
    docs, imports, declarations = [], [], []
    for ci, (start, key, kind, doc) in enumerate(commands):
        stop = commands[ci + 1][0] if ci + 1 < len(commands) else len(tokens)
        end = tokens[stop].start if stop < len(tokens) else len(source)
        command_source = source[tokens[start].start:end].rstrip()
        lexical_namespace = ".".join(name for scope_kind, name in scopes if scope_kind == "namespace")
        if kind == "with_weak_namespace":
            name, _ = identifier(tokens, key + 1)
            base = pending_namespace if pending_namespace is not None else lexical_namespace
            pending_namespace = (name[len("_root_."):] if name.startswith("_root_.") else
                                 "" if name == "_root_" else ".".join(x for x in (base, name) if x))
            pending_context.append({"kind": kind, "source": command_source, "line": tokens[key].line})
            continue
        if kind in {"open", "include", "omit", "set_option", "attribute"} and tokens[stop - 1].text == "in":
            pending_context.append({"kind": kind, "source": command_source, "line": tokens[key].line})
            continue
        declaration_namespace = pending_namespace if pending_namespace is not None else lexical_namespace
        declaration_context = list(pending_context)
        if pending_namespace is not None and kind in {"namespace", "section", "mutual"}:
            raise SourceError(f"Unsupported namespace-changing wrapper at line {tokens[key].line}")
        pending_namespace, pending_context = None, []
        if kind == "module_doc":
            docs.append(doc)
            continue
        if kind == "namespace":
            parts = identifier_parts(tokens, key + 1) if key + 1 < stop else []
            # Lean's addScopes/elabEnd use one scope per name component, not
            # one per namespace command (Lean/Elab/BuiltinCommand.lean).
            scopes.extend((kind, part) for part in parts)
            contexts.append((len(scopes), {"kind": kind, "source": command_source,
                                          "line": tokens[key].line}))
            continue
        if kind in {"section", "mutual"}:
            parts = identifier_parts(tokens, key + 1) if kind == "section" and key + 1 < stop else []
            scopes.extend((kind, part) for part in (parts or [""]))
            contexts.append((len(scopes), {"kind": kind, "source": command_source,
                                          "line": tokens[key].line}))
            continue
        if kind == "end":
            parts = identifier_parts(tokens, key + 1) if key + 1 < stop else []
            count = len(parts) or 1
            if count > len(scopes):
                raise SourceError(f"Unmatched scope end at line {tokens[key].line}")
            actual = [name for _, name in scopes[-count:]]
            if actual != (parts or [""]):
                raise SourceError(f"Scope end mismatch at line {tokens[key].line}: {parts!r} versus {actual!r}")
            remaining = len(scopes) - count
            contexts = [(level, item) for level, item in contexts if level <= remaining]
            del scopes[remaining:]
            continue
        if kind == "import":
            i = key + 1
            while i < stop:
                name, after = identifier(tokens, i)
                if name and name not in {"all", "meta"}:
                    imports.append(name)
                i = max(i + 1, after)
            continue
        if kind in {"universe", "universes", "variable", "variables", "open",
                    "include", "omit", "attribute", "set_option", "notation",
                    "infix", "infixl", "infixr", "prefix", "postfix"}:
            contexts.append((len(scopes), {"kind": kind, "source": command_source,
                                          "line": tokens[key].line}))
        if kind not in DECLARATIONS:
            continue
        name_at = key + 1
        effective_kind = kind
        if kind == "class" and name_at < stop and tokens[name_at].text == "inductive":
            name_at += 1
            effective_kind = "class inductive"
        if kind == "instance" and name_at < stop and tokens[name_at].text == "(":
            # A named instance can start with `(priority := ...)`.
            end_priority = name_at + 1
            while end_priority < stop and not (tokens[end_priority].text == ")" and
                                                tokens[end_priority].depth == 0):
                end_priority += 1
            if name_at + 1 < stop and tokens[name_at + 1].text == "priority":
                name_at = end_priority + 1
        name, after_name = identifier(tokens, name_at)
        if kind == "instance" and name in {"where"}:
            name = ""
        namespace = declaration_namespace
        display_name = (name[len("_root_."):] if name.startswith("_root_.") else
                        ".".join(x for x in (namespace, name) if x)) if name else "(anonymous instance)"
        line = tokens[key].line
        declaration_end = tokens[stop - 1].end if stop > start else tokens[key].end
        # Trailing ordinary comments belong to the module source, not this entry.
        declaration_source = source[tokens[start].start:declaration_end].rstrip()
        header_end = declaration_end
        statement_includes_body = True
        if kind not in {"structure", "class", "inductive"}:
            header_tokens = tokens[max(after_name, key + 1):stop]
            for position, token in enumerate(header_tokens):
                if token.depth == 0 and token.text in {":=", "where", "|"}:
                    # A return type is an arbitrary Lean term. For example,
                    # `: let x := value; conclusion` contains a top-level `:=`
                    # which is NOT the proof boundary. In such cases retain
                    # the complete written declaration, including its value.
                    # We deliberately do not guess a term grammar or inferred
                    # signature. Equation/where forms receive the same fallback.
                    ambiguous = token.text != ":=" or any(
                        t.kind == "identifier" and t.text in {
                            "let", "letI", "letI'", "have", "haveI", "haveI'",
                            "match", "fun", "do", "by", "if", "unless", "show",
                        } for t in header_tokens[:position]
                    )
                    if not ambiguous:
                        header_end = token.start
                        statement_includes_body = False
                    break
        statement = source[tokens[key].start:header_end].rstrip()
        entry = {
            "id": "d-" + hashlib.sha256(f"{module}:{line}:{display_name}".encode()).hexdigest()[:16],
            "name": display_name,
            "sourceName": name,
            "namespace": namespace,
            "kind": effective_kind,
            "line": line,
            "endLine": source.count("\n", 0, declaration_end) + 1,
            "doc": doc,
            "statement": statement,
            "statementIncludesBody": statement_includes_body,
            "source": declaration_source,
            "context": [item for _, item in contexts] + declaration_context,
            "sourceUrl": f"{source_base}/{quote(path, safe='/')}#L{line}",
            "hasSorry": any(t.kind == "identifier" and t.text == "sorry" for t in tokens[key:stop]),
        }
        declarations.append(entry)
        if kind == "instance" and any(t.text == "local" for t in tokens[start:key]):
            contexts.append((len(scopes), {"kind": "local instance", "source": declaration_source,
                                          "line": line}))
    return {"name": module, "path": path, "doc": "\n\n".join(docs),
            "imports": list(dict.fromkeys(imports)), "importedBy": [],
            "source": source, "sourceUrl": f"{source_base}/{quote(path, safe='/')}",
            "declarations": declarations, "indexKind": "source",
            "attribution": source_attribution(source, path, source_base, provenance)}


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def write_json(path: Path, data: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n", encoding="utf-8")


def build(root: Path, output: Path, repository: str, revision: str | None = None,
          site_url: str = SITE_URL) -> dict:
    root, output = root.resolve(), output.resolve()
    parsed_url = urlsplit(site_url)
    if (parsed_url.scheme not in {"http", "https"} or not parsed_url.hostname or
            parsed_url.username is not None or parsed_url.password is not None or
            parsed_url.query or parsed_url.fragment):
        raise SourceError("Site URL must be an absolute HTTP(S) homepage URL without credentials, query, or fragment")
    site_url = site_url.rstrip("/") + "/"
    source_root = root / "Nyll"
    if not source_root.is_dir():
        raise SourceError(f"Missing Lean source directory: {source_root}")
    if output == root or output.is_relative_to(source_root):
        raise SourceError("Generated site output must be separate from Lean source and repository root")
    commit = revision or git(root, "rev-parse", "HEAD")
    if not re.fullmatch(r"[0-9a-fA-F]{40}", commit):
        raise SourceError("Source revision must be a full 40-character Git commit")
    source_base = f"{repository.rstrip('/')}/blob/{commit}"
    try:
        committed_at = git(root, "show", "-s", "--format=%cI", commit)
    except subprocess.CalledProcessError:
        committed_at = ""
    files = sorted(source_root.rglob("*.lean"))
    if (root / "Nyll.lean").is_file():
        files.insert(0, root / "Nyll.lean")
    modules: dict[str, dict] = {}
    search = []
    libraries: dict[str, list[dict]] = defaultdict(list)
    declaration_ids: set[str] = set()
    provenance = pi1_provenance(root)
    for number, path in enumerate(files, 1):
        if path.is_symlink():
            raise SourceError(f"Refusing a symlinked Lean source: {path}")
        relative = path.relative_to(root).as_posix()
        name = relative.removesuffix(".lean").replace("/", ".")
        try:
            module = parse_module(path.read_text(encoding="utf-8"), name, relative, source_base,
                                  provenance.get(relative))
        except SourceError as error:
            raise SourceError(f"{relative}: {error}") from error
        parts = name.split(".")
        library = parts[1] if len(parts) > 1 and parts[1] != "All" else ""
        module["library"] = library
        module["declarationCount"] = len(module["declarations"])
        modules[name] = module
        if library:
            libraries[library].append(module)
        for declaration in module["declarations"]:
            if declaration["id"] in declaration_ids:
                raise SourceError(f"Duplicate source entry: {name} line {declaration['line']}")
            declaration_ids.add(declaration["id"])
            search.append({"type": "declaration", "id": declaration["id"],
                           "name": declaration["name"], "kind": declaration["kind"],
                           "module": name, "library": library, "line": declaration["line"],
                           "doc": summary(declaration["doc"], 160),
                           "hasSorry": declaration["hasSorry"]})
        if number % 1000 == 0:
            print(f"Indexed {number}/{len(files)} modules", file=sys.stderr)
    for module in modules.values():
        for imported in module["imports"]:
            if imported.startswith("Nyll.") or imported == "Nyll":
                if imported not in modules:
                    raise SourceError(f"{module['name']} imports missing local module {imported}")
                modules[imported]["importedBy"].append(module["name"])
    library_rows = []
    for library, members in sorted(libraries.items()):
        aggregate = modules.get(f"Nyll.{library}.All") or modules.get(f"Nyll.{library}") or members[0]
        title = re.search(r"^#\s+(.+)$", aggregate["doc"], re.MULTILINE)
        title_text = title.group(1).replace("`", "") if title else ""
        library_rows.append({"id": library, "name": title_text if title_text.lower() not in {"", "all"} else library,
                             "rootModule": aggregate["name"], "doc": summary(aggregate["doc"]),
                             "moduleCount": len(members),
                             "declarationCount": sum(m["declarationCount"] for m in members)})
    manifest = {
        "schemaVersion": 1, "indexKind": "source",
        "title": "NYLL", "description": "A library of formalized mathematics in Lean 4.",
        "source": {"repo": repository.rstrip("/"), "commit": commit, "commitShort": commit[:8],
                   "committedAt": committed_at},
        "searchUrl": f"data/{commit}/search.json",
        "counts": {"libraries": len(libraries), "modules": len(modules), "declarations": len(search)},
        "libraries": library_rows,
        "modules": [{"name": m["name"], "library": m["library"], "path": m["path"],
                     "doc": summary(m["doc"]), "declarationCount": m["declarationCount"],
                     "dataUrl": f"data/{commit}/modules/{m['name']}.json"} for m in modules.values()],
    }
    output.mkdir(parents=True, exist_ok=True)
    if (root / "site").is_dir():
        shutil.copytree(root / "site", output, dirs_exist_ok=True,
                        ignore=shutil.ignore_patterns("guides"))
    # A deployment contains one immutable revision. Remove only a previously
    # generated data tree, after all source validation has succeeded. This also
    # prevents deleted modules and older revisions from accumulating on Pages.
    data_directory = output / "data"
    if data_directory.exists():
        if data_directory.is_symlink() or data_directory.resolve().parent != output:
            raise SourceError("Refusing to replace a redirected generated data directory")
        previous_manifest = data_directory / "manifest.json"
        try:
            previous = json.loads(previous_manifest.read_text(encoding="utf-8"))
        except (OSError, ValueError) as error:
            raise SourceError("Refusing to replace data without a valid NYLL generated manifest") from error
        if previous.get("schemaVersion") != 1 or previous.get("indexKind") != "source":
            raise SourceError("Refusing to replace data without a NYLL source-index manifest")
        shutil.rmtree(data_directory)
    for module in modules.values():
        write_json(output / "data" / commit / "modules" / (module["name"] + ".json"), module)
    write_json(output / "data" / commit / "search.json", search)
    write_json(output / "data" / "manifest.json", manifest)
    # The same shell now has a crawlable page for every library and module.
    # Statements and documentation are in the initial HTML; interactive proof
    # expansion still uses the immutable JSON rather than duplicating all source.
    try:
        source_urls = write_pages(output, (root / "site" / "index.html").read_text(encoding="utf-8"),
                                  manifest, modules, site_url)
    except (ValueError, OSError) as error:
        raise SourceError(str(error)) from error
    write_sitemap(output, "sitemap-source.xml", source_urls, site_url)
    (output / ".nojekyll").touch()
    print(json.dumps(manifest["counts"]))
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--repository", default="https://github.com/n-yamaguchi-0729/NYLL")
    parser.add_argument("--site-url", default=SITE_URL, help="Absolute published homepage URL for sitemap.xml")
    parser.add_argument("--revision", help="Exact source commit; defaults to HEAD")
    args = parser.parse_args()
    try:
        build(args.root, args.output or args.root / "_site", args.repository, args.revision, args.site_url)
    except (SourceError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Site build failed: {error}\n")


if __name__ == "__main__":
    main()
