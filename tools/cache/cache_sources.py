"""Read NYLL import declarations without relying on local audit files.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""

# Keep historical flat module imports and CLI entry points compatible.
import sys as _tool_sys
from pathlib import Path as _ToolPath
_tool_sys.path.insert(0, str(_ToolPath(__file__).resolve().parents[1]))
import re

TOKEN = re.compile(r'/\-|--|"|\'(?:\\.|[^\'\\\n])\'')
BLOCK = re.compile(r'/\-|\-/')
STRING = re.compile(r'"(?:\\.|[^"\\])*"', re.S)


def strip_comments_strings(source):
    """Preserve every newline; remove nested comments and literal contents."""
    chunks = []
    cursor = 0
    while True:
        match = TOKEN.search(source, cursor)
        if match is None:
            chunks.append(source[cursor:])
            return ''.join(chunks)
        start = match.start()
        chunks.append(source[cursor:start])
        token = match.group()
        if token == '/-':
            nesting = 1
            end = match.end()
            for boundary in BLOCK.finditer(source, end):
                nesting += 1 if boundary.group() == '/-' else -1
                end = boundary.end()
                if nesting == 0:
                    break
            if nesting:
                raise ValueError('Unterminated block comment')
        elif token == '--':
            end = source.find('\n', match.end())
            if end < 0:
                end = len(source)
        elif token == '"':
            literal = STRING.match(source, start)
            if literal is None:
                raise ValueError('Unterminated string literal')
            end = literal.end()
        else:
            end = match.end()
        chunks.append(' ' + '\n' * source[start:end].count('\n'))
        cursor = end


def parse_imports(source):
    result = []
    clean = strip_comments_strings(source)
    for match in re.finditer(
            r"(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?"
            r"([A-Za-z_][\w.']*(?:[ \t]+[A-Za-z_][\w.']*)*)", clean):
        line_number = clean.count('\n', 0, match.start()) + 1
        for target in match.group(1).split():
            if target == 'Nyll' or target.startswith('Nyll.'):
                result.append((target, line_number))
    return result
