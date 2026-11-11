#!/usr/bin/env python3
"""Compatibility entry point; implementation: tools/validation/check_lean_rules.py.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from pathlib import Path as _EntryPath
_entry_impl = _EntryPath(__file__).resolve().parent / "validation/check_lean_rules.py"
# Execute in this module namespace so imports and monkeypatches retain identity.
__file__ = str(_entry_impl)
exec(compile(_entry_impl.read_bytes(), __file__, "exec"), globals(), globals())
