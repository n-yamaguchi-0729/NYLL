# Published library guides

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The seven JSON files contain curated mathematical explanations and bibliographic
references. Each selected result points to exact declaration names in a published
standalone repository. The generator reads source from Git objects, checks its
publication manifest, and includes the declaration, its local Lean context, and
immutable links to the standalone repository and its originating NYLL commit.
It does not execute Lean or claim to replace kernel verification.

Library overviews explain the mathematical problem and what the library achieves
in connected prose. Include necessary qualifications there without a separate
scope section. An entry opens with its short `summary`, followed by `discussion`
explaining its significance and a little historical context. Avoid restating the
summary. The longer `history` field remains editorial source material, without a
separate displayed section. References must support the displayed explanation.

Guide typography uses the role-based variables in `site/assets/site.css`, shared
with the homepage and source browser. Keep the homepage's appearance and align
guide content with its left edge at every breakpoint. Pages without the module
tree share the same right edge; do not center entry and overview pages separately.
The homepage hero remains a larger display heading; guides use the ordinary page
title style shared with library pages in the source browser.

The Pages workflow rebuilds on NYLL pushes, manual runs, and daily at 04:23 UTC.
It fetches the current published revisions and refreshes Lean excerpts and links.
The editorial selection and historical prose are maintained here; new results
are added deliberately, rather than automatically inventing explanations.

Select mathematically substantial proved results with useful conclusions.
Do not make individual pages for a definition, a notation, a routine calculation,
or a small step of a proof; explain necessary definitions within a result's page.
A constructed equivalence or isomorphism can be a substantial result even when
Lean expresses it as a definition. Its inverse and proof obligations must actually
be supplied. Classify pages by their mathematical content, not the command token.

There is no minimum or target number of pages per library. An empty selection is
preferable to padding it with minor results. Keep unfinished local prototypes out
of the selection, and state the precise hypotheses and scope of partial theorems.

`review-lock.json` records the reviewed declarations and their transitive NYLL
source dependencies, together with the dependency manifest and Lean toolchain.
Changes to these inputs stop deployment pending review, including proof changes
inside the dependency closure. Unrelated published changes can refresh the source
revision and links automatically. This conservative check detects changed inputs;
it does not prove the correctness of the mathematical prose. A failed build leaves
the existing site online.

After reviewing the changed source, assumptions, explanations, and references:

```sh
python3 tools/build_guides.py --output tmp/guide-preview \
  --sources tmp/published-guide-sources --fetch --write-lock
python3 -m unittest discover -s tools/tests
```

Commit the updated prose and review lock together. Never run `--write-lock` in
unattended CI. To reproduce the complete site, first run `tools/build_site.py`
into the same output directory and then run `tools/build_guides.py` without
`--write-lock`. All generated files belong in a task-specific `tmp/` directory
locally. The deployment workflow uses its disposable `_site` directory.

References are collected on each library overview, not repeated on individual
result pages. No BibTeX files are generated.
