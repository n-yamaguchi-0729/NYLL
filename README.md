# NYLL

The public development home for a growing collection of Lean 4 libraries.

NYLL brings together all of these libraries, including work in progress. As parts
are completed, they are extracted and published as standalone libraries in their
own repositories. The full collection continues to be developed here.

[Browse the library](https://n-yamaguchi-0729.github.io/NYLL/) · [Source](https://github.com/n-yamaguchi-0729/NYLL)

Import the whole library with `import Nyll`, or a specific module such as
`import Nyll.EtaleFundamentalGroups.All`.

## Published standalone libraries

The repositories below contain work extracted from NYLL. Follow these links for
each library's scope, documentation, and source.

| Library | Description |
| --- | --- |
| [Pro-C Groups](https://github.com/n-yamaguchi-0729/ProCGroups) | Profinite and pro-C groups, free pro-C groups, and completed group algebras. |
| [Class Field Theory](https://github.com/n-yamaguchi-0729/ClassFieldTheory) | Local and global class field theory, reciprocity, and ramification. |
| [Sawin's Totally Real Towers](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers) | Sawin's totally real tower theorem and related results of Martinet and Shafarevich. |
| [Étale Fundamental Groups and Cohomology](https://github.com/n-yamaguchi-0729/EtaleFundamentalGroupsAndCohomology) | Étale fundamental groups and étale cohomology. |
| [Jacobian Varieties](https://github.com/n-yamaguchi-0729/JacobianVarieties) | Algebraic curves, Picard groups, and Jacobian varieties. |
| [Research Papers](https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization) | Formalizations of research papers. |
| [Anabelian Geometry](https://github.com/n-yamaguchi-0729/AnabelianGeometry) | A library under development toward the formalization of Grothendieck's anabelian conjecture. |

## AI-written code and verification

All original code developed for NYLL is written by OpenAI Codex. The project maintainer sets the mathematical goals and scope and directs the development.

Lean kernel checking validates formal proofs against the encoded statements, definitions, and assumptions. Whether those statements faithfully represent the original mathematics requires separate review. NYLL includes work in progress and code that has not yet been checked by Lean; publication here does not imply that every formalization is complete or verified.

Copyright, authorship, and license notices for upstream and adapted code are preserved in the relevant source files.

## License and attribution

NYLL's original code and documentation are Copyright (c) 2026 Naganori Yamaguchi
and released under [Apache-2.0](LICENSE), unless a file states otherwise.

External and adapted material retains its source-specific copyright, authorship,
license, and attribution notices. An absent upstream notice does not transfer
ownership to NYLL. The [pi1 attribution record](Nyll/EtaleFundamentalGroups/Pi1/ATTRIBUTION.md)
and [pinned source manifest](Nyll/EtaleFundamentalGroups/Pi1/UPSTREAM.json) distinguish
upstream adaptations from NYLL additions. Anthropic FLT, mathlib, and other external
source notices remain in their corresponding files and directories.
