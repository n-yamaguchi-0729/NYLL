# NYLL

Lean 4 libraries for number theory and arithmetic geometry.

The official NYLL repository publishes completed, verified modules together with
their dependencies. Further development and unfinished mathematical goals are
maintained separately in the private development workspace. The scope of each
published result is given by its precise Lean statement and assumptions.

[Browse the library](https://n-yamaguchi-0729.github.io/NYLL/) · [Source](https://github.com/n-yamaguchi-0729/NYLL)

Import the whole library with `import Nyll`, or a specific module such as
`import Nyll.EtaleFundamentalGroups.All`.

## Using the library

Use the Lean version in [lean-toolchain](lean-toolchain) and the dependency
revisions in [lake-manifest.json](lake-manifest.json). From the repository root,
obtain the pinned Mathlib cache with `lake --wfail exe cache get` and run
`lake --wfail build +Nyll`, or build only the module needed for your work.

The official repository contains source code. Private proof-cache distribution
and development records are maintained separately.

## Published standalone libraries

These repositories contain their named library and its actual NYLL import
dependencies. Their READMEs describe the included results and assumptions.

| Library | Description |
| --- | --- |
| [Pro-C Groups](https://github.com/n-yamaguchi-0729/ProCGroups) | Profinite and pro-C groups, free pro-C groups, and completed group algebras. |
| [Class Field Theory](https://github.com/n-yamaguchi-0729/ClassFieldTheory) | Local fields, number fields and global function fields; reciprocity, norm subgroups and class fields. |
| [Sawin's Totally Real Towers](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers) | Sawin's totally real tower theorem and related results of Martinet and Shafarevich. |
| [Étale Fundamental Groups and Cohomology](https://github.com/n-yamaguchi-0729/EtaleFundamentalGroupsAndCohomology) | Finite étale covers, fundamental groups, Galois categories and proved cohomological comparisons. |
| [Jacobian Varieties](https://github.com/n-yamaguchi-0729/JacobianVarieties) | Picard and Jacobian constructions, including generalized-Jacobian modulus existence and equivariant Abel factorization over arbitrary fields. |
| [Research Papers](https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization) | Results on ab-faithful Galois actions and solvable coverings. |
| [Anabelian Geometry](https://github.com/n-yamaguchi-0729/AnabelianGeometry) | Genus-zero weak reconstruction over number fields and geometric hyperbolic slimness. Weak reconstruction proves existence of a curve isomorphism; realizing the supplied group isomorphism and uniqueness in that correspondence remain unfinished. |

NYLL also contains the shared foundations in scheme theory, valued fields,
Galois cohomology, algebraic curves and abelian varieties. A proved component
does not imply completion of a larger mathematical program: the general
Néron–Ogg–Shafarevich criterion, the general proper/Henselian specialization
equivalence, the full Lefschetz trace formula, further
generalized-Jacobian comparisons and the general anabelian conjectures remain
separate goals.

## AI-written code and verification

All original code developed for NYLL is written by OpenAI Codex. The project
maintainer sets the mathematical goals and scope and directs the development.

Published source is checked by Lean with errors and warnings treated as failures.
The Lean workflow records verification for its exact commit. Kernel checking
validates formal proofs against their encoded statements, definitions and
assumptions; fidelity to the intended mathematics requires separate review.

Copyright, authorship and license notices for upstream and adapted code are
preserved in the relevant source files.

## License and attribution

NYLL's original code and documentation are Copyright (c) 2026 Naganori Yamaguchi
and released under [Apache-2.0](LICENSE), unless a file states otherwise.

External and adapted material retains its source-specific copyright, authorship,
license and attribution notices. An absent upstream notice does not transfer
ownership to NYLL. The [pi1 attribution record](Nyll/EtaleFundamentalGroups/Pi1/ATTRIBUTION.md)
and [pinned source manifest](Nyll/EtaleFundamentalGroups/Pi1/UPSTREAM.json) distinguish
upstream adaptations from NYLL additions. Anthropic FLT, Mathlib and other external
source notices remain in their corresponding files and directories.
