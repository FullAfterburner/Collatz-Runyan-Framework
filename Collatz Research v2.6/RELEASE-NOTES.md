# Collatz–Runyan Framework v2.6 — Binary Conjugation, Adelic Compatibility, and Cyclic Rotation Rigidity

Published November 26, 2026 (UTC). [GitHub release](https://github.com/FullAfterburner/Collatz-Runyan-Framework/releases/tag/v2.6).

## Verification

- 19 additional mathematical modules and 142 inventoried theorem/lemma declarations.
- Cumulative distinct inventory: 62 modules and 560 declarations (v2.5 baseline: 43/418; combined v2.5/v2.6 audit: 26/255, including the overlapping seven v2.5 modules and 113 declarations).
- Successful main-branch automated audit at `cd21b9c77d192bb3b016b95514b3916637d2ddc2`: https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45911485057
- Source hashes and axiom checks enforced by the audit scripts. Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` dependencies permitted.
- [Audit provenance](audit/verification-provenance.json), [source inventory](audit/source-inventory.json), [checksums](SHA256SUMS.txt).

## Research scope

Binary conjugation and rational spectral symmetry, 2-adic and adelic arithmetic, accelerated iteration correspondence under supplied factorizations, non-descent constraints, cycle budget and minimum restrictions, affine divisibility and exact valuation admissibility, and constructive one-step cyclic rotation.

The last result constructs a successor candidate under supplied arithmetic hypotheses; full periodic constructive equivalence is a future objective. Universal descent, divergence exclusion, and nontrivial positive cycle exclusion remain unresolved. No physical correspondence or historical novelty is established. Automated verification is not independent human peer review; counts include supporting and repeated statements.

## Archival citation

Version-specific Zenodo DOI: [10.5281/zenodo.24573216](https://doi.org/10.5281/zenodo.24573216) (publication confirmed in the author's GitHub integration dashboard). Earlier releases and audit history are preserved. The published v2.6 tag is unchanged; subsequent documentation and citation corrections are on main.
