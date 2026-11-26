# Collatz–Runyan Framework v2.6 — audit candidate

**Checkpoint:** November 26, 2026. **Status:** source checkpoint, fresh CI audit pending. Not a proof of the Collatz conjecture.

This supplement adds 19 mathematical Lean files with 142 inventoried theorem/lemma declarations to the v2.5 baseline (43 modules, 418 audited declarations). The proposed cumulative inventory is 62 modules and 560 declarations; these totals are not a new successful CI result. All 19 source bytes match the locally recorded SHA-256 fingerprints. The author reported local compilation and matching working/backup hashes. Not every earlier local declaration has an individually preserved audit log; the new audit must establish those results independently.

## Scope

- Binary conjugation is a defined two-sector symmetry, not the standard signed Collatz map or a physical correspondence.
- Rational spectral decomposition, two-place absolute value/2-adic norm duality, and exact correction-product identities.
- Conditional shortcut-to-accelerated iteration bridge and non-descent restrictions.
- Necessary cycle budget, integer exclusion, minimum bound, affine divisibility and exact valuation residue conditions.
- One cyclic rotation of a finite positive valuation word: with positive discrepancy and an integral affine candidate, the next integer candidate can be constructed. Full periodic constructive equivalence is a future objective, not a verified result here.

## New source inventory

| Module | Declarations |
|---|---:|
| BinaryAdelicDuality | 8 |
| BinaryConjugation | 19 |
| BinaryDynamicalCompatibility | 9 |
| BinarySpectralIteration | 6 |
| BinarySpectralSymmetry | 12 |
| CollatzAdelicCompatibility | 8 |
| CollatzAdelicDrift | 3 |
| CollatzCorrectionBounds | 6 |
| CollatzCycleAdmissibility | 5 |
| CollatzCycleAffineRigidity | 6 |
| CollatzCycleBudget | 3 |
| CollatzCycleExclusionCertificate | 2 |
| CollatzCycleMinimumRigidity | 3 |
| CollatzCyclicRotationRigidity | 10 |
| CollatzIterationBridge | 8 |
| ConjugateCoefficientRigidity | 12 |
| ConjugateCycleRigidity | 9 |
| IntegratedNonDescentRigidity | 3 |
| TwoAdicSectorDecomposition | 10 |
| Total | 142 |

See SHA256SUMS.txt and audit/source-inventory.json for the exact source fingerprints. The audit compiles v2.5 dependencies and v2.6 modules together from fresh source, checks their SHA-256 identities, and audits individual declarations. Run from repository root: `python3 "Collatz Research v2.6/audit/verify-v26.py"`. The new workflow additionally reruns the v2.5 full audit.

Nontrivial positive cycle exclusion, divergence exclusion and universal descent remain unresolved. No claim of historical novelty or independent peer review is made. The next proposed theorem is constructive cycle equivalence; no new theorem development is included in this checkpoint.
