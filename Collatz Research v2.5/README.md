# Collatz–Runyan Framework — v2.5

**Status:** audited on main; release prepared. The [main-branch automated audit](https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45865785715) completed November 26, 2026 at 17:22 UTC, with 418/418 declarations and 43/43 mathematical modules passed. The seven new modules contain 113 declarations. All 43 source identities and both versioned manifests passed, and the original 305 declarations and their axiom dependencies matched the published baseline. The only reported foundational axiom types were `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` dependency was reported. The audit-branch [run](https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45860248412) also passed.

## Source inventory

| Module | Declarations |
| --- | ---: |
| `SparseCoefficientRigidity` | 16 |
| `CoalescentCoefficientRigidity` | 26 |
| `FamilyCoalescenceRigidity` | 20 |
| `FamilyCorrectionProduct` | 20 |
| `FamilyCoefficientRigidity` | 13 |
| `AsymptoticCoefficientRigidity` | 12 |
| `ParityDriftConflict` | 6 |

## Mathematical scope

Write `T` for the shortcut Collatz map and `C_k(n) = 3^{a_k(n)}/2^k`, where `a_k(n)` counts odd transitions.

- `FamilyCoefficientRigidity.prefix_coefficient_growth`: assuming `n % 3 ≠ 0` and injectivity of the shortcut orbit, for each natural `k` there is `j ≤ k` with `k^29 ≤ (C_j(n) n)^32` (rational arithmetic).
- `AsymptoticCoefficientRigidity.eventual_scaled_coefficient_growth`: for an injective orbit, every rational `q > 1` and rational `D` admit an `N` such that `D < C_k(n) q^k` for every `k ≥ N`.
- `ParityDriftConflict.eventual_above_certified_frequency`: given injectivity, natural `p,b`, `b > 0`, rational `q > 1`, and `3^p q^b ≤ 2^b`, eventually `p k < b a_k(n)`. In particular `5 k < 8 a_k(n)` eventually.
- `ParityDriftConflict.certified_deficit_forces_repeat`: under the same numerical certificate, arbitrarily late deficient prefixes imply two distinct indices with equal orbit values.
- `ParityDriftConflict.no_uniform_block_contraction`: for each positive natural block length `L` and cutoff `M`, there exists `n ≥ M` with `C_L(n) > 1`.

The real-valued logarithmic liminf restriction is an analytical consequence of the rational theorem, not a separately claimed Lean declaration. These conditional results do not establish the Collatz conjecture. Eventual periodicity is not necessarily arrival at the known cycle. The proposed physical theory is not established by this formal collection.

## Reproduce

The complete audit uses the existing Lean and Mathlib v4.19.0 projects. From the repository root, on Ubuntu with Git, Python 3, Elan and full baseline Git history:

```sh
python3 "Collatz Research v2.5/audit/verify-v25.py"
```

GitHub Actions runs the same script, archives per-module compile and axiom logs, dependency orders, source hashes and the full declaration inventory. The audit checks the exact historical source commit and the published baseline inventory; the new sources are compiled in dependency order and audited via imports of fresh `.olean` files.

`SHA256SUMS.txt` and `audit/source-inventory.json` describe the seven authenticated input sources. They are not new compilation evidence. The fresh main-branch run passed at commit `3e036b21968b04e5b5209bc4d8b6f29cc3bdcdbd`. Its [declaration inventory](audit/declaration-inventory.json) and [source-check record](audit/source-checks.json) are preserved byte-for-byte. See [verification provenance](audit/verification-provenance.json) for run, job, artifact and SHA-256 identifiers. The [full original audit artifact](https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45865785715/artifacts/15139469972) contains 99 files; download and retain it before GitHub's retention period expires. Counts include supporting and repeated mathematical statements, not necessarily distinct discoveries. Automated verification is not independent human peer review; historical novelty is not established.

## Publication

The v2.5 technical audit is complete. See [release notes](RELEASE-NOTES.md). The published v2.4 version-specific DOI remains authoritative for that archived version; a v2.5 version-specific DOI must be assigned separately. No v2.5 DOI is asserted here.

- v2.4: https://doi.org/10.5281/zenodo.24549264
- Prior audit: https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45754171971
- Next mathematical investigation: Parity Residue Rigidity, after consolidation.
