# Collatz–Runyan Framework v2.5 — Coefficient Growth, Asymptotic Rigidity and Parity Drift Constraints

## Formal verification

- 418/418 inventoried theorem and lemma declarations passed across 43/43 mathematical Lean modules.
- Seven new modules containing 113 additional declarations; all seven authenticated source fingerprints match.
- 43/43 source identities and both versioned checksum manifests verified.
- Lean 4 and Mathlib v4.19.0; fresh dependency-aware compilation and axiom inspection of imported compiled declarations.
- Zero reported sorryAx dependencies; only propext, Classical.choice and Quot.sound.
- The original 305 declarations and their axiom dependencies were reconciled with v2.4.
- Two successful automated audit runs, including the merged main-branch source.

## Research extensions

The seven new modules investigate sparse and coalescent coefficient bounds, family coalescence and correction products, conditional prefix-maximum coefficient growth of exponent 29/32, rational asymptotic restrictions for injective shortcut Collatz trajectories, certified parity deficits, and the obstruction to uniform fixed-block contraction.

The 29/32 result assumes an injective shortcut orbit with starting integer not divisible by three. The rational asymptotic theorem implies a real logarithmic parity-frequency liminf restriction analytically; that formulation is not separately counted as a Lean theorem. Orbit repetition is not necessarily convergence to the known cycle.

## Reproducibility

- Audited source commit: 3e036b21968b04e5b5209bc4d8b6f29cc3bdcdbd
- Main-branch audit: https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45865785715
- Pre-merge audit: https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45860248412
- Full original verification archive: https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45865785715/artifacts/15139469972
- Archive SHA-256: a42d6037018b06b11c08d952442dde593bdab81a1dc18659fa532a4f5dc0b575
- Permanent declaration inventory and source identity record: in the v2.5 audit directory.
- Previous version-specific Zenodo DOI: https://doi.org/10.5281/zenodo.24549264
- Concept DOI: https://doi.org/10.5281/zenodo.24517627

## Scientific limitations

The Collatz conjecture remains unresolved. The formal results establish encoded propositions under their explicit hypotheses, not the entire mathematical or physical framework. Declaration counts include supporting and repeated results, not necessarily distinct discoveries. Automated formal verification is not independent human peer review, and historical novelty has not been established.

Next mathematical investigation: Parity Residue Rigidity.
