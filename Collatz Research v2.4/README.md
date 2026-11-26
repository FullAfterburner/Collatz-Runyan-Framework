# Collatz Research v2.4

This supplement preserves 19 author-compiled research modules (168 theorem declarations). Together with the previously audited 137 declarations across 17 modules, the combined inventory is 305 declarations across 36 modules. Counts include supporting and repeated results, not distinct discoveries. A fresh [GitHub Actions audit](https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45754171971) verified all 305 declarations and 36 modules at commit `61654302e084a2fa2fdcf50321a8fa64a19994ad`, including 19/19 source checksum checks and no unexpected axiom dependencies. The Collatz conjecture remains open; no claim of historical novelty or peer review is made.

| Module | Declarations |
| --- | ---: |
| DenominatorRigidity | 7 |
| PrimePowerRigidity | 8 |
| PrimePowerCorrections | 7 |
| ExceptionalGapRigidity | 9 |
| ModularWeightRigidity | 11 |
| ZeroSumRigidity | 8 |
| CycleBoundConflict | 8 |
| ForcedZeroSum | 8 |
| IntegralityRigidity | 10 |
| AdaptiveResidueRigidity | 8 |
| GlobalRunRigidity | 9 |
| CoupledRunRigidity | 9 |
| StabilizedCoreRigidity | 8 |
| LocalDivisorRigidity | 8 |
| CongruencePropagation | 8 |
| UniversalDescentRigidity | 8 |
| LogarithmicDeficitRigidity | 13 |
| CriticalParityRigidity | 10 |
| BoundedCoefficientRigidity | 11 |
| Total | 168 |

## Reproduce

Use the pinned Lean/Mathlib v4.19.0 project in `Collatz Research v2.3` to compile these standalone files. The [full workflow](../.github/workflows/collatz-v24-full-audit.yml) stages them in that project, regenerates individual axiom checks, compiles every inventoried file and checks the SHA-256 manifest. [Audit inventory](audit/declaration-inventory.json) is extracted from the successful job log and preserved here for long-term access. The original [GitHub artifact](https://github.com/FullAfterburner/Collatz-Runyan-Framework/actions/runs/45754171971/artifacts/15087395952) contains the complete logs and machine-generated inventory while available.

## Scope

The results include conditional cycle exclusions, modular consistency limitations, distinct-visit correction bounds and necessary coefficient growth for injective shortcut orbits. They do not prove universal descent or exclude all nontrivial cycles or divergence. The count is of uniquely named declarations, not unique mathematical propositions. No peer review or historical novelty is claimed.
