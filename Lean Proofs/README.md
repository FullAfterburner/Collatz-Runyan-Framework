# Collatz–Runyan Lean Proofs — v2.2 formalization

**Build status: successful author-run local compilation, documented in the [kernel build log](kernel_verification.txt).** The [axiom audit](axiom_verification.txt) lists only `propext`, `Classical.choice` and `Quot.sound` for seven selected statements, with no `sorryAx` dependencies. This is a partial formalization of the mathematical core, not a formal proof of the entire framework. No independent fresh build is claimed by this documentation update.

Source manuscript: [Theorems, Supporting Lemmas and Complete Proofs (v2.1L)](../Proofs/Collatz_Runyan_Theorems_Lemmas_Proofs_v21L.pdf).

## Scope

| Module | Formal statements | Not yet formalized |
| --- | --- | --- |
| Arithmetic | Rational inverse maps, affine commutator, conditional Diophantine descent inequality, integer Pell examples | 2-adic representation and parity iteration identity |
| BranchAlgebra | Matrix-unit multiplication from equal-length cancellation | Haar measure, isometries, adjoints, independence, full algebra isomorphism |
| Lorentzian | Polynomial determinant and boost identity | Hermitian space dimension/signature theorem and full Lorentz group |
| Intersection | Zero complementary pairing for arbitrary integer vectors supported on four admissible triples | Radical independence, Lagrangian/calibration constraints, topology-to-coordinate identification |
| Pending | — | Circle orbit and Gromov–Hausdorff limit, quantum oscillator sums and Casimir limit |

In particular, the finite intersection result does not itself prove the full special Lagrangian theorem. No physical theory, Collatz convergence, or emergent spacetime is proved by this project.

## Build locally

Install Lean 4 using the [official installation instructions](https://lean-lang.org/install/). From the repository root:

```sh
cd "Lean Proofs"
lake update
lake exe cache get
lake build
```

The Lean and Mathlib versions are pinned to v4.19.0. The first build downloads dependencies. The repository includes the generated dependency manifest; preserve it for reproducibility. Open the folder in VS Code with the Lean 4 extension for interactive proof checking.

Check that the build exits successfully; inspect all diagnostics. To examine theorem dependencies in a Lean file, use for example:

```lean
import CollatzRunyan
#print axioms CollatzRunyan.supported_pairing_zero
#print axioms CollatzRunyan.affine_commutator
```

The archived compilation and the seven-statement audit are separate checks. Reproduce the audit with `lake env lean Verification.lean`. The audit is not a substitute for kernel type-checking and does not imply that standard Mathlib foundations use no axioms.

Evidence: [verification source](Verification.lean), [kernel log](kernel_verification.txt), [build log](build_verification.txt), [axiom log](axiom_verification.txt), [dependency manifest](lake-manifest.json).

## Verification roadmap

1. Reproduce the recorded build independently and audit any remaining declarations.
2. Formalize parity cylinders and branch isometries.
3. Formalize the exact cycle period and metric limit.
4. Formalize Fourier oscillator sums and the renormalized limit.
5. Prove the arithmetic radical independence and connect differential-form constraints to the integral homology pairing.

Keep the PDF, computational audits and Lean statements versioned separately. A successful build certifies only the statements actually expressed in Lean, under their explicit hypotheses.
