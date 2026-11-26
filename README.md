# The Collatz–Runyan Arithmetic Framework

## Arithmetic Foundations, Relativistic Geometry, Quantum Gravity, Modular Supergravity and Emergent String Dynamics

**Author:** Jake Thomas Runyan  
**Research Edition:** v2.3 — Formal Collatz Descent, Parity Rigidity and Cycle Research Edition (supplementing v2.2)  
**Updated:** November 25, 2026  
**Status:** Independent mathematical and theoretical physics research programme; selected statements machine-checked in Lean 4; broader results remain subject to independent review.

https://doi.org/10.5281/zenodo.24517681

## v2.3 — Formal Collatz Descent, Parity Rigidity and Cycle Research

The [v2.3 research supplement](Collatz%20Research%20v2.3/README.md) adds 13 standalone Lean 4 research modules and archived author-run audits of 89 selected declarations. The original v2.2 Lean project and its seven-statement audit remain unchanged.

The supplement covers affine descent and convergence equivalences, repeated-block and global parity rigidity, finite parity complexity, necessary parity-frequency inequalities, binary residue reconstruction, first-crossing and Diophantine arithmetic, coefficient stopping-time restrictions, and hypothetical cycle minima and odd-core arithmetic.

The archived logs record successful individual-file checks using Lean and Mathlib v4.19.0; the reported dependencies are standard Lean foundational axioms, with no `sorryAx` dependencies in the 89 audited declarations. See the [audit directory](Collatz%20Research%20v2.3/audit), [environment record](Collatz%20Research%20v2.3/audit/environment.txt), and [integrity manifest](Collatz%20Research%20v2.3/SHA256SUMS.txt). Reproduction instructions are in the supplement README. A clean independent rebuild of the packaged supplement has not yet been performed.

**Scope and limitations:** v2.3 is not a proof or disproof of the Collatz conjecture. Universal descent, divergence exclusion and nontrivial positive cycle exclusion remain open. The audits establish only the encoded statements under their explicit hypotheses; external computational bounds and analytical deductions are not certified in their entirety. No claim of historical novelty, independent peer review, or verification of the broader physical framework is made by this supplement.

The Zenodo DOI above refers to the previously cited record; a version-specific v2.3 DOI will be added after archival publication.

## Abstract

The Collatz–Runyan Arithmetic Framework is an interdisciplinary research programme investigating mathematical relationships between discrete arithmetic, number theory, noncommutative geometry, quantum mechanics, particle physics, special and general relativity, quantum gravity, supergravity and string theory.

The framework explores whether fundamental geometric structures and physical laws can emerge from underlying arithmetic dynamics rather than being introduced as independent assumptions.

Beginning with the Collatz transformation, Bernoulli numbers, 2-adic and 3-adic arithmetic, Pell equations and Diophantine relationships, the research develops arithmetic spectral operators, modular geometries, quantum matter models, relativistic symmetries and candidate continuum limits.

The repository contains mathematical manuscripts, formal theorems, supporting lemmas, analytical proofs, Lean 4 formalizations with archived compilation and axiom-audit evidence, symbolic derivations, Python verification engines, computational experiments, numerical results, technical cross-audits and interactive three-dimensional visualizations.

**Start here:** [Expanded proof paper v2.1L](Proofs/Collatz_Runyan_Theorems_Lemmas_Proofs_v21L.pdf) · [Lean formal verification v2.2](Lean%20Proofs/README.md) · [Kernel build log](Lean%20Proofs/kernel_verification.txt) · [Axiom audit](Lean%20Proofs/axiom_verification.txt).

The research emphasizes reproducibility, mathematical consistency, transparent assumptions, independent verification and the documentation of negative results.

## 1. Fundamental Research Objectives

The central objective of the Collatz–Runyan Framework is to investigate whether a common arithmetic foundation can provide a mathematically consistent microscopic description of spacetime, matter and gravitational interactions.

The research programme addresses:

- The Collatz conjecture and deterministic arithmetic descent.
- 2-adic and 3-adic dynamical systems.
- Bernoulli numbers, the Basel problem and Riemann zeta functions.
- Pell equations and arithmetic Lorentz transformations.
- Noncommutative operator algebras.
- Emergent spacetime dimensionality and causal geometry.
- Special and general relativity.
- Quantum field theory and gravitational scattering amplitudes.
- Higgs dynamics and spontaneous symmetry breaking.
- The cosmological constant problem and quantum vacuum energy.
- Supersymmetry, gravitinos and modular supergravity.
- Kaluza–Klein compactification and Epstein spectral functions.
- Arithmetic string dynamics and D-brane operator algebras.
- Mathematical obstructions to realistic chiral particle spectra.
- The possibility of a controlled arithmetic quantum theory of gravity.

## 2. Arithmetic and Number-Theoretic Foundations

The framework begins with the Collatz transformation

$$
T(n)=
\begin{cases}
n/2,&n\equiv0\pmod2,\\
3n+1,&n\equiv1\pmod2.
\end{cases}
$$

The research investigates parity histories, inverse arithmetic branches, stopping times, residue classes, p-adic valuations and exact Diophantine descent certificates.

The original arithmetic investigation also incorporates the Bernoulli number

$$
B_{32}=-\frac{7709321041217}{510},
$$

whose numerator possesses the exact prime factorization

$$
7709321041217=37\cdot683\cdot305065927.
$$

These arithmetic relationships motivate subsequent spectral and geometric constructions.

The corrected Collatz trajectory of the Bernoulli-derived integer 305065927 reaches 1 after 243 standard transitions, comprising 83 odd operations and 160 even operations.

The framework does not currently claim a proof of the Collatz conjecture.

## 3. The Runyan Arithmetic Spectral Operator

A central mathematical construction is the symmetric arithmetic operator

$$
A=
\begin{pmatrix}
3&\sqrt{185}\\
\sqrt{185}&17
\end{pmatrix}.
$$

Its exact eigenvalues are

$$
\lambda_\pm=10\pm\sqrt{234}.
$$

Under an additional physical mass interpretation, the corresponding positive mass scales are

$$
m_\pm=M(\sqrt{234}\pm10),
$$

where $M$ is a model-dependent reference scale.

The spectrum generates the exact invariants

$$
m_-m_+=134M^2,
$$

$$
m_-^2+m_+^2=668M^2.
$$

These relationships provide a common spectral foundation for investigations involving quantum matter, gravitational effective actions, particle mass hierarchies, spectral determinants and vacuum-energy contributions.

Their identification with observed elementary particles remains an open physical question.

## 4. Collatz Dynamics and Diophantine Descent

The framework develops exact arithmetic descent certificates through finite parity histories.

For a shortcut Collatz trajectory of length $k$, containing $m$ odd operations, the iterated transformation can be expressed as

$$
T^k(n)=\frac{3^mn+c}{2^k}.
$$

Strict descent occurs precisely when

$$
(2^k-3^m)n>c.
$$

Research includes residue-class certificate enumeration, exceptional parity histories, combined 2-adic and 3-adic constraints, weighted arithmetic transfer operators and candidate Lyapunov functionals.

Computational investigations extend coefficient-contraction survival calculations through 500 shortcut iterations.

The research also identifies fundamental limitations of fixed-resolution modular corrections and randomized contraction arguments. Statistical convergence does not constitute a universal proof.

## 5. Noncommutative Arithmetic Geometry

Representing the two inverse Collatz branches as Hilbert-space isometries produces operators satisfying the Cuntz relations.

At arithmetic history depth $k$, the associated matrix-unit algebra satisfies

$$
\mathcal A_k\cong M_{2^k}(\mathbb C).
$$

At the elementary branch level,

$$
\mathcal A_1\cong M_2(\mathbb C).
$$

Its Hermitian component possesses four independent real coordinates and the exact determinant

$$
\det X=t^2-x^2-y^2-z^2.
$$

This establishes a Lorentzian quadratic space within the arithmetic operator representation.

The construction also admits canonical phase symmetries and unitary branch-mixing transformations, providing a mathematical setting for investigating candidate gauge structures.

These are algebraic symmetries rather than established physical gauge interactions.

## 6. Arithmetic Reconstruction of Special and General Relativity

The framework investigates a conditional reconstruction of Einstein's theories through arithmetic branch algebras, Pell equations, spinorial transformations and local differential geometry.

The Pell equation

$$
u^2-Dv^2=1
$$

generates exact Lorentz transformations.

Multiplicatively independent Pell units generate dense sets of rapidities, allowing continuous Lorentz symmetry to be recovered under specified spatial-frame assumptions.

The research reconstructs standard special-relativistic relationships, including time dilation, length contraction and the relativistic energy–momentum equation

$$
E^2=p^2c^2+m^2c^4.
$$

Local spin frames, curvature, tetrads and quantum-induced gravitational terms provide a conditional route to the Einstein field equations:

$$
G_{\mu\nu}+\Lambda g_{\mu\nu}
=\frac{8\pi G}{c^4}T_{\mu\nu}.
$$

Symbolic and numerical investigations reproduce Schwarzschild–de Sitter geometry, Friedmann cosmological equations, gravitational time dilation, solar light deflection and Mercury's anomalous perihelion advance.

These results demonstrate consistency with established relativity under conventional continuum assumptions. They do not yet establish that physical spacetime, the equivalence principle or fundamental physical constants emerge uniquely from arithmetic.

## 7. Quantum Matter, Higgs Dynamics and Induced Gravity

The framework investigates arithmetic mass spectra coupled to quantum matter, including matched scalar and fermionic degrees of freedom.

The research addresses:

- Radiative Higgs symmetry breaking.
- Coleman–Weinberg and Gildener–Weinberg effective potentials.
- Heat-kernel expansions.
- Functional determinants.
- Matter-induced Einstein–Hilbert curvature terms.
- Graviton propagators and physical polarization states.
- Nonlocal gravitational form factors.
- Gravitational scattering amplitudes.
- Optical-theorem and unitarity constraints.
- Infrared cancellation and ultraviolet behavior.

Under specified free-field assumptions, matched bosonic and fermionic matter contributions produce

$$
a_0=0,\qquad a_1=(1-4\xi)R.
$$

The leading volume coefficient cancels while a nonzero curvature contribution can survive.

The resulting induced Newton coupling remains dependent on regulator choices, the matter spectrum and the underlying physical scale.

Complete ultraviolet consistency and radiatively stable vacuum cancellation remain unresolved.

## 8. Modular Geometry and Supergravity

The arithmetic compactification programme investigates three distinguished quadratic parameters:

$$
D\in\{3,37,137\}.
$$

Associated research includes Pell geometry, modular transformations, Dedekind eta functions, modular-invariant potentials, conformal field theories and toroidal compactifications.

The candidate internal geometry is

$$
T^6=T^2_3\times T^2_{37}\times T^2_{137}.
$$

The corresponding dimensionless rectangular metric has determinant 15207.

Supergravity investigations address spontaneous supersymmetry breaking, Polonyi models, gravitino dynamics, no-scale geometry, supertrace constraints and modular vacuum stabilization.

A technical cross-audit identified a global negative Kähler-metric defect in an earlier deformation. A corrected smooth localized construction preserves the relevant local vacuum structure while establishing positive moduli-space kinetic geometry under stated conditions.

A complete globally stable quantum vacuum and realistic supersymmetric particle spectrum remain open research objectives.

## 9. The Basel Problem, Spectral Zeta Functions and Vacuum Energy

The framework incorporates Euler's Basel identity

$$
\zeta(2)=\frac{\pi^2}{6}
$$

and its generalization through Bernoulli numbers:

$$
\zeta(2n)=
\frac{(-1)^{n+1}B_{2n}(2\pi)^{2n}}
{2(2n)!}.
$$

These identities connect the original arithmetic foundations to spectral geometry, compactification and quantum effective actions.

Research includes:

- Kaluza–Klein mass towers.
- Generalized Epstein zeta functions.
- Poisson resummation.
- Spectral determinants and modular functions.
- Periodic and antiperiodic quantum boundary conditions.
- Casimir energies.
- Radion stabilization.
- Six-dimensional arithmetic winding spectra.

An extended Casimir model demonstrates conditional local stabilization of a compactification radius and permits anti-de Sitter, Minkowski and positive-energy radial vacua through an adjustable bulk vacuum coefficient.

The local renormalized cosmological constant is not determined by these spectral calculations alone.

## 10. Arithmetic String Dynamics and D-Branes

The framework explores mathematical relationships between Collatz inverse histories, noncommutative matrix algebras and string-theoretic constructions.

Arithmetic history matrices reproduce the multiplication structure of Chan–Paton endpoint factors:

$$
E_{uv}E_{rs}=\delta_{vr}E_{us}.
$$

The affine commutator of the rationally extended Collatz inverse branches produces the translation

$$
C(x)=x-\frac13.
$$

Modulo $2^k$, this translation generates a cyclic graph of exactly $2^k$ vertices.

Under an explicitly rescaled graph metric, these cycles converge to a continuous circle.

Introducing harmonic nearest-neighbor dynamics gives the oscillator spectrum

$$
\omega_p=
\frac{2c_s}{a}
\left|\sin\frac{\pi p}{N}\right|.
$$

Its continuum limit reproduces free periodic string-like oscillations.

The corresponding bulk-subtracted quantum vacuum energy converges to

$$
E_{\mathrm{Casimir}}
=-\frac{\pi\hbar c_s}{6L}.
$$

These constructions establish mathematically controlled string analogues. Physical string tension, worldsheet supersymmetry, conformal anomaly cancellation, critical spacetime dimensionality and interacting closed-string gravitons have not yet been derived from arithmetic.

## 11. Formal Theorems, Lemmas and Proofs — v2.1L

The expanded mathematical edition contains:

- Five principal theorems.
- Seventeen supporting lemmas.
- Five corollaries.
- Twenty-seven accompanying proofs.

The principal results establish:

**Theorem 1 — Arithmetic History Algebra**

The finite-depth Collatz inverse-history representation generates full complex matrix algebras.

**Theorem 2 — Lorentzian Quadratic Geometry**

The Hermitian elementary branch algebra admits the exact four-dimensional Minkowski quadratic form.

**Theorem 3 — Arithmetic Circular Continuum**

Affine Collatz commutators generate cyclic graphs converging to a continuous circle under specified metric rescaling.

**Theorem 4 — Quantum Casimir Energy**

The quantized harmonic arithmetic cycle reproduces the standard periodic scalar Casimir energy after bulk subtraction.

**Theorem 5 — Generalized D-Brane Intersection Obstruction**

For the specified rectangular arithmetic six-torus, product symplectic structure and phase-zero special Lagrangian calibration, compact oriented special Lagrangian three-cycles have identically vanishing mutual homological intersection numbers.

The fifth theorem reduces the relevant integral homology lattice from rank twenty to a primitive rank-four isotropic subgroup generated by

$$
xxx,\quad xyy,\quad yxy,\quad yyx.
$$

Consequently,

$$
[\Sigma_a]\cdot[\Sigma_b]=0.
$$

This establishes an obstruction to net chiral intersections in the specified bulk D6-brane compactification, including nonfactorized special Lagrangian cycles.

The theorem does not exclude more general string compactifications, modified moduli, fractional branes, fluxed branes or alternative calibration structures.

## 12. Lean 4 Formal Verification — v2.2

The repository now includes a [Lean 4 and Mathlib project](Lean%20Proofs/README.md), pinned to Lean v4.19.0, implementing selected mathematical statements from the research programme. A successful local rebuild is documented in the archived kernel build log, including compilation of all four project modules and the root module. A separate axiom audit records the dependencies of seven selected theorems.

| Formal statement | Scope |
| --- | --- |
| `affine_commutator` | Exact commutator of rational affine branch extensions |
| `descent_certificate` | Descent equivalence given an affine trajectory identity and positive denominator |
| `matrix_unit_mul` | Matrix-unit multiplication assuming the cancellation relations |
| `lorentzian_polynomial` | Real polynomial identity of Minkowski signature |
| `hermitian_determinant_formula` | Algebraic two-by-two determinant identity |
| `boost_invariant` | Preservation of the Lorentz quadratic form under the stated boost condition |
| `supported_pairing_zero` | Zero integral pairing for vectors supported on the four admissible coordinate triples |

The recorded audit lists only standard Lean foundational axioms: `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx` dependency appears in the seven audited statements. Kernel type-checking and axiom inspection are distinct verification steps; the latter is not a substitute for the former.

### Reproduce the verification

Install [Lean 4](https://lean-lang.org/install/) and Git, then run from the repository root:

```sh
cd "Lean Proofs"
lake exe cache get
lake build CollatzRunyan
lake env lean Verification.lean
```

The dependency manifest is included. On a new setup, if dependency resolution is required, run `lake update` first. A GitHub Actions workflow is also provided for automated builds.

### Archived evidence

- [Kernel build log](Lean%20Proofs/kernel_verification.txt)
- [Axiom dependency audit](Lean%20Proofs/axiom_verification.txt)
- [Build verification log](Lean%20Proofs/build_verification.txt)
- [Verification source](Lean%20Proofs/Verification.lean)
- [Dependency manifest](Lean%20Proofs/lake-manifest.json)
- [Lean project source and documentation](Lean%20Proofs/README.md)

The evidence documents a successful author-run local build; it is not an independent human peer review or a claim that a fresh external build has been performed for this README update. The full geometric D-brane theorem, the complete Hilbert-space branch representation, the circle continuum limit and the Casimir limit remain to be formalized. Lean establishes the encoded propositions under their stated hypotheses; it does not establish originality, empirical validity, or the entire framework.

## 13. Computational Verification and Cross-Auditing

The research employs analytical derivations, exact integer and rational arithmetic, symbolic computation, high-precision numerical calculations and independent numerical comparisons.

Computational resources include Python, NumPy, SciPy, SymPy and mpmath.

The programme incorporates technical cross-verification performed with ChatGPT and Google Gemini, including corrections to numerical calculations, algebraic conventions and physical interpretations.

Verification procedures include reproducibility checks, archived computational outputs, matrix diagonalization, spectral calculations, exact homology calculations and independent evaluations of mathematical expressions.

Computational reproducibility supports the reported calculations but does not replace analytical proof, experimental validation or independent human peer review.

## 14. Research Papers and Repository Resources

The repository includes the master research monograph, subsequent technical manuscripts, standalone mathematical papers and verification engines.

Selected resources:

- [Master Research Monograph](Collatz_Runyan_Master_Paper.pdf)
- [Cross-Verified Technical Synthesis v1.5R](Collatz_Runyan_Cross_Verified_Synthesis_v15R.pdf)
- [Arithmetic Reconstruction of Special and General Relativity v1.9](Collatz-Runyan%20Framework/Collatz_Runyan_Arithmetic_Relativity_v19.pdf)
- [Verified Mathematical Proofs v2.1R](Proofs/Collatz_Runyan_Verified_Proofs_v21R.pdf)
- [Expanded Theorems, Lemmas and Proofs v2.1L](Proofs/Collatz_Runyan_Theorems_Lemmas_Proofs_v21L.pdf)
- [Independent Proof Verification Engine](Proofs/runyan_proof_audit_v21.py)

## 15. Interactive Three-Dimensional Research Laboratory

The [Collatz–Runyan 3D Visualization Suite v3.0](Collatz_Runyan_3D_Visualization_Suite_v3.html) provides 38 interactive visualization environments across seven research categories.

These environments cover arithmetic and modular geometry, compactification, particle physics, spacetime refinement, induced gravity, Higgs potentials, gravitational scattering, graviton propagators and modular supergravity.

The suite includes numerical surfaces, mathematical diagrams and schematic physical interpretations.

It is designed to operate offline in a modern browser, with interactive WebGL rendering where supported and static visualization fallbacks.

## 16. Scientific Status and Open Problems

The Collatz–Runyan Framework remains an exploratory research programme.

Established mathematical results are explicitly distinguished from conditional constructions, computational benchmarks, speculative physical interpretations and unresolved conjectures.

Major open objectives include:

- A universal proof of the Collatz conjecture.
- A dynamical four-dimensional continuum emerging from arithmetic.
- Derivation of the equivalence principle.
- Arithmetic selection of physical gauge symmetries.
- A realistic interacting chiral particle spectrum.
- Regulator-independent predictions of fundamental physical constants.
- Radiatively stable vacuum-energy cancellation.
- Quantum-consistent worldsheet supersymmetry and string dynamics.
- Emergent interacting massless spin-two particles.
- A complete ultraviolet-consistent quantum theory of gravity.

The framework does not claim to have established a theory of everything, solved the cosmological constant problem or experimentally discovered new physical laws.

## 17. Future Research Directions

The next formal verification milestone is to complete the supporting lemmas for the special Lagrangian intersection obstruction, especially multiquadratic radical independence and the passage from geometric constraints to integral homology. The broader research stages concentrate on arithmetic discrete Cartan geometry, noncommutative spectral triples, adaptive Diophantine descent certificates, coupled modular vacuum stabilization, Virasoro symmetry, worldsheet supersymmetry and candidate emergent gravitational degrees of freedom.

The long-term objective is to determine whether established physical theories can arise as controlled effective descriptions of a deeper arithmetic quantum structure.

## 18. Scientific Review and Collaboration

Independent mathematical verification, constructive criticism, replication of computational experiments, literature comparisons and technical corrections are welcomed.

Researchers are encouraged to examine both successful constructions and documented mathematical obstructions.

The programme prioritizes mathematical rigor over numerical coincidence, reproducible evidence over speculative interpretation, and transparent correction over unsupported claims.

## 19. Citation and Research Provenance

**Runyan, Jake Thomas (2026).** *The Collatz–Runyan Arithmetic Framework: Arithmetic Foundations, Relativistic Geometry, Quantum Gravity, Modular Supergravity and Emergent String Dynamics.* Independent research programme, through version 2.3.

When citing individual results, reference the relevant version-specific manuscript, theorem or computational experiment. Use the corresponding Zenodo DOI when available.

AI-assisted mathematical investigation, computational development and technical auditing include contributions from OpenAI ChatGPT and Google Gemini.

The manuscripts remain subject to author review, independent mathematical scrutiny and formal peer review.

For licensing and reuse conditions, consult the repository's [LICENSE](LICENSE) file.

---

**From discrete arithmetic to continuous geometry — investigating the mathematical foundations of spacetime, matter and fundamental interactions.**
