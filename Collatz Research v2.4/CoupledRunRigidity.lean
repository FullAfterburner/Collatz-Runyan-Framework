import Mathlib

namespace CollatzRunyan.CoupledRunRigidity

/-- An exact edge transfers lower bounds in the forward direction. -/
theorem forward_threshold (A P C u v L R : ℤ)
    (hA : 0 < A) (hP : 0 < P) (he : P*v = A*u+C)
    (hL : L ≤ u) (hR : P*(R-1) < A*L+C) : R ≤ v := by
  have h1 := mul_le_mul_of_nonneg_left hL (le_of_lt hA)
  by_contra! hn
  have h2 : v ≤ R-1 := by omega
  have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hP)
  linarith

/-- The same edge transfers lower bounds backwards. -/
theorem backward_threshold (A P C u v L R : ℤ)
    (hA : 0 < A) (hP : 0 < P) (he : P*v = A*u+C)
    (hL : L ≤ v) (hR : A*(R-1) < P*L-C) : R ≤ u := by
  have h1 := mul_le_mul_of_nonneg_left hL (le_of_lt hP)
  by_contra! hn
  have h2 : u ≤ R-1 := by omega
  have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hA)
  linarith

/-- Rounding up to the next member of a residue class modulo six is sound. -/
theorem residue_rounding (u L R : ℤ) (hL : L ≤ u)
    (hR : R-6 < L) (hc : (u-R) % 6 = 0) : R ≤ u := by
  omega

/-- If neither direction can improve a bound, the edge is exact. -/
theorem stable_edge (A P C L K : ℤ)
    (hf : A*L+C ≤ P*K) (hb : P*K-C ≤ A*L) :
    P*K = A*L+C := by
  linarith

/-- Simultaneous stability certifies every equation, including closure at r. -/
theorem stable_chain (A P C L : ℕ → ℤ) (r : ℕ)
    (hf : ∀ i < r, A i*L i+C i ≤ P i*L (i+1))
    (hb : ∀ i < r, P i*L (i+1)-C i ≤ A i*L i)
    (hc : L r = L 0) :
    (∀ i < r, P i*L (i+1) = A i*L i+C i) ∧ L r = L 0 := by
  refine ⟨?_, hc⟩
  intro i hi
  exact stable_edge (A i) (P i) (C i) (L i) (L (i+1)) (hf i hi) (hb i hi)

/-- Product of the edge coefficients in their given order. -/
def coeffProduct (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n+1 => coeffProduct f n * f n

/-- Affine numerator under composition of the edge equations. -/
def chainOffset (A P C : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => A n * chainOffset A P C n + coeffProduct P n * C n

/-- Compose all edge equations without dividing in the integers. -/
theorem chain_affine (A P C u : ℕ → ℤ)
    (he : ∀ i, P i*u (i+1) = A i*u i+C i) (n : ℕ) :
    coeffProduct P n*u n = coeffProduct A n*u 0+chainOffset A P C n := by
  induction n with
  | zero => simp [coeffProduct, chainOffset]
  | succ n ih =>
    simp only [coeffProduct, chainOffset]
    calc
      coeffProduct P n * P n * u (n+1) =
          coeffProduct P n * (P n * u (n+1)) := by ring
      _ = coeffProduct P n * (A n * u n + C n) := by rw [he n]
      _ = A n * (coeffProduct P n * u n) + coeffProduct P n * C n := by ring
      _ = coeffProduct A n * A n * u 0 +
          (A n * chainOffset A P C n + coeffProduct P n * C n) := by rw [ih]; ring

/-- Closing a chain gives the usual affine denominator equation. -/
theorem closed_denominator (A P C u : ℕ → ℤ)
    (he : ∀ i, P i*u (i+1) = A i*u i+C i) (n : ℕ)
    (hc : u n = u 0) :
    (coeffProduct P n-coeffProduct A n)*u 0 = chainOffset A P C n := by
  have h := chain_affine A P C u he n
  rw [hc] at h
  linear_combination h

/-- A monotone integer-valued potential cannot keep increasing under a finite cap. -/
theorem bounded_stabilization (f : ℕ → ℕ) (B : ℕ)
    (hmono : ∀ n, f n ≤ f (n+1)) (hcap : ∀ n, f n ≤ B) :
    ∃ n < B+1, f n = f (n+1) := by
  by_contra! hn
  have hg : ∀ n ≤ B+1, n ≤ f n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hb
      have h0 : n ≤ B+1 := by omega
      have h1 : n < B+1 := by omega
      have h2 := ih h0
      have h3 := hmono n
      have h4 := hn n h1
      omega
  have h1 := hg (B+1) (le_refl _)
  have h2 := hcap (B+1)
  omega

/-- The first surviving pattern from the finite sieve is excluded by one
backward update. Here the initial cores are 3 and 5, the updated core is 57,
and the two odd-run lengths are 1 and 4. -/
theorem coupled_example (u v : ℤ) (hv : 5 ≤ v) (hc : (u-57)%6 = 0)
    (he : 32*v = 3*u+1) :
    57 ≤ u ∧ (8 : ℤ)*5*79 ≤ 8*404 ∧ 8*113*79 > 170*404 := by
  have h := backward_threshold 3 32 1 u v 5 53 (by norm_num) (by norm_num)
    he hv (by norm_num)
  exact ⟨residue_rounding u 53 57 h (by norm_num) hc, by norm_num, by norm_num⟩

end CollatzRunyan.CoupledRunRigidity

#print axioms CollatzRunyan.CoupledRunRigidity.forward_threshold
#print axioms CollatzRunyan.CoupledRunRigidity.backward_threshold
#print axioms CollatzRunyan.CoupledRunRigidity.residue_rounding
#print axioms CollatzRunyan.CoupledRunRigidity.stable_edge
#print axioms CollatzRunyan.CoupledRunRigidity.stable_chain
#print axioms CollatzRunyan.CoupledRunRigidity.chain_affine
#print axioms CollatzRunyan.CoupledRunRigidity.closed_denominator
#print axioms CollatzRunyan.CoupledRunRigidity.bounded_stabilization
#print axioms CollatzRunyan.CoupledRunRigidity.coupled_example
