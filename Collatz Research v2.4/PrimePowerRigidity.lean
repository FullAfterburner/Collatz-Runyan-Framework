import Mathlib

/-!
# Collatz–Runyan: prime-power gap rigidity
The gap congruence obstruction applies to any modulus q, hence to prime
powers. The recurrence lemmas use exact integer affine coefficients.
No universal cycle exclusion or historical novelty is asserted.
-/
namespace CollatzRunyan.PrimePowerRigidity

-- A single accelerated odd-to-odd transition.
theorem step_defect (q m x y : ℤ)
    (hgap : q ∣ m-3) (hstep : m*y = 3*x+1) :
    q ∣ 3*(y-x)-1 := by
  obtain ⟨t, ht⟩ := hgap
  refine ⟨-t*y, ?_⟩
  calc
    3*(y-x)-1 = -(m-3)*y := by linear_combination hstep
    _ = _ := by rw [ht]; ring

-- Telescoping the defects over a finite chain.
theorem chain_defect (q : ℤ) (m x : ℕ → ℤ) (n : ℕ) :
    (∀ i : ℕ, i < n → q ∣ m i-3) →
    (∀ i : ℕ, i < n → m i*x (i+1) = 3*x i+1) →
    q ∣ 3*(x n-x 0)-(n : ℤ) := by
  induction n with
  | zero =>
      intro hg hs
      simp
  | succ n ih =>
      intro hg hs
      have hprev := ih (fun i hi => hg i (Nat.lt.step hi))
        (fun i hi => hs i (Nat.lt.step hi))
      have hlast := step_defect q (m n) (x n) (x (n+1))
        (hg n (Nat.lt_succ_self n)) (hs n (Nat.lt_succ_self n))
      have he : 3*(x (n+1)-x 0)-((n+1 : ℕ) : ℤ) =
          (3*(x n-x 0)-(n : ℤ))+(3*(x (n+1)-x n)-1) := by
        push_cast
        ring
      change q ∣ 3*(x (n+1)-x 0)-((n+1 : ℕ) : ℤ)
      rw [he]
      exact dvd_add hprev hlast

-- Returning to the starting value forces the modulus to divide the count.
theorem cycle_count_divisible (q : ℤ) (m x : ℕ → ℤ) (n : ℕ)
    (hg : ∀ i : ℕ, i < n → q ∣ m i-3)
    (hs : ∀ i : ℕ, i < n → m i*x (i+1) = 3*x i+1)
    (hc : x n = x 0) : q ∣ (n : ℤ) := by
  obtain ⟨t, ht⟩ := chain_defect q m x n hg hs
  refine ⟨-t, ?_⟩
  rw [hc] at ht
  linear_combination -ht

-- Specialize to q=p^r and actual powers of two in the gap equations.
theorem prime_power_gap_obstruction (p : ℤ) (r n : ℕ)
    (g : ℕ → ℕ) (x : ℕ → ℤ)
    (hg : ∀ i : ℕ, i < n → p^r ∣ (2 : ℤ)^(g i)-3)
    (hs : ∀ i : ℕ, i < n → (2 : ℤ)^(g i)*x (i+1) = 3*x i+1)
    (hn : ¬ p^r ∣ (n : ℤ)) : x n ≠ x 0 := by
  intro hc
  exact hn (cycle_count_divisible (p^r) (fun i => (2 : ℤ)^(g i)) x n hg hs hc)

-- One step of the exact affine numerator congruence.
-- M' = M*m, B' = 3*B+M, and n counts odd steps.
theorem affine_defect_step (q M B m n : ℤ)
    (h : q ∣ 3*B-n*M) (hg : q ∣ m-3) :
    q ∣ 3*(3*B+M)-(n+1)*(M*m) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := hg
  refine ⟨3*u-(n+1)*M*v, ?_⟩
  calc
    3*(3*B+M)-(n+1)*(M*m) =
        3*(3*B-n*M)-(n+1)*M*(m-3) := by ring
    _ = _ := by rw [hu, hv]; ring

-- Iterate the affine congruence over a finite sequence of gap multipliers.
theorem affine_defect_chain (q : ℤ) (m M B : ℕ → ℤ) (n : ℕ)
    (hM0 : M 0 = 1) (hB0 : B 0 = 0) :
    (∀ i : ℕ, i < n → q ∣ m i-3) →
    (∀ i : ℕ, i < n → M (i+1) = M i*m i) →
    (∀ i : ℕ, i < n → B (i+1) = 3*B i+M i) →
    q ∣ 3*B n-(n : ℤ)*M n := by
  induction n with
  | zero =>
      intro hg hm hb
      simp [hM0, hB0]
  | succ n ih =>
      intro hg hm hb
      have hprev := ih (fun i hi => hg i (Nat.lt.step hi))
        (fun i hi => hm i (Nat.lt.step hi))
        (fun i hi => hb i (Nat.lt.step hi))
      have hnext := affine_defect_step q (M n) (B n) (m n) (n : ℤ)
        hprev (hg n (Nat.lt_succ_self n))
      change q ∣ 3*B (n+1)-((n+1 : ℕ) : ℤ)*M (n+1)
      rw [hm n (Nat.lt_succ_self n), hb n (Nat.lt_succ_self n)]
      simpa only [Nat.cast_add, Nat.cast_one] using hnext

-- Cancel the units 3 and M: numerator divisibility equals count divisibility.
theorem affine_count_iff (q M B n : ℤ)
    (h3 : IsCoprime q 3) (hM : IsCoprime q M)
    (hd : q ∣ 3*B-n*M) : (q ∣ B) ↔ (q ∣ n) := by
  obtain ⟨u, hu⟩ := hd
  constructor
  · rintro ⟨v, hv⟩
    apply hM.dvd_of_dvd_mul_left
    refine ⟨3*v-u, ?_⟩
    calc
      M*n = 3*B-(3*B-n*M) := by ring
      _ = _ := by rw [hu, hv]; ring
  · rintro ⟨v, hv⟩
    apply h3.dvd_of_dvd_mul_left
    refine ⟨u+v*M, ?_⟩
    calc
      3*B = (3*B-n*M)+n*M := by ring
      _ = _ := by rw [hu, hv]; ring

-- A concrete arithmetic example: the prime 5 cancels, but 25 does not.
-- Gap sequence [7,7,7,7,27], so k=55 and a=5.
theorem higher_power_example :
    (25 : ℤ) ∣ ((2 : ℤ)^55-3^5) ∧
    (5 : ℤ) ∣ (274877905 : ℤ) ∧
    ¬ (25 : ℤ) ∣ (274877905 : ℤ) := by norm_num

#print axioms step_defect
#print axioms chain_defect
#print axioms cycle_count_divisible
#print axioms prime_power_gap_obstruction
#print axioms affine_defect_step
#print axioms affine_defect_chain
#print axioms affine_count_iff
#print axioms higher_power_example

end CollatzRunyan.PrimePowerRigidity
