import FamilyCoefficientRigidity

/-!
# Asymptotic coefficient rigidity
For an injective shortcut orbit, every fixed finite interval is eventually
avoided. The exact multiplicative correction is therefore subexponential.
For each rational q > 1, the quantity coefficient n k * q^k eventually
exceeds every rational threshold. No three-free hypothesis is needed.
This is a necessary restriction, not a proof of Collatz convergence.
-/
namespace CollatzRunyan.AsymptoticCoefficientRigidity

open scoped BigOperators
open CollatzRunyan.SparseCoefficientRigidity (orbit coefficient oddCount)
open CollatzRunyan.FamilyCoefficientRigidity (visitCorrection orbit_product_identity)

/-- An injective sequence of natural numbers eventually exceeds every bound. -/
theorem injective_escape (f : ℕ → ℕ) (hinj : Function.Injective f) (M : ℕ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → M ≤ f k := by
  induction M with
  | zero => exact ⟨0, fun k _ => Nat.zero_le (f k)⟩
  | succ M ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases h : ∃ j : ℕ, f j = M
    · obtain ⟨j, hj⟩ := h
      refine ⟨max N (j+1), ?_⟩
      intro k hk
      have hkN : N ≤ k := le_trans (le_max_left _ _) hk
      have hkj : j+1 ≤ k := le_trans (le_max_right _ _) hk
      have hl := hN k hkN
      by_contra! hlt
      have he : f k = M := by omega
      have hi : k = j := hinj (he.trans hj.symm)
      omega
    · refine ⟨N, ?_⟩
      intro k hk
      have hl := hN k hk
      by_contra! hlt
      exact h ⟨k, by omega⟩

theorem visit_correction_ge_one (x : ℕ) : (1 : ℚ) ≤ visitCorrection x := by
  by_cases h : x % 2 = 0
  · simp [visitCorrection, h]
  · rw [visitCorrection, if_neg h]
    exact FamilyCorrectionProduct.correction_ge_one x

/-- A sufficiently large visit has correction at most q. -/
theorem visit_correction_le_rate (x : ℕ) (q : ℚ) (hq : 1 ≤ q)
    (hx : 0 < x) (hm : 1 ≤ 3*(x : ℚ)*(q-1)) : visitCorrection x ≤ q := by
  by_cases h : x % 2 = 0
  · simpa [visitCorrection, h] using hq
  · have hxq : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hx
    have hd : (1 : ℚ)/(3*(x : ℚ)) ≤ q-1 := by
      apply (div_le_iff₀ (by positivity : 0 < 3*(x : ℚ))).2
      calc
        1 ≤ 3*(x : ℚ)*(q-1) := hm
        _ = (q-1)*(3*(x : ℚ)) := by ring
    rw [visitCorrection, if_neg h, FamilyCorrectionProduct.correction]
    linarith

theorem eventually_correction_le (n : ℕ) (hinj : Function.Injective (orbit n))
    (q : ℚ) (hq : 1 < q) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → visitCorrection (orbit n k) ≤ q := by
  have hd : 0 < 3*(q-1) := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt ((1 : ℚ)/(3*(q-1)))
  have hm : (1 : ℚ) < (M : ℚ)*(3*(q-1)) := (div_lt_iff₀ hd).1 hM
  obtain ⟨N, hN⟩ := injective_escape (orbit n) hinj M
  refine ⟨N, ?_⟩
  intro k hk
  have hMk : (M : ℚ) ≤ (orbit n k : ℚ) := by exact_mod_cast hN k hk
  have hx := SparseCoefficientRigidity.injective_avoids_small n hinj k
  apply visit_correction_le_rate _ q hq.le (by omega)
  calc
    1 ≤ (M : ℚ)*(3*(q-1)) := hm.le
    _ ≤ (orbit n k : ℚ)*(3*(q-1)) := mul_le_mul_of_nonneg_right hMk hd.le
    _ = 3*(orbit n k : ℚ)*(q-1) := by ring

def correctionProduct (n k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, visitCorrection (orbit n i)

theorem correction_product_succ (n k : ℕ) :
    correctionProduct n (k+1) = correctionProduct n k * visitCorrection (orbit n k) := by
  simp only [correctionProduct, Finset.prod_range_succ]

theorem correction_product_ge_one (n k : ℕ) : 1 ≤ correctionProduct n k := by
  induction k with
  | zero => simp [correctionProduct]
  | succ k ih =>
    rw [correction_product_succ]
    calc
      1 ≤ correctionProduct n k := ih
      _ = correctionProduct n k * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (visit_correction_ge_one _) (by linarith)

/-- Once each correction is at most q, a tail of j visits costs at most q^j. -/
theorem tail_product_bound (n N : ℕ) (q : ℚ) (hq : 1 ≤ q)
    (h : ∀ i : ℕ, N ≤ i → visitCorrection (orbit n i) ≤ q) (j : ℕ) :
    correctionProduct n (N+j) ≤ correctionProduct n N * q^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show N+(j+1) = (N+j)+1 by omega, correction_product_succ, pow_succ]
    have hc := visit_correction_ge_one (orbit n (N+j))
    have hle := h (N+j) (by omega)
    have hq0 : 0 ≤ q := by linarith
    have hp0 : 0 ≤ correctionProduct n N := le_trans (by norm_num) (correction_product_ge_one n N)
    calc
      _ ≤ (correctionProduct n N * q^j) * q :=
        mul_le_mul ih hle (by linarith) (mul_nonneg hp0 (pow_nonneg hq0 _))
      _ = _ := by ring

/-- A rational subexponential envelope for the entire correction product. -/
theorem eventual_product_envelope (n : ℕ) (hinj : Function.Injective (orbit n))
    (q : ℚ) (hq : 1 < q) :
    ∃ B : ℚ, 0 < B ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      correctionProduct n k ≤ B*q^k := by
  obtain ⟨N, hN⟩ := eventually_correction_le n hinj q hq
  have hp := correction_product_ge_one n N
  refine ⟨correctionProduct n N, by linarith, N, ?_⟩
  intro k hk
  have htail := tail_product_bound n N q hq.le hN (k-N)
  have he : N+(k-N) = k := by omega
  rw [he] at htail
  have hpow : q^(k-N) ≤ q^k := pow_le_pow_right₀ hq.le (by omega)
  exact le_trans htail (mul_le_mul_of_nonneg_left hpow (by linarith))

/-- The trajectory is bounded above by the scaled coefficient times a constant. -/
theorem eventual_exponential_envelope (n : ℕ) (hinj : Function.Injective (orbit n))
    (q : ℚ) (hq : 1 < q) :
    ∃ A : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (orbit n k : ℚ) ≤ A * (coefficient n k * q^k) := by
  obtain ⟨B, hB, N, hN⟩ := eventual_product_envelope n hinj q hq
  have hn := SparseCoefficientRigidity.injective_avoids_small n hinj 0
  change 2 ≤ n at hn
  have hnq : 0 < (n : ℚ) := by exact_mod_cast (show 0 < n by omega)
  refine ⟨(n : ℚ)*B, mul_pos hnq hB, N, ?_⟩
  intro k hk
  have he := orbit_product_identity n k (fun i _ =>
    lt_of_lt_of_le (by decide : 0 < 2) (SparseCoefficientRigidity.injective_avoids_small n hinj i))
  change (orbit n k : ℚ) = coefficient n k * (n : ℚ) * correctionProduct n k at he
  have hc : 0 ≤ coefficient n k := by unfold SparseCoefficientRigidity.coefficient; positivity
  calc
    _ = _ := he
    _ ≤ (coefficient n k * (n : ℚ)) * (B*q^k) :=
      mul_le_mul_of_nonneg_left (hN k hk) (mul_nonneg hc hnq.le)
    _ = _ := by ring

/-- The scaled coefficient eventually exceeds every rational threshold. -/
theorem eventual_scaled_coefficient_growth (n : ℕ) (hinj : Function.Injective (orbit n))
    (q : ℚ) (hq : 1 < q) (D : ℚ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → D < coefficient n k * q^k := by
  obtain ⟨A, hA, N, hN⟩ := eventual_exponential_envelope n hinj q hq
  obtain ⟨M, hM⟩ := exists_nat_gt (D*A)
  obtain ⟨L, hL⟩ := injective_escape (orbit n) hinj M
  refine ⟨max N L, ?_⟩
  intro k hk
  have hkN : N ≤ k := le_trans (le_max_left _ _) hk
  have hkL : L ≤ k := le_trans (le_max_right _ _) hk
  have hMk : (M : ℚ) ≤ (orbit n k : ℚ) := by exact_mod_cast hL k hkL
  have hs : D*A < (coefficient n k*q^k)*A := by
    calc
      _ < (M : ℚ) := hM
      _ ≤ (orbit n k : ℚ) := hMk
      _ ≤ A*(coefficient n k*q^k) := hN k hkN
      _ = _ := by ring
  by_contra! hbad
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_right hbad hA.le)) hs

/-- In particular the coefficient cannot fall below q^(-k) arbitrarily late. -/
theorem eventual_no_exponential_contraction (n : ℕ) (hinj : Function.Injective (orbit n))
    (q : ℚ) (hq : 1 < q) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → 1 < coefficient n k * q^k :=
  eventual_scaled_coefficient_growth n hinj q hq 1

/-- Equivalent rational parity-power restriction, with no logarithms. -/
theorem eventual_parity_power_bound (n : ℕ) (hinj : Function.Injective (orbit n))
    (q : ℚ) (hq : 1 < q) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (2 : ℚ)^k < (3 : ℚ)^oddCount n k * q^k := by
  obtain ⟨N, hN⟩ := eventual_no_exponential_contraction n hinj q hq
  refine ⟨N, ?_⟩
  intro k hk
  have h := hN k hk
  rw [SparseCoefficientRigidity.coefficient, div_mul_eq_mul_div] at h
  have hh := (lt_div_iff₀ (by positivity : 0 < (2 : ℚ)^k)).1 h
  simpa only [one_mul] using hh

#print axioms injective_escape
#print axioms visit_correction_ge_one
#print axioms visit_correction_le_rate
#print axioms eventually_correction_le
#print axioms correction_product_succ
#print axioms correction_product_ge_one
#print axioms tail_product_bound
#print axioms eventual_product_envelope
#print axioms eventual_exponential_envelope
#print axioms eventual_scaled_coefficient_growth
#print axioms eventual_no_exponential_contraction
#print axioms eventual_parity_power_bound

end CollatzRunyan.AsymptoticCoefficientRigidity
