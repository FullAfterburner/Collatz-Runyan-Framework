import AsymptoticCoefficientRigidity

/-!
# Parity drift conflict and finite-block obstruction
The eventual parity-power bound excludes arbitrarily late prefixes with a
fixed subcritical rational odd frequency. Conversely, arbitrarily large
positive starting values have arbitrarily long all-odd finite prefixes.
This does not establish the subcritical-prefix hypothesis on any injective
orbit, nor prove the Collatz conjecture.
-/
namespace CollatzRunyan.ParityDriftConflict

open CollatzRunyan.SparseCoefficientRigidity (orbit shortcut oddCount coefficient)

/-- A rational certificate for a subcritical frequency p/b. -/
theorem eventual_above_certified_frequency (n p b : ℕ)
    (hinj : Function.Injective (orbit n)) (hb : 0 < b)
    (q : ℚ) (hq : 1 < q) (hcert : (3 : ℚ)^p * q^b ≤ (2 : ℚ)^b) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → p*k < b*oddCount n k := by
  obtain ⟨N, hN⟩ := AsymptoticCoefficientRigidity.eventual_parity_power_bound n hinj q hq
  refine ⟨N, ?_⟩
  intro k hk
  by_contra! hbad
  have hs := hN k hk
  have hstrict : ((2 : ℚ)^k)^b < ((3 : ℚ)^oddCount n k * q^k)^b := by
    have hb0 : b ≠ 0 := by omega
    gcongr <;> first | exact hs | exact hb0 | positivity | omega
  have ha : (3 : ℚ)^(oddCount n k*b) ≤ (3 : ℚ)^(p*k) := by
    apply pow_le_pow_right₀ (by norm_num)
    rw [Nat.mul_comm (oddCount n k) b]
    exact hbad
  have hq0 : 0 ≤ q := by linarith
  have hc : ((3 : ℚ)^p*q^b)^k ≤ ((2 : ℚ)^b)^k := by
    gcongr
  have hle : ((3 : ℚ)^oddCount n k*q^k)^b ≤ ((2 : ℚ)^k)^b := by
    calc
      _ = (3 : ℚ)^(oddCount n k*b)*q^(k*b) := by rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ (3 : ℚ)^(p*k)*q^(k*b) := mul_le_mul_of_nonneg_right ha (pow_nonneg hq0 _)
      _ = ((3 : ℚ)^p*q^b)^k := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm b k]
      _ ≤ ((2 : ℚ)^b)^k := hc
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm b k]
  exact (not_lt_of_ge hle) hstrict

/-- A concrete 5/8 certificate; 5/8 is strictly below log(2)/log(3). -/
theorem eventual_above_five_eighths (n : ℕ) (hinj : Function.Injective (orbit n)) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → 5*k < 8*oddCount n k := by
  exact eventual_above_certified_frequency n 5 8 hinj (by decide)
    (1001/1000) (by norm_num) (by norm_num)

/-- Arbitrarily late certified low-frequency prefixes force a repeat. -/
theorem certified_deficit_forces_repeat (n p b : ℕ) (hb : 0 < b)
    (q : ℚ) (hq : 1 < q) (hcert : (3 : ℚ)^p*q^b ≤ (2 : ℚ)^b)
    (hdef : ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ b*oddCount n k ≤ p*k) :
    ∃ i j : ℕ, i ≠ j ∧ orbit n i = orbit n j := by
  by_contra! h
  have hinj : Function.Injective (orbit n) := by
    intro i j he
    by_contra hne
    exact h i j hne he
  obtain ⟨N, hN⟩ := eventual_above_certified_frequency n p b hinj hb q hq hcert
  obtain ⟨k, hk, hd⟩ := hdef N
  exact (not_lt_of_ge hd) (hN k hk)

/-- Exact affine evolution while a dyadic factor remains in x+1. -/
theorem all_odd_run_formula (m k t : ℕ) (hm : 0 < m) :
    orbit (2^(k+t)*m-1) k+1 = 3^k*2^t*m ∧
    oddCount (2^(k+t)*m-1) k = k := by
  induction k generalizing t with
  | zero =>
    have hp : 0 < 2^t*m := by positivity
    have hcancel : 2^t*m-1+1 = 2^t*m := Nat.sub_add_cancel hp
    simp only [Nat.zero_add, orbit, oddCount, pow_zero, one_mul]
    exact ⟨hcancel, True.intro⟩
  | succ k ih =>
    have he : k+1+t = k+(t+1) := by omega
    let n := 2^(k+1+t)*m-1
    have h := ih (t+1)
    rw [← he] at h
    change orbit n k+1 = 3^k*2^(t+1)*m ∧ oddCount n k = k at h
    have hscale : 3^k*2^(t+1)*m = 2*(3^k*2^t*m) := by rw [pow_succ]; ring
    have ho : orbit n k % 2 ≠ 0 := by omega
    have hs : 2*shortcut (orbit n k) = 3*orbit n k+1 := by
      simp only [shortcut, if_neg ho]
      omega
    have hnext : 3^(k+1)*2^t*m = 3*(3^k*2^t*m) := by rw [pow_succ]; ring
    change shortcut (orbit n k)+1 = 3^(k+1)*2^t*m ∧
      (if orbit n k % 2 = 0 then oddCount n k else oddCount n k+1) = k+1
    rw [if_neg ho, h.2]
    constructor
    · omega
    · rfl

/-- The full all-odd prefix can occur at arbitrarily large starting values. -/
theorem arbitrarily_large_all_odd (L M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ oddCount n L = L := by
  refine ⟨2^L*(M+1)-1, ?_, ?_⟩
  · have hp0 : 0 < (2 : ℕ)^L := by positivity
    have hp : 1 ≤ (2 : ℕ)^L := by omega
    have hmul := Nat.mul_le_mul_right (M+1) hp
    omega
  · simpa using (all_odd_run_formula (M+1) L 0 (by omega)).2

/-- No fixed positive length can give uniform negative drift above a cutoff. -/
theorem no_uniform_block_contraction (L M : ℕ) (hL : 0 < L) :
    ∃ n : ℕ, M ≤ n ∧ 1 < coefficient n L := by
  obtain ⟨n, hn, ha⟩ := arbitrarily_large_all_odd L M
  refine ⟨n, hn, ?_⟩
  rw [SparseCoefficientRigidity.coefficient, ha, ← div_pow]
  have h : (3/2 : ℚ)^0 < (3/2 : ℚ)^L := pow_lt_pow_right₀ (by norm_num) hL
  simpa using h

#print axioms eventual_above_certified_frequency
#print axioms eventual_above_five_eighths
#print axioms certified_deficit_forces_repeat
#print axioms all_odd_run_formula
#print axioms arbitrarily_large_all_odd
#print axioms no_uniform_block_contraction

end CollatzRunyan.ParityDriftConflict
