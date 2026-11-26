import Mathlib

/-! Adaptive residue rigidity, arithmetic core. The constant-gap run
identities and their residue consequences are proved here. The full
fixed-depth counterexample family, including the choice of cycle exponents
and the product bound, is a separate mathematical argument. This module
makes no claim of universal cycle exclusion. -/
namespace CollatzRunyan.AdaptiveResidueRigidity

-- For a run of accelerated gap 2, subtract the fixed point 1.
theorem incoming_run_identity (x : ℕ → ℤ) (d : ℕ)
    (h : ∀ i, i < d → 4*x (i+1) = 3*x i+1) :
    (4 : ℤ)^d*(x d-1) = (3 : ℤ)^d*(x 0-1) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have he : 4*(x (d+1)-1) = 3*(x d-1) := by
        linarith only [h d (by omega)]
      have hp := ih (fun i hi => h i (by omega))
      calc
        (4 : ℤ)^(d+1)*(x (d+1)-1) = (4 : ℤ)^d*(4*(x (d+1)-1)) := by
          rw [pow_succ]; ring
        _ = (4 : ℤ)^d*(3*(x d-1)) := by rw [he]
        _ = 3*((4 : ℤ)^d*(x d-1)) := by ring
        _ = 3*((3 : ℤ)^d*(x 0-1)) := by rw [hp]
        _ = (3 : ℤ)^(d+1)*(x 0-1) := by rw [pow_succ]; ring

-- For a run of accelerated gap 1, add 1 instead.
theorem outgoing_run_identity (x : ℕ → ℤ) (d : ℕ)
    (h : ∀ i, i < d → 2*x (i+1) = 3*x i+1) :
    (2 : ℤ)^d*(x d+1) = (3 : ℤ)^d*(x 0+1) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have he : 2*(x (d+1)+1) = 3*(x d+1) := by
        linarith only [h d (by omega)]
      have hp := ih (fun i hi => h i (by omega))
      calc
        (2 : ℤ)^(d+1)*(x (d+1)+1) = (2 : ℤ)^d*(2*(x (d+1)+1)) := by
          rw [pow_succ]; ring
        _ = (2 : ℤ)^d*(3*(x d+1)) := by rw [he]
        _ = 3*((2 : ℤ)^d*(x d+1)) := by ring
        _ = 3*((3 : ℤ)^d*(x 0+1)) := by rw [hp]
        _ = (3 : ℤ)^(d+1)*(x 0+1) := by rw [pow_succ]; ring

-- The endpoint of a gap-2 run is 1 modulo the corresponding ternary power.
theorem incoming_run_residue (x : ℕ → ℤ) (d : ℕ)
    (h : ∀ i, i < d → 4*x (i+1) = 3*x i+1) :
    (3 : ℤ)^d ∣ x d-1 := by
  have hc : IsCoprime (3 : ℤ) 4 := ⟨-1, 1, by norm_num⟩
  have hc' : IsCoprime ((3 : ℤ)^d) ((4 : ℤ)^d) := hc.pow
  exact hc'.dvd_of_dvd_mul_left ⟨x 0-1, incoming_run_identity x d h⟩

-- An odd endpoint adds one binary digit to the outgoing residue condition.
theorem outgoing_run_residue (x : ℕ → ℤ) (d : ℕ) t
    (h : ∀ i, i < d → 2*x (i+1) = 3*x i+1)
    (ho : x d = 2*t+1) : (2 : ℤ)^(d+1) ∣ x 0+1 := by
  have hc : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
  have hc' : IsCoprime ((2 : ℤ)^(d+1)) ((3 : ℤ)^d) := hc.pow
  apply hc'.dvd_of_dvd_mul_left
  refine ⟨t+1, ?_⟩
  calc
    (3 : ℤ)^d*(x 0+1) = (2 : ℤ)^d*(x d+1) := (outgoing_run_identity x d h).symm
    _ = (2 : ℤ)^(d+1)*(t+1) := by rw [ho, pow_succ]; ring

-- The two local residue conditions are jointly satisfiable above any bound.
theorem local_residue_exists (d : ℕ) (L : ℤ) :
    ∃ x : ℤ, L ≤ x ∧ (3 : ℤ)^d ∣ x-1 ∧ (2 : ℤ)^(d+1) ∣ x+1 := by
  let P : ℤ := 3^d
  let Q : ℤ := 2^(d+1)
  have hbase : IsCoprime (3 : ℤ) 2 := ⟨1, -1, by norm_num⟩
  have hc : IsCoprime P Q := hbase.pow
  obtain ⟨u,v,huv⟩ := hc
  let R : ℤ := 1-2*u*P
  let t : ℤ := |R|+|L|+1
  have hp : 0 < P := by dsimp [P]; positivity
  have hq : 0 < Q := by dsimp [Q]; positivity
  have hpq : 1 ≤ P*Q := by
    have h1 : 1 ≤ P := by omega
    have h2 : 1 ≤ Q := by omega
    nlinarith only [h1,h2,mul_nonneg (show 0 ≤ P-1 by omega) (show 0 ≤ Q-1 by omega)]
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hprod := mul_nonneg (show 0 ≤ P*Q-1 by omega) ht
  refine ⟨R+P*Q*t, ?_, ?_, ?_⟩
  · have htbound : L ≤ R+t := by
      dsimp [t]
      linarith only [neg_abs_le R, le_abs_self L]
    nlinarith only [hprod, htbound]
  · change P ∣ R+P*Q*t-1
    refine ⟨-2*u+Q*t, ?_⟩
    dsimp [R]; ring
  · change Q ∣ R+P*Q*t+1
    refine ⟨2*v+P*t, ?_⟩
    dsimp [R]
    linear_combination -2*huv

-- A positive start of a complete gap-1 run is exponentially large.
theorem long_run_lower (b : ℕ) (x : ℤ) (hx : 0 < x)
    (h : (2 : ℤ)^(b+1) ∣ x+1) : (2 : ℤ)^(b+1)-1 ≤ x := by
  obtain ⟨t,ht⟩ := h
  have hp : 0 < (2 : ℤ)^(b+1) := by positivity
  have htpos : 0 < t := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hp) (show t ≤ 0 by omega)
    omega
  have hm := mul_nonneg (le_of_lt hp) (show 0 ≤ t-1 by omega)
  nlinarith only [ht,hm]

-- Conditional exclusion once the full ascending run exceeds the upper bound.
theorem long_run_exclusion (b : ℕ) (x U : ℤ) (hx : 0 < x)
    (hU : x ≤ U) (hsmall : U < (2 : ℤ)^(b+1)-1)
    (h : (2 : ℤ)^(b+1) ∣ x+1) : False := by
  have hl := long_run_lower b x hx h
  omega

-- A sufficiently large modulus determines at most one candidate in an interval.
theorem interval_unique (P L U x y : ℤ) (hP : U-L < P)
    (hx : L ≤ x ∧ x ≤ U) (hy : L ≤ y ∧ y ≤ U)
    (hd : P ∣ x-y) : x = y := by
  obtain ⟨t,ht⟩ := hd
  have hp : 0 < P := by omega
  by_cases hz : t = 0
  · rw [hz, mul_zero] at ht; omega
  · by_cases hs : 0 < t
    · have hm := mul_nonneg (le_of_lt hp) (show 0 ≤ t-1 by omega)
      nlinarith only [hm,ht,hP,hx.2,hy.1]
    · have hm := mul_nonneg (le_of_lt hp) (show 0 ≤ -t-1 by omega)
      nlinarith only [hm,ht,hP,hx.1,hy.2]

#print axioms incoming_run_identity
#print axioms outgoing_run_identity
#print axioms incoming_run_residue
#print axioms outgoing_run_residue
#print axioms local_residue_exists
#print axioms long_run_lower
#print axioms long_run_exclusion
#print axioms interval_unique

end CollatzRunyan.AdaptiveResidueRigidity
