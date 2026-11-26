import Mathlib

open scoped BigOperators

/-! Weighted modular cycle balance for arbitrary exceptional gaps.
The finite-chain lemmas are conditional on the transition and weight
congruences. The numerical example is an arithmetic exclusion certificate.
This file does not prove universal cycle exclusion. -/
namespace CollatzRunyan.ExceptionalGapRigidity

theorem weighted_chain (q : ℤ) (m x w : ℕ → ℤ) (n : ℕ) :
    (∀ i : ℕ, i < n → m i*x (i+1) = 3*x i+1) →
    (∀ i : ℕ, i < n → q ∣ w i*m i-3*w (i+1)) →
    q ∣ (∑ i ∈ Finset.range n, w i)-3*(w n*x n-w 0*x 0) := by
  induction n with
  | zero =>
      intro hs hw
      simp
  | succ n ih =>
      intro hs hw
      obtain ⟨s, hS⟩ := ih (fun i hi => hs i (Nat.lt.step hi))
        (fun i hi => hw i (Nat.lt.step hi))
      obtain ⟨t, ht⟩ := hw n (Nat.lt_succ_self n)
      have hstep := hs n (Nat.lt_succ_self n)
      have hmul := congrArg (fun z : ℤ => w n*z) hstep
      refine ⟨s+t*x (n+1), ?_⟩
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range n, w i)+w n-3*(w (n+1)*x (n+1)-w 0*x 0) =
          ((∑ i ∈ Finset.range n, w i)-3*(w n*x n-w 0*x 0))+
            (w n*m n-3*w (n+1))*x (n+1) := by
              linear_combination -hmul
        _ = _ := by rw [hS, ht]; ring

theorem weighted_cycle (q : ℤ) (m x w : ℕ → ℤ) (n : ℕ)
    (hs : ∀ i : ℕ, i < n → m i*x (i+1) = 3*x i+1)
    (hw : ∀ i : ℕ, i < n → q ∣ w i*m i-3*w (i+1))
    (hx : x n = x 0) (hc : w n = w 0) :
    q ∣ ∑ i ∈ Finset.range n, w i := by
  have h := weighted_chain q m x w n hs hw
  simpa [hx, hc] using h

theorem ordinary_weight (q m w : ℤ) (h : q ∣ m-3) :
    q ∣ w*m-3*w := by
  obtain ⟨t, ht⟩ := h
  refine ⟨w*t, ?_⟩
  calc
    w*m-3*w = w*(m-3) := by ring
    _ = _ := by rw [ht]; ring

theorem unit_gap_weight (q u v : ℤ) (h : 3*v = 2*u) :
    q ∣ 2*u-3*v := by
  rw [h, sub_self]
  exact dvd_zero q

theorem closing_weight (q m : ℤ) (r : ℕ)
    (h : q ∣ (2 : ℤ)^r*m-3^(r+1)) :
    q ∣ (2 : ℤ)^r*m-3*3^r := by
  have he : (3 : ℤ)^(r+1) = 3*3^r := by rw [pow_succ]; ring
  simpa only [he] using h

theorem weight_sum_bounds (w : ℕ → ℤ) (lo hi : ℤ) (n : ℕ) :
    (∀ i : ℕ, i < n → lo ≤ w i ∧ w i ≤ hi) →
    (n : ℤ)*lo ≤ (∑ i ∈ Finset.range n, w i) ∧
    (∑ i ∈ Finset.range n, w i) ≤ (n : ℤ)*hi := by
  induction n with
  | zero =>
      intro h
      simp
  | succ n ih =>
      intro h
      obtain ⟨hl, hu⟩ := ih (fun i hi' => h i (Nat.lt.step hi'))
      obtain ⟨ha, hb⟩ := h n (Nat.lt_succ_self n)
      rw [Finset.sum_range_succ]
      push_cast
      constructor <;> nlinarith

theorem positive_small_not_dvd (q s : ℤ) (hs : 0 < s) (hq : s < q) :
    ¬ q ∣ s := by
  rintro ⟨t, ht⟩
  have hqp : 0 < q := by omega
  by_cases htp : 0 < t
  · have ht1 : 1 ≤ t := by omega
    have hm := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ t-1 by omega)
    nlinarith
  · have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ q by omega)
          (show t ≤ 0 by omega)
    linarith

theorem bounded_weight_exclusion (q lo hi : ℤ) (m x w : ℕ → ℤ) (n : ℕ)
    (hs : ∀ i : ℕ, i < n → m i*x (i+1) = 3*x i+1)
    (hw : ∀ i : ℕ, i < n → q ∣ w i*m i-3*w (i+1))
    (hc : w n = w 0)
    (hb : ∀ i : ℕ, i < n → lo ≤ w i ∧ w i ≤ hi)
    (hl : 0 < (n : ℤ)*lo) (hu : (n : ℤ)*hi < q) : x n ≠ x 0 := by
  intro hx
  obtain ⟨hlo, hhi⟩ := weight_sum_bounds w lo hi n hb
  exact (positive_small_not_dvd q _ (lt_of_lt_of_le hl hlo) (lt_of_le_of_lt hhi hu))
    (weighted_cycle q m x w n hs hw hx hc)

-- Gaps (1,1,1,5) give D=175 and weights 27,18,12,8.
theorem three_unit_gap_example :
    (7 : ℤ) ∣ ((2 : ℤ)^8-3^4) ∧
    (7 : ℤ) ∣ ((2 : ℤ)^3*2^5-3^4) ∧
    ¬ (7 : ℤ) ∣ (27+18+12+8 : ℤ) := by norm_num

#print axioms weighted_chain
#print axioms weighted_cycle
#print axioms ordinary_weight
#print axioms unit_gap_weight
#print axioms closing_weight
#print axioms weight_sum_bounds
#print axioms positive_small_not_dvd
#print axioms bounded_weight_exclusion
#print axioms three_unit_gap_example

end CollatzRunyan.ExceptionalGapRigidity
