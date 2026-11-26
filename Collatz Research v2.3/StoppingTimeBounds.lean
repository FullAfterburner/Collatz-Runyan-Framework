import Mathlib

/-!
# Collatz–Runyan: stopping-time bounds

Standalone integer arithmetic for the improved first-crossing sieve.
The logarithm estimates, identification of the first crossing, and the
published verification threshold are separate inputs; this file does
not prove universal coefficient contraction or Collatz convergence.
-/
namespace CollatzRunyan.StoppingTimeBounds

/-- Any failure of descent in an affine step gives a bound on the gap.
The offset bound is a hypothesis (proved in DiophantineGap.lean for
first coefficient crossings). -/
theorem affine_gap_bound (n y A M B a : ℤ)
    (hM : 0 ≤ M) (h : M * y = A * n + B)
    (hb : 3 * B ≤ a * A) (hn : n ≤ y) :
    3 * (M - A) * n ≤ a * A := by
  have hh := mul_le_mul_of_nonneg_left hn hM
  nlinarith only [h, hb, hh]

/-- Bezout relation between the integer grid coordinate and the odd count. -/
theorem grid_identity (k a : ℤ) :
    137528045312 * (65470613321 * k - 103768467013 * a) =
      a + 65470613321 * (137528045312 * k - 217976794617 * a) := by
  ring

set_option maxHeartbeats 2000000 in
/-- For nonnegative grid coordinate and the proposed depth cap, the
odd count is strictly below the first determinant-one candidate. -/
theorem odd_count_cap (k a z : ℤ)
    (hk : k < 114208327604) (hz : 0 ≤ z)
    (he : z = 137528045312 * k - 217976794617 * a) :
    a < 72057431991 := by
  have hk' : k ≤ 114208327603 := by
    clear he hz
    omega
  linarith only [hk', hz, he]

set_option maxHeartbeats 2000000 in
/-- The normalized gap inequality forces the nonnegative grid coordinate
into the small set {0,1,2} when the seed is at least 2^71. -/
theorem grid_cap (n a z : ℤ)
    (hn : 2361183241434822606848 ≤ n) (ha : a < 72057431991)
    (hz : 0 ≤ z) (h : 2 * n * z ≤ a * 137528045312) : z ≤ 2 := by
  have hm := mul_le_mul_of_nonneg_right hn hz
  have h' : 2 * (2361183241434822606848 : ℤ) * z ≤ a * 137528045312 := by
    linarith only [hm, h]
  by_contra hnz
  have hz3 : 3 ≤ z := by
    clear hn ha hz h hm h'
    omega
  linarith only [h', ha, hz3]

set_option maxHeartbeats 2000000 in
/-- Exclude the complete grid range below the determinant-one candidate.
No enumeration of Collatz trajectories is required. -/
theorem grid_exclusion (n k a z : ℤ)
    (hn : 2361183241434822606848 ≤ n) (ha : 0 < a)
    (hk : k < 114208327604) (hz : 0 ≤ z)
    (he : z = 137528045312 * k - 217976794617 * a)
    (hg : 2 * n * z ≤ a * 137528045312) : False := by
  have ha' := odd_count_cap k a z hk hz he
  have hz' := grid_cap n a z hn ha' hz hg
  let w : ℤ := 65470613321 * k - 103768467013 * a
  have hw : 137528045312 * w = a + 65470613321 * z := by
    dsimp [w]
    rw [he]
    exact grid_identity k a
  clear_value w
  have hw0 : 0 < w := by linarith only [hw, ha, hz]
  have hw2 : w < 2 := by linarith only [hw, ha', hz']
  have hw1 : w = 1 := by
    clear hn ha hk hz he hg ha' hz' hw
    omega
  have hz2 : z = 2 := by
    by_contra hne
    have hz1 : z ≤ 1 := by
      clear hn ha hk he hg ha' hw hw0 hw2 hw1
      omega
    rw [hw1] at hw
    linarith only [hw, ha', hz1]
  have haeq : a = 6586818670 := by
    rw [hw1, hz2] at hw
    linarith only [hw]
  rw [haeq, hz2] at hg
  linarith only [hg, hn]

/-- If the normalized integer gap bound and nonnegative grid coordinate
hold at a crossing, the crossing must be at or beyond the new depth cap.
The analytic conversion into these hypotheses is not formalized here. -/
theorem crossing_depth_lower_bound (n k a : ℤ)
    (hn : 2361183241434822606848 ≤ n) (ha : 0 < a)
    (hz : 0 ≤ 137528045312 * k - 217976794617 * a)
    (hg : 2 * n * (137528045312 * k - 217976794617 * a) ≤ a * 137528045312) :
    114208327604 ≤ k := by
  by_contra h
  exact grid_exclusion n k a _ hn ha (lt_of_not_ge h) hz rfl hg

#print axioms affine_gap_bound
#print axioms grid_identity
#print axioms odd_count_cap
#print axioms grid_cap
#print axioms grid_exclusion
#print axioms crossing_depth_lower_bound

end CollatzRunyan.StoppingTimeBounds
