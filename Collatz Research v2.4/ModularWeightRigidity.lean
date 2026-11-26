import Mathlib

open scoped BigOperators

/-! Modular weight cancellation, following the exceptional-gap balance.
The divisibility hypothesis is the necessary modular weight condition for a
closed cycle. These are arithmetic exclusion certificates, not a proof of
universal cycle exclusion. The concrete example refutes a universal bound
on sums of positive residue representatives. -/
namespace CollatzRunyan.ModularWeightRigidity

-- Congruent sums have identical divisibility status.
theorem residue_dvd_iff (q s t : ℤ) (h : q ∣ s-t) :
    (q ∣ s) ↔ (q ∣ t) := by
  constructor
  · intro hs
    have hd := dvd_sub hs h
    have he : s-(s-t) = t := by ring
    rwa [he] at hd
  · intro ht
    have hd := dvd_add h ht
    have he : s-t+t = s := by ring
    rwa [he] at hd

-- Removing a pair that sums to zero modulo q changes no divisibility test.
theorem opposite_pair_cancel (q u v s : ℤ) (h : q ∣ u+v) :
    (q ∣ u+v+s) ↔ (q ∣ s) := by
  apply residue_dvd_iff
  have he : u+v+s-s = u+v := by ring
  rwa [he]

-- Two positive complementary representatives already contribute at least q.
theorem positive_small_not_dvd (q s : ℤ) (hs : 0 < s) (hq : s < q) :
    ¬ q ∣ s := by
  rintro ⟨t, ht⟩
  have hqp : 0 < q := by omega
  by_cases htp : 0 < t
  · have hm := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ t-1 by omega)
    nlinarith
  · have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ q by omega)
          (show t ≤ 0 by omega)
    linarith

theorem opposite_pair_lower_bound (q u v : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hd : q ∣ u+v) : q ≤ u+v := by
  by_contra h
  exact positive_small_not_dvd q (u+v) (by omega) (by omega) hd

-- Repeated pair cancellation can be represented by a finite sum of blocks.
theorem zero_block_sum (q : ℤ) (b : ℕ → ℤ) (n : ℕ) :
    (∀ i : ℕ, i < n → q ∣ b i) → q ∣ ∑ i ∈ Finset.range n, b i := by
  induction n with
  | zero => intro h; simp
  | succ n ih =>
      intro h
      rw [Finset.sum_range_succ]
      exact dvd_add (ih (fun i hi => h i (Nat.lt.step hi)))
        (h n (Nat.lt_succ_self n))

-- Once zero-sum blocks are removed, a small positive residual excludes closure.
theorem small_residual_exclusion (q s : ℤ) (b : ℕ → ℤ) (n : ℕ)
    (hb : ∀ i : ℕ, i < n → q ∣ b i)
    (hs : 0 < s) (hq : s < q) :
    ¬ q ∣ (∑ i ∈ Finset.range n, b i)+s := by
  intro h
  have hblocks := zero_block_sum q b n hb
  have hd := dvd_sub h hblocks
  have he : (∑ i ∈ Finset.range n, b i)+s-(∑ i ∈ Finset.range n, b i) = s := by ring
  rw [he] at hd
  exact positive_small_not_dvd q s hs hq hd

-- For weights congruent to +u or -u, only the signed count matters.
theorem signed_count_iff (q s u p m : ℤ) (hu : IsCoprime q u)
    (h : q ∣ s-u*(p-m)) : (q ∣ s) ↔ (q ∣ p-m) := by
  constructor
  · intro hs
    apply hu.dvd_of_dvd_mul_left
    exact (residue_dvd_iff q s (u*(p-m)) h).mp hs
  · rintro ⟨t, ht⟩
    apply (residue_dvd_iff q s (u*(p-m)) h).mpr
    refine ⟨u*t, ?_⟩
    rw [ht]
    ring

-- A nonzero signed count of magnitude less than the modulus cannot vanish.
theorem signed_count_exclusion (q s u p m : ℤ) (hu : IsCoprime q u)
    (h : q ∣ s-u*(p-m)) (hne : p ≠ m)
    (hlo : -q < p-m) (hhi : p-m < q) : ¬ q ∣ s := by
  intro hs
  have hd := (signed_count_iff q s u p m hu h).mp hs
  by_cases hp : 0 < p-m
  · exact positive_small_not_dvd q (p-m) hp hhi hd
  · have hn : 0 < -(p-m) := by omega
    have hbound : -(p-m) < q := by omega
    obtain ⟨t, ht⟩ := hd
    apply positive_small_not_dvd q (-(p-m)) hn hbound
    refine ⟨-t, ?_⟩
    rw [ht]
    ring

-- In particular, an odd total number of signed weights below q is impossible.
theorem odd_signed_count_exclusion (q s u p m : ℤ) (hu : IsCoprime q u)
    (h : q ∣ s-u*(p-m)) (hp : 0 ≤ p) (hm : 0 ≤ m)
    (hodd : (p+m)%2 = 1) (hsmall : p+m < q) : ¬ q ∣ s := by
  apply signed_count_exclusion q s u p m hu h <;> omega

-- Concrete counterexample: gaps (1,1,3), k=5, a=3, D=5, B=19.
-- All positive representatives obtained by nonzero scaling have sum > 5.
theorem minimization_counterexample (t : ℤ) (ht : 1 ≤ t) (hu : t < 5) :
    (5 : ℤ) < t%5+(4*t)%5+t%5 := by
  interval_cases t <;> norm_num

theorem counterexample_excluded :
    (2 : ℤ)^5-3^3 = 5 ∧ (3 : ℤ)^2+3*2+4 = 19 ∧
    ¬ (5 : ℤ) ∣ (19 : ℤ) := by norm_num

#print axioms residue_dvd_iff
#print axioms opposite_pair_cancel
#print axioms positive_small_not_dvd
#print axioms opposite_pair_lower_bound
#print axioms zero_block_sum
#print axioms small_residual_exclusion
#print axioms signed_count_iff
#print axioms signed_count_exclusion
#print axioms odd_signed_count_exclusion
#print axioms minimization_counterexample
#print axioms counterexample_excluded

end CollatzRunyan.ModularWeightRigidity
