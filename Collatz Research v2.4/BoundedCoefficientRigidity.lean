import Mathlib

/-!
# Bounded coefficient rigidity
For the shortcut Collatz map, an injective orbit cannot have bounded
multiplicative coefficients 3^a / 2^k. The proof uses a cubic correction
bound, a finite product over the actual distinct visits, and a record
maximum. No conjecture about all Collatz orbits is assumed or asserted.
-/
namespace CollatzRunyan.BoundedCoefficientRigidity

open scoped BigOperators

def shortcut (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else (3*x+1)/2

def orbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k+1 => shortcut (orbit n k)

def oddCount (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => if orbit n k % 2 = 0 then oddCount n k else oddCount n k+1

def factor (x : ℕ) : ℚ := if x % 2 = 0 then 1/2 else 3/2

def coefficient (n k : ℕ) : ℚ := (3 : ℚ)^oddCount n k / (2 : ℚ)^k

def major (x : ℕ) : ℚ := if x ≤ 1 then 1 else (x : ℚ)/((x : ℚ)-1)

theorem coefficient_step (n k : ℕ) :
    coefficient n (k+1) = coefficient n k * factor (orbit n k) := by
  by_cases h : orbit n k % 2 = 0
  · simp only [coefficient, oddCount, factor, if_pos h, pow_succ]
    rw [div_mul_div_comm, mul_one]
  · simp only [coefficient, oddCount, factor, if_neg h, pow_succ]
    rw [div_mul_div_comm]

theorem major_ge_one (x : ℕ) : 1 ≤ major x := by
  by_cases h : x ≤ 1
  · simp [major, h]
  · have hx : (1 : ℚ) < (x : ℚ) := by exact_mod_cast (show 1 < x by omega)
    rw [major, if_neg h]
    apply (le_div_iff₀ (sub_pos.mpr hx)).2
    linarith

theorem cubic_step_bound (x : ℕ) (hx : 2 ≤ x) :
    (shortcut x : ℚ)^3 ≤ (factor x)^3 * (x : ℚ)^3 * major x := by
  have hxq : (2 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx
  have hx1 : 0 < (x : ℚ)-1 := by linarith
  have hx0 : 0 ≤ (x : ℚ) := by positivity
  by_cases h : x % 2 = 0
  · have he : 2*shortcut x = x := by
      simp only [shortcut, if_pos h]
      omega
    have heq : (2 : ℚ)*(shortcut x : ℚ) = (x : ℚ) := by exact_mod_cast he
    have ht : (shortcut x : ℚ) = (1/2 : ℚ)*(x : ℚ) := by linarith
    rw [ht, factor, if_pos h, mul_pow]
    calc
      _ = ((1/2 : ℚ)^3*(x : ℚ)^3)*1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (major_ge_one x) (by positivity)
  · have ho : 2*shortcut x = 3*x+1 := by
      simp only [shortcut, if_neg h]
      omega
    have hoq : (2 : ℚ)*(shortcut x : ℚ) = 3*(x : ℚ)+1 := by exact_mod_cast ho
    have ht : (shortcut x : ℚ) = (3*(x : ℚ)+1)/2 := by linarith
    have hh : ¬ x ≤ 1 := by omega
    rw [ht, factor, if_neg h, major, if_neg hh, ← mul_div_assoc]
    apply (le_div_iff₀ hx1).2
    nlinarith [sq_nonneg (x : ℚ)]

/-- Telescoping over all integers 2,...,R; no sorting is required. -/
theorem major_range (R : ℕ) (hR : 1 ≤ R) :
    (∏ x ∈ Finset.range (R+1), major x) = (R : ℚ) := by
  induction R with
  | zero => omega
  | succ R ih =>
    by_cases h : R = 0
    · subst R
      norm_num [Finset.prod_range_succ, major]
    · have hr : 1 ≤ R := by omega
      have hrq : 0 < (R : ℚ) := by exact_mod_cast hr
      have hh : ¬ R+1 ≤ 1 := by omega
      rw [Finset.prod_range_succ, ih hr, major, if_neg hh, Nat.cast_succ]
      have hden : (R : ℚ)+1-1 = (R : ℚ) := by ring
      rw [hden]
      field_simp [ne_of_gt hrq] <;> ring

/-- The actual orbit satisfies the cubic envelope with its visit product. -/
theorem orbit_product_bound (n k : ℕ) (hsmall : ∀ j < k, 2 ≤ orbit n j) :
    (orbit n k : ℚ)^3 ≤ (coefficient n k * (n : ℚ))^3 *
      (∏ j ∈ Finset.range k, major (orbit n j)) := by
  induction k with
  | zero => simp [orbit, coefficient, oddCount]
  | succ k ih =>
    have hi := ih (fun j hj => hsmall j (by omega))
    have hs := cubic_step_bound (orbit n k) (hsmall k (by omega))
    have hf : 0 ≤ factor (orbit n k) := by unfold factor; split <;> norm_num
    have hm : 0 ≤ major (orbit n k) := le_trans (by norm_num) (major_ge_one _)
    rw [coefficient_step, Finset.prod_range_succ]
    change (shortcut (orbit n k) : ℚ)^3 ≤ _
    calc
      _ ≤ (factor (orbit n k))^3 * (orbit n k : ℚ)^3 * major (orbit n k) := hs
      _ ≤ (factor (orbit n k))^3 * ((coefficient n k * (n : ℚ))^3 *
          (∏ j ∈ Finset.range k, major (orbit n j))) * major (orbit n k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (pow_nonneg hf _)) hm
      _ = _ := by ring

/-- Injection permits each correction factor to be charged at most once. -/
theorem distinct_visit_product (n k R : ℕ) (hR : 1 ≤ R)
    (hinj : Function.Injective (orbit n)) (hmax : ∀ j < k, orbit n j ≤ R) :
    (∏ j ∈ Finset.range k, major (orbit n j)) ≤ (R : ℚ) := by
  classical
  let s := (Finset.range k).image (orbit n)
  have hs : s ⊆ Finset.range (R+1) := by
    intro x hx
    change x ∈ (Finset.range k).image (orbit n) at hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (by have h := hmax j (Finset.mem_range.mp hj); omega)
  have he : (∏ x ∈ s, major x) = ∏ j ∈ Finset.range k, major (orbit n j) := by
    exact Finset.prod_image (fun i _ j _ h => hinj h)
  have hp (t : Finset ℕ) : (1 : ℚ) ≤ ∏ x ∈ t, major x := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert x t hx ih =>
      rw [Finset.prod_insert hx]
      have hm := major_ge_one x
      have ht : 0 ≤ ∏ x ∈ t, major x := le_trans (by norm_num) ih
      calc
        1 ≤ ∏ x ∈ t, major x := ih
        _ = 1 * (∏ x ∈ t, major x) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hm ht
  have hd : (∏ x ∈ Finset.range (R+1) \ s, major x) * (∏ x ∈ s, major x) =
      ∏ x ∈ Finset.range (R+1), major x := Finset.prod_sdiff hs
  rw [← he, ← major_range R hR, ← hd]
  calc
    _ = 1 * (∏ x ∈ s, major x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hp _) (le_trans (by norm_num) (hp s))

/-- Every injective shortcut orbit avoids 0 and the 1-2 cycle. -/
theorem injective_avoids_small (n : ℕ) (hinj : Function.Injective (orbit n)) (j : ℕ) :
    2 ≤ orbit n j := by
  by_contra! h
  have hc : orbit n j = 0 ∨ orbit n j = 1 := by omega
  rcases hc with h0 | h1
  · have he : orbit n (j+1) = orbit n j := by simp [orbit, h0, shortcut]
    have hh := hinj he
    omega
  · have he : orbit n (j+2) = orbit n j := by norm_num [orbit, h1, shortcut]
    have hh := hinj he
    omega

theorem exists_prefix_max (n k : ℕ) :
    ∃ j ≤ k, ∀ i ≤ k, orbit n i ≤ orbit n j := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro i hi
    have h : i = 0 := by omega
    simp [h]
  | succ k ih =>
    obtain ⟨j, hj, hmax⟩ := ih
    by_cases h : orbit n (k+1) ≤ orbit n j
    · refine ⟨j, by omega, ?_⟩
      intro i hi
      by_cases hi' : i ≤ k
      · exact hmax i hi'
      · have he : i = k+1 := by omega
        simpa [he] using h
    · refine ⟨k+1, le_rfl, ?_⟩
      intro i hi
      by_cases hi' : i ≤ k
      · exact le_trans (hmax i hi') (le_of_lt (lt_of_not_ge h))
      · have he : i = k+1 := by omega
        simp [he]

/-- The cube of n times the record's coefficient dominates the square
    of the record value. This uses the actual orbit, not a parity model. -/
theorem record_square_bound (n j : ℕ) (hinj : Function.Injective (orbit n))
    (hmax : ∀ i < j, orbit n i ≤ orbit n j) :
    (orbit n j : ℚ)^2 ≤ (coefficient n j * (n : ℚ))^3 := by
  have hj := injective_avoids_small n hinj j
  have hjq : 0 < (orbit n j : ℚ) := by exact_mod_cast (show 0 < orbit n j by omega)
  have hp := orbit_product_bound n j (fun i _ => injective_avoids_small n hinj i)
  have hd := distinct_visit_product n j (orbit n j) (by omega) hinj hmax
  have hc : 0 ≤ coefficient n j := by unfold coefficient; positivity
  have hb : (orbit n j : ℚ)^3 ≤ (coefficient n j * (n : ℚ))^3 * (orbit n j : ℚ) :=
    le_trans hp (mul_le_mul_of_nonneg_left hd (by positivity))
  by_contra! h
  have hh := mul_lt_mul_of_pos_right h hjq
  nlinarith

/-- Quantitative necessary coefficient growth for an injective orbit. -/
theorem prefix_coefficient_growth (n k : ℕ) (hinj : Function.Injective (orbit n)) :
    ∃ j ≤ k, (k : ℚ)^2 ≤ (coefficient n j * (n : ℚ))^3 := by
  obtain ⟨j, hj, hmax⟩ := exists_prefix_max n k
  let f : Fin (k+1) → Fin (orbit n j+1) := fun i =>
    ⟨orbit n i.val, by have hi := i.isLt; have hm := hmax i.val (by omega); omega⟩
  have hf : Function.Injective f := by
    intro i l he
    apply Fin.ext
    apply hinj
    exact congrArg Fin.val he
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  have hk : k ≤ orbit n j := by omega
  have hkq : (k : ℚ) ≤ (orbit n j : ℚ) := by exact_mod_cast hk
  have hpow : (k : ℚ)^2 ≤ (orbit n j : ℚ)^2 := by
    gcongr <;> first | exact hkq | positivity
  exact ⟨j, hj, le_trans hpow (record_square_bound n j hinj (fun i hi => hmax i (by omega)))⟩

/-- No globally bounded coefficient is possible for an injective orbit.
    Natural bounds suffice because every finite real bound has a natural upper bound. -/
theorem injective_coefficient_unbounded (n C : ℕ) (hinj : Function.Injective (orbit n)) :
    ∃ j, (C : ℚ) < coefficient n j := by
  by_contra! h
  let k := (C*n)^3+1
  obtain ⟨j, _, hg⟩ := prefix_coefficient_growth n k hinj
  have hc : 0 ≤ coefficient n j := by unfold coefficient; positivity
  have hjle : coefficient n j ≤ (C : ℚ) := h j
  have hbase := mul_le_mul_of_nonneg_right hjle (show 0 ≤ (n : ℚ) by positivity)
  have hbase0 : 0 ≤ coefficient n j * (n : ℚ) := by positivity
  have hp : (coefficient n j * (n : ℚ))^3 ≤ ((C : ℚ)*(n : ℚ))^3 := by
    gcongr <;> assumption
  have hk : (k : ℚ) = ((C : ℚ)*(n : ℚ))^3+1 := by
    simp [k, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  have hk1 : (1 : ℚ) ≤ (k : ℚ) := by
    rw [hk]
    have hh : 0 ≤ ((C : ℚ)*(n : ℚ))^3 := by positivity
    linarith
  have hk0 : (0 : ℚ) ≤ (k : ℚ) := by positivity
  have hs : (k : ℚ) ≤ (k : ℚ)^2 := by
    nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk1)]
  linarith

#print axioms coefficient_step
#print axioms major_ge_one
#print axioms cubic_step_bound
#print axioms major_range
#print axioms orbit_product_bound
#print axioms distinct_visit_product
#print axioms injective_avoids_small
#print axioms exists_prefix_max
#print axioms record_square_bound
#print axioms prefix_coefficient_growth
#print axioms injective_coefficient_unbounded

end CollatzRunyan.BoundedCoefficientRigidity
