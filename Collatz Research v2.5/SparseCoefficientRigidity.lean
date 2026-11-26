import Mathlib

/-!
# Sparse coefficient rigidity — candidate
Nine-power correction over the actual distinct odd, three-free visits.
The final statement concerns injective shortcut orbits starting three-free.
Not a proof of the Collatz conjecture. Candidate, not yet compiled.
-/
namespace CollatzRunyan.SparseCoefficientRigidity

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

theorem coefficient_step (n k : ℕ) :
    coefficient n (k+1) = coefficient n k * factor (orbit n k) := by
  by_cases h : orbit n k % 2 = 0
  · simp only [coefficient, oddCount, factor, if_pos h, pow_succ]
    rw [div_mul_div_comm, mul_one]
  · simp only [coefficient, oddCount, factor, if_neg h, pow_succ]
    rw [div_mul_div_comm]


/-- A nonmultiple of three stays a nonmultiple of three. -/
theorem shortcut_three_free (x : ℕ) (h3 : x % 3 ≠ 0) :
    shortcut x % 3 ≠ 0 := by
  by_cases h : x % 2 = 0
  · simp only [shortcut, if_pos h]
    omega
  · simp only [shortcut, if_neg h]
    omega

theorem orbit_three_free (n : ℕ) (h3 : n % 3 ≠ 0) (k : ℕ) :
    orbit n k % 3 ≠ 0 := by
  induction k with
  | zero => simpa [orbit] using h3
  | succ k ih => exact shortcut_three_free (orbit n k) ih

/-- Odd three-free integers have at most one representative per rank x/3. -/
theorem odd_rank_injective (x y : ℕ) (hx : x % 2 ≠ 0) (hy : y % 2 ≠ 0)
    (hx3 : x % 3 ≠ 0) (hy3 : y % 3 ≠ 0) (h : x / 3 = y / 3) : x = y := by
  omega

theorem odd_rank_bounds (x : ℕ) (hx : 2 ≤ x) (ho : x % 2 ≠ 0)
    (h3 : x % 3 ≠ 0) : 1 ≤ x / 3 ∧ 3*(x/3)+1 ≤ x := by
  omega

def rankMajor (r : ℕ) : ℚ :=
  if r = 0 then 1 else (3*(r : ℚ)+2)/(3*(r : ℚ)-1)

def major (x : ℕ) : ℚ :=
  if x % 2 = 0 then 1 else rankMajor (x/3)

theorem rank_major_ge_one (r : ℕ) : 1 ≤ rankMajor r := by
  by_cases h : r = 0
  · simp [rankMajor, h]
  · have hr : (1 : ℚ) ≤ (r : ℚ) := by exact_mod_cast (show 1 ≤ r by omega)
    rw [rankMajor, if_neg h]
    apply (le_div_iff₀ (by linarith : 0 < 3*(r : ℚ)-1)).2
    linarith

theorem major_ge_one (x : ℕ) : 1 ≤ major x := by
  by_cases h : x % 2 = 0
  · simp [major, h]
  · simpa [major, h] using rank_major_ge_one (x/3)

/-- The product telescopes over ranks, including rank zero of weight one. -/
theorem rank_major_range (R : ℕ) :
    (∏ r ∈ Finset.range (R+1), rankMajor r) = (3*(R : ℚ)+2)/2 := by
  induction R with
  | zero => norm_num [Finset.prod_range_succ, rankMajor]
  | succ R ih =>
    have h : R+1 ≠ 0 := by omega
    rw [Finset.prod_range_succ, ih, rankMajor, if_neg h, Nat.cast_succ]
    have hd : 3*((R : ℚ)+1)-1 = 3*(R : ℚ)+2 := by ring
    rw [hd]
    have hn : (3*(R : ℚ)+2) ≠ 0 := by positivity
    field_simp [hn] <;> ring

/-- Ninth power correction at a real visit, charged to its lower rank. -/
theorem ranked_nine_bound (L x : ℚ) (hL : 2 ≤ L) (hx : L ≤ x) :
    (3*x+1)^9*(L-2) ≤ (3*x)^9*(L+1) := by
  have hx0 : 0 ≤ x := by linarith
  have hx3 : 0 ≤ 3*x := by positivity
  have hpow : (3*x)^9 ≤ (3*x+1)^9 := by gcongr <;> linarith
  have hbase : 0 ≤ (3*x)^9*(x+1)-(3*x+1)^9*(x-2) := by
    rw [show (3*x)^9*(x+1)-(3*x+1)^9*(x-2) =
      39366*x^8+96228*x^7+91854*x^6+51030*x^5+18144*x^4+
      4212*x^3+621*x^2+53*x+2 by ring]
    positivity
  have hgap := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hpow)
  apply sub_nonneg.mp
  calc
    0 ≤ ((3*x)^9*(x+1)-(3*x+1)^9*(x-2)) +
        (x-L)*((3*x+1)^9-(3*x)^9) := add_nonneg hbase hgap
    _ = (3*x)^9*(L+1)-(3*x+1)^9*(L-2) := by ring

theorem ninth_step_bound (x : ℕ) (hx : 2 ≤ x) (h3 : x % 3 ≠ 0) :
    (shortcut x : ℚ)^9 ≤ (factor x)^9 * (x : ℚ)^9 * major x := by
  by_cases h : x % 2 = 0
  · have he : 2*shortcut x = x := by
      simp only [shortcut, if_pos h]
      omega
    have heq : (2 : ℚ)*(shortcut x : ℚ) = (x : ℚ) := by exact_mod_cast he
    have ht : (shortcut x : ℚ) = (1/2 : ℚ)*(x : ℚ) := by linarith
    rw [ht, factor, if_pos h, major, if_pos h, mul_pow, mul_one]
  · have ho : 2*shortcut x = 3*x+1 := by
      simp only [shortcut, if_neg h]
      omega
    have hoq : (2 : ℚ)*(shortcut x : ℚ) = 3*(x : ℚ)+1 := by exact_mod_cast ho
    have ht : (shortcut x : ℚ) = (3*(x : ℚ)+1)/2 := by linarith
    obtain ⟨hr, hlow⟩ := odd_rank_bounds x hx h h3
    have hrq : (1 : ℚ) ≤ ((x/3 : ℕ) : ℚ) := by exact_mod_cast hr
    have hlq : 3*((x/3 : ℕ) : ℚ)+1 ≤ (x : ℚ) := by exact_mod_cast hlow
    have hbound := ranked_nine_bound (3*((x/3 : ℕ) : ℚ)+1) (x : ℚ) (by linarith) hlq
    rw [show 3*((x/3 : ℕ) : ℚ)+1-2 = 3*((x/3 : ℕ) : ℚ)-1 by ring,
      show 3*((x/3 : ℕ) : ℚ)+1+1 = 3*((x/3 : ℕ) : ℚ)+2 by ring] at hbound
    have hn : x/3 ≠ 0 := by omega
    rw [ht, factor, if_neg h, major, if_neg h, rankMajor, if_neg hn, ← mul_div_assoc]
    apply (le_div_iff₀ (by linarith : 0 < 3*((x/3 : ℕ) : ℚ)-1)).2
    calc
      _ = ((3*(x : ℚ)+1)^9*(3*((x/3 : ℕ) : ℚ)-1))/2^9 := by ring
      _ ≤ ((3*(x : ℚ))^9*(3*((x/3 : ℕ) : ℚ)+2))/2^9 :=
        div_le_div_of_nonneg_right hbound (by norm_num)
      _ = _ := by ring

theorem orbit_product_bound (n k : ℕ) (hthree : n % 3 ≠ 0)
    (hsmall : ∀ j < k, 2 ≤ orbit n j) :
    (orbit n k : ℚ)^9 ≤ (coefficient n k * (n : ℚ))^9 *
      (∏ j ∈ Finset.range k, major (orbit n j)) := by
  induction k with
  | zero => simp [orbit, coefficient, oddCount]
  | succ k ih =>
    have hi := ih (fun j hj => hsmall j (by omega))
    have hs := ninth_step_bound (orbit n k) (hsmall k (by omega)) (orbit_three_free n hthree k)
    have hf : 0 ≤ factor (orbit n k) := by unfold factor; split <;> norm_num
    have hm : 0 ≤ major (orbit n k) := le_trans (by norm_num) (major_ge_one _)
    rw [coefficient_step, Finset.prod_range_succ]
    change (shortcut (orbit n k) : ℚ)^9 ≤ _
    calc
      _ ≤ (factor (orbit n k))^9 * (orbit n k : ℚ)^9 * major (orbit n k) := hs
      _ ≤ (factor (orbit n k))^9 * ((coefficient n k * (n : ℚ))^9 *
          (∏ j ∈ Finset.range k, major (orbit n j))) * major (orbit n k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (pow_nonneg hf _)) hm
      _ = _ := by ring


/-- Only odd visits are charged; each odd three-free rank appears once. -/
theorem distinct_visit_product (n k R : ℕ) (hR : 2 ≤ R)
    (hthree : n % 3 ≠ 0) (hinj : Function.Injective (orbit n))
    (hmax : ∀ j < k, orbit n j ≤ R) :
    (∏ j ∈ Finset.range k, major (orbit n j)) ≤ (R : ℚ) := by
  classical
  let s := (Finset.range k).filter (fun j => orbit n j % 2 ≠ 0)
  let ranks := s.image (fun j => orbit n j / 3)
  have hs : ranks ⊆ Finset.range (R/3+1) := by
    intro r hr
    change r ∈ s.image (fun j => orbit n j / 3) at hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    have hjk : j < k := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    exact Finset.mem_range.mpr (by have h := hmax j hjk; omega)
  have he : (∏ r ∈ ranks, rankMajor r) = ∏ j ∈ s, rankMajor (orbit n j / 3) := by
    apply Finset.prod_image
    intro i hi j hj hij
    apply hinj
    exact odd_rank_injective _ _ (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
      (orbit_three_free n hthree i) (orbit_three_free n hthree j) hij
  have hf : (∏ j ∈ s, rankMajor (orbit n j / 3)) =
      ∏ j ∈ Finset.range k, major (orbit n j) := by
    dsimp [s]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases h : orbit n j % 2 = 0 <;> simp [major, h]
  have hp (t : Finset ℕ) : (1 : ℚ) ≤ ∏ r ∈ t, rankMajor r := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert r t hr ih =>
      rw [Finset.prod_insert hr]
      have hm := rank_major_ge_one r
      have ht : 0 ≤ ∏ x ∈ t, rankMajor x := le_trans (by norm_num) ih
      calc
        1 ≤ ∏ x ∈ t, rankMajor x := ih
        _ = 1 * (∏ x ∈ t, rankMajor x) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hm ht
  have hd : (∏ r ∈ Finset.range (R/3+1) \ ranks, rankMajor r) *
      (∏ r ∈ ranks, rankMajor r) =
      ∏ r ∈ Finset.range (R/3+1), rankMajor r := Finset.prod_sdiff hs
  have hle : (∏ r ∈ ranks, rankMajor r) ≤ ∏ r ∈ Finset.range (R/3+1), rankMajor r := by
    rw [← hd]
    calc
      _ = 1 * (∏ r ∈ ranks, rankMajor r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hp _) (le_trans (by norm_num) (hp ranks))
  rw [he, hf] at hle
  rw [rank_major_range] at hle
  have hfloor : 3*((R/3 : ℕ) : ℚ) ≤ (R : ℚ) := by
    exact_mod_cast (show 3*(R/3) ≤ R by omega)
  have hRq : (2 : ℚ) ≤ (R : ℚ) := by exact_mod_cast hR
  exact le_trans hle (by linarith)

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


/-- Actual record bound on a three-free injective orbit. -/
theorem record_eighth_bound (n j : ℕ) (hthree : n % 3 ≠ 0)
    (hinj : Function.Injective (orbit n)) (hmax : ∀ i < j, orbit n i ≤ orbit n j) :
    (orbit n j : ℚ)^8 ≤ (coefficient n j * (n : ℚ))^9 := by
  have hj := injective_avoids_small n hinj j
  have hjq : 0 < (orbit n j : ℚ) := by exact_mod_cast (show 0 < orbit n j by omega)
  have hp := orbit_product_bound n j hthree (fun i _ => injective_avoids_small n hinj i)
  have hd := distinct_visit_product n j (orbit n j) hj hthree hinj hmax
  have hc : 0 ≤ coefficient n j := by unfold coefficient; positivity
  have hb : (orbit n j : ℚ)^9 ≤ (coefficient n j * (n : ℚ))^9 * (orbit n j : ℚ) :=
    le_trans hp (mul_le_mul_of_nonneg_left hd (by positivity))
  by_contra! h
  have hh := mul_lt_mul_of_pos_right h hjq
  have he : (orbit n j : ℚ)^8 * (orbit n j : ℚ) = (orbit n j : ℚ)^9 := by ring
  rw [he] at hh
  exact (not_lt_of_ge hb) hh

theorem prefix_coefficient_growth (n k : ℕ) (hthree : n % 3 ≠ 0) (hinj : Function.Injective (orbit n)) :
    ∃ j ≤ k, (k : ℚ)^8 ≤ (coefficient n j * (n : ℚ))^9 := by
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
  have hpow : (k : ℚ)^8 ≤ (orbit n j : ℚ)^8 := by
    gcongr <;> first | exact hkq | positivity
  exact ⟨j, hj, le_trans hpow (record_eighth_bound n j hthree hinj (fun i hi => hmax i (by omega)))⟩


#print axioms coefficient_step
#print axioms shortcut_three_free
#print axioms orbit_three_free
#print axioms odd_rank_injective
#print axioms odd_rank_bounds
#print axioms rank_major_ge_one
#print axioms major_ge_one
#print axioms rank_major_range
#print axioms ranked_nine_bound
#print axioms ninth_step_bound
#print axioms orbit_product_bound
#print axioms distinct_visit_product
#print axioms injective_avoids_small
#print axioms exists_prefix_max
#print axioms record_eighth_bound
#print axioms prefix_coefficient_growth

end CollatzRunyan.SparseCoefficientRigidity
