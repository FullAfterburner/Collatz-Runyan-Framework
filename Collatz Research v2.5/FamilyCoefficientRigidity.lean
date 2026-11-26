import SparseCoefficientRigidity
import FamilyCoalescenceRigidity
import FamilyCorrectionProduct

/-!
# Family coefficient rigidity (integration candidate)
Uses the three previously audited modules without duplicating their declarations.
Charges actual odd visits to distinct lower family representatives, then applies
 the verified rational product envelope. All conclusions about growth are
conditional on injectivity and a three-free starting value.
-/
namespace CollatzRunyan.FamilyCoefficientRigidity

open scoped BigOperators
open CollatzRunyan.SparseCoefficientRigidity (shortcut orbit factor coefficient oddCount)

local notation "FOrbit" => CollatzRunyan.FamilyCoalescenceRigidity.orbit
local notation "Eligible" => CollatzRunyan.FamilyCoalescenceRigidity.Eligible
local notation "Family" => CollatzRunyan.FamilyCoalescenceRigidity.Family
local notation "correction" => CollatzRunyan.FamilyCorrectionProduct.correction
local notation "weight" => CollatzRunyan.FamilyCorrectionProduct.weight
local notation "prefixProduct" => CollatzRunyan.FamilyCorrectionProduct.prefixProduct

theorem orbit_agreement (n k : ℕ) : FOrbit n k = orbit n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change shortcut (FOrbit n k) = shortcut (orbit n k)
    exact congrArg shortcut ih

noncomputable def representative (x : ℕ) : ℕ := by
  classical
  exact if h : Eligible x then
    Classical.choose (FamilyCoalescenceRigidity.eligible_representative x h)
  else x

theorem representative_spec (x : ℕ) (hx : Eligible x) :
    Eligible (representative x) ∧ Family x (representative x) ∧
      representative x ≤ x ∧
      (representative x = 5 ∨ representative x % 24 ≠ 5) ∧
      representative x % 96 ≠ 85 := by
  classical
  unfold representative
  rw [dif_pos hx]
  exact Classical.choose_spec (FamilyCoalescenceRigidity.eligible_representative x hx)

theorem eligible_odd_visit (n i : ℕ) (hthree : n % 3 ≠ 0)
    (hinj : Function.Injective (orbit n)) (hi : orbit n i % 2 ≠ 0) :
    Eligible (orbit n i) := by
  have hs := SparseCoefficientRigidity.injective_avoids_small n hinj i
  have ht := SparseCoefficientRigidity.orbit_three_free n hthree i
  exact ⟨by omega, hi, ht⟩

theorem representative_visit_injective (n i j : ℕ)
    (hthree : n % 3 ≠ 0) (hinj : Function.Injective (orbit n))
    (hi : orbit n i % 2 ≠ 0) (hj : orbit n j % 2 ≠ 0)
    (he : representative (orbit n i) = representative (orbit n j)) : i = j := by
  have hfi : Function.Injective (FOrbit n) := by
    intro a b hab
    apply hinj
    simpa only [orbit_agreement] using hab
  have ha := (representative_spec _ (eligible_odd_visit n i hthree hinj hi)).2.1
  have hb := (representative_spec _ (eligible_odd_visit n j hthree hinj hj)).2.1
  rw [← he] at hb
  apply FamilyCoalescenceRigidity.shared_family_visit_unique n i j
    (representative (orbit n i)) hfi
  · simpa only [orbit_agreement] using hi
  · simpa only [orbit_agreement] using hj
  · simpa only [orbit_agreement] using ha
  · simpa only [orbit_agreement] using hb

theorem correction_antitone (y x : ℕ) (hy : 0 < y) (hyx : y ≤ x) :
    correction x ≤ correction y := by
  have hyq : (0 : ℚ) < (y : ℚ) := by exact_mod_cast hy
  have hle : (y : ℚ) ≤ (x : ℚ) := by exact_mod_cast hyx
  have hxq : (0 : ℚ) < (x : ℚ) := lt_of_lt_of_le hyq hle
  unfold FamilyCorrectionProduct.correction
  have hd : (1 : ℚ)/(3*(x : ℚ)) ≤ 1/(3*(y : ℚ)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3*(x : ℚ))
      (by positivity : 0 < 3*(y : ℚ))).2
    linarith
  exact add_le_add_left hd 1

theorem representative_weight (x : ℕ) (hx : Eligible x) :
    correction x ≤ weight (representative x) := by
  obtain ⟨hy, _, hle, hfirst, hsecond⟩ := representative_spec x hx
  rcases hy with ⟨hy5, hyodd, hythree⟩
  have hcond : 5 ≤ representative x ∧ representative x % 2 ≠ 0 ∧
      representative x % 3 ≠ 0 ∧
      (representative x = 5 ∨ representative x % 24 ≠ 5) ∧
      representative x % 96 ≠ 85 := ⟨hy5, hyodd, hythree, hfirst, hsecond⟩
  rw [FamilyCorrectionProduct.weight, if_pos hcond]
  exact correction_antitone _ _ (by omega) hle

def visitCorrection (x : ℕ) : ℚ :=
  if x % 2 = 0 then 1 else correction x

theorem shortcut_product_identity (x : ℕ) (hx : 0 < x) :
    (shortcut x : ℚ) = factor x * (x : ℚ) * visitCorrection x := by
  have hxq : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hx
  by_cases h : x % 2 = 0
  · have he : 2*shortcut x = x := by
      simp only [SparseCoefficientRigidity.shortcut, if_pos h]
      omega
    have heq : (2 : ℚ)*(shortcut x : ℚ) = (x : ℚ) := by exact_mod_cast he
    simp only [SparseCoefficientRigidity.factor, visitCorrection, if_pos h, mul_one]
    linarith
  · have ho : 2*shortcut x = 3*x+1 := by
      simp only [SparseCoefficientRigidity.shortcut, if_neg h]
      omega
    have hoq : (2 : ℚ)*(shortcut x : ℚ) = 3*(x : ℚ)+1 := by exact_mod_cast ho
    have ht : (shortcut x : ℚ) = (3*(x : ℚ)+1)/2 := by linarith
    rw [ht]
    simp only [SparseCoefficientRigidity.factor, visitCorrection, if_neg h,
      FamilyCorrectionProduct.correction]
    field_simp [ne_of_gt hxq] <;> ring

theorem orbit_product_identity (n k : ℕ) (hpos : ∀ i < k, 0 < orbit n i) :
    (orbit n k : ℚ) = coefficient n k * (n : ℚ) *
      (∏ i ∈ Finset.range k, visitCorrection (orbit n i)) := by
  induction k with
  | zero => simp [SparseCoefficientRigidity.orbit, SparseCoefficientRigidity.coefficient,
      SparseCoefficientRigidity.oddCount]
  | succ k ih =>
    have he := ih (fun i hi => hpos i (by omega))
    rw [SparseCoefficientRigidity.coefficient_step, Finset.prod_range_succ]
    change (shortcut (orbit n k) : ℚ) = _
    rw [shortcut_product_identity _ (hpos k (by omega)), he]
    ring

theorem prefix_as_product (N : ℕ) :
    prefixProduct N = ∏ x ∈ Finset.range N, weight x := by
  induction N with
  | zero => simp [FamilyCorrectionProduct.prefixProduct]
  | succ N ih =>
    rw [Finset.prod_range_succ]
    change prefixProduct N * weight N = _
    rw [ih]

theorem finite_weight_ge_one (s : Finset ℕ) : (1 : ℚ) ≤ ∏ x ∈ s, weight x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx]
    calc
      1 ≤ ∏ y ∈ s, weight y := ih
      _ = 1 * (∏ y ∈ s, weight y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (FamilyCorrectionProduct.weight_ge_one x)
        (le_trans (by norm_num) ih)

/-- Actual odd-visit correction product is bounded by the verified prefix product. -/
theorem distinct_family_product (n k R : ℕ) (hthree : n % 3 ≠ 0)
    (hinj : Function.Injective (orbit n)) (hmax : ∀ i < k, orbit n i ≤ R) :
    (∏ i ∈ Finset.range k, visitCorrection (orbit n i)) ≤ prefixProduct (R+1) := by
  classical
  let s := (Finset.range k).filter (fun i => orbit n i % 2 ≠ 0)
  let reps := s.image (fun i => representative (orbit n i))
  have hs : reps ⊆ Finset.range (R+1) := by
    intro y hy
    change y ∈ s.image (fun i => representative (orbit n i)) at hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hik := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hodd := (Finset.mem_filter.mp hi).2
    have hrep := (representative_spec _ (eligible_odd_visit n i hthree hinj hodd)).2.2.1
    exact Finset.mem_range.mpr (by have hm := hmax i hik; omega)
  have himage : (∏ y ∈ reps, weight y) =
      ∏ i ∈ s, weight (representative (orbit n i)) := by
    apply Finset.prod_image
    intro i hi j hj he
    exact representative_visit_injective n i j hthree hinj
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 he
  have hfilter : (∏ i ∈ s, correction (orbit n i)) =
      ∏ i ∈ Finset.range k, visitCorrection (orbit n i) := by
    dsimp [s]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : orbit n i % 2 = 0 <;> simp [visitCorrection, h]
  have hcompare : (∏ i ∈ s, correction (orbit n i)) ≤
      ∏ i ∈ s, weight (representative (orbit n i)) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact le_trans (by norm_num) (FamilyCorrectionProduct.correction_ge_one _)
    · intro i hi
      exact representative_weight _ (eligible_odd_visit n i hthree hinj (Finset.mem_filter.mp hi).2)
  have hd : (∏ y ∈ Finset.range (R+1) \ reps, weight y) *
      (∏ y ∈ reps, weight y) = ∏ y ∈ Finset.range (R+1), weight y :=
    Finset.prod_sdiff hs
  have hsub : (∏ y ∈ reps, weight y) ≤ ∏ y ∈ Finset.range (R+1), weight y := by
    rw [← hd]
    calc
      _ = 1 * (∏ y ∈ reps, weight y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (finite_weight_ge_one _)
        (le_trans (by norm_num) (finite_weight_ge_one reps))
  rw [← hfilter, prefix_as_product]
  rw [himage] at hsub
  exact le_trans hcompare hsub

/-- New record inequality, assembled from the audited family and product modules. -/
theorem record_twenty_ninth_bound (n j : ℕ) (hthree : n % 3 ≠ 0)
    (hinj : Function.Injective (orbit n)) (hmax : ∀ i < j, orbit n i ≤ orbit n j) :
    (orbit n j : ℚ)^29 ≤ (coefficient n j * (n : ℚ))^32 := by
  have hj := SparseCoefficientRigidity.injective_avoids_small n hinj j
  have hR : (0 : ℚ) < (orbit n j : ℚ) := by exact_mod_cast (show 0 < orbit n j by omega)
  have he := orbit_product_identity n j (fun i _ =>
    lt_of_lt_of_le (by decide : 0 < 2) (SparseCoefficientRigidity.injective_avoids_small n hinj i))
  have hp := distinct_family_product n j (orbit n j) hthree hinj hmax
  have hc : 0 ≤ coefficient n j * (n : ℚ) := by
    unfold SparseCoefficientRigidity.coefficient
    positivity
  have hb : (orbit n j : ℚ) ≤ coefficient n j * (n : ℚ) * prefixProduct (orbit n j+1) := by
    calc
      _ = _ := he
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hc
  have hpow : (orbit n j : ℚ)^32 ≤
      (coefficient n j * (n : ℚ) * prefixProduct (orbit n j+1))^32 := by gcongr
  rw [mul_pow] at hpow
  have hprod := FamilyCorrectionProduct.family_product_bound (orbit n j) (by omega)
  have hfinal : (orbit n j : ℚ)^32 ≤
      (coefficient n j * (n : ℚ))^32 * (orbit n j : ℚ)^3 :=
    le_trans hpow (mul_le_mul_of_nonneg_left hprod (pow_nonneg hc _))
  by_contra! h
  have hstrict := mul_lt_mul_of_pos_right h (pow_pos hR 3)
  have hidentity : (orbit n j : ℚ)^29 * (orbit n j : ℚ)^3 = (orbit n j : ℚ)^32 := by ring
  rw [hidentity] at hstrict
  exact (not_lt_of_ge hfinal) hstrict

theorem prefix_coefficient_growth (n k : ℕ) (hthree : n % 3 ≠ 0)
    (hinj : Function.Injective (orbit n)) :
    ∃ j ≤ k, (k : ℚ)^29 ≤ (coefficient n j * (n : ℚ))^32 := by
  obtain ⟨j, hj, hmax⟩ := SparseCoefficientRigidity.exists_prefix_max n k
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
  have hpow : (k : ℚ)^29 ≤ (orbit n j : ℚ)^29 := by gcongr
  exact ⟨j, hj, le_trans hpow (record_twenty_ninth_bound n j hthree hinj
    (fun i hi => hmax i (by omega)))⟩

#print axioms orbit_agreement
#print axioms representative_spec
#print axioms eligible_odd_visit
#print axioms representative_visit_injective
#print axioms correction_antitone
#print axioms representative_weight
#print axioms shortcut_product_identity
#print axioms orbit_product_identity
#print axioms prefix_as_product
#print axioms finite_weight_ge_one
#print axioms distinct_family_product
#print axioms record_twenty_ninth_bound
#print axioms prefix_coefficient_growth

end CollatzRunyan.FamilyCoefficientRigidity
