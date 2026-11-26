import Mathlib

/-!
# Family correction product — candidate
An elementary rational product estimate for the representative set of
FamilyCoalescenceRigidity. No logarithms or nonstandard axioms are used.
This standalone module targets P(R)^32 <= R^3 for positive natural R.
The link to the actual injective orbit is a separate formalization step.
Not yet compiled in Lean.
-/
namespace CollatzRunyan.FamilyCorrectionProduct

open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 512

def allowedResidues : Finset ℕ :=
  (Finset.range 96).filter (fun r => r%2 ≠ 0 ∧ r%3 ≠ 0 ∧ r%24 ≠ 5 ∧ r ≠ 85)

def correction (x : ℕ) : ℚ := 1 + 1/(3*(x : ℚ))

def weight (x : ℕ) : ℚ :=
  if 5 ≤ x ∧ x%2 ≠ 0 ∧ x%3 ≠ 0 ∧ (x = 5 ∨ x%24 ≠ 5) ∧ x%96 ≠ 85
  then correction x else 1

/-- Product of weights at the integers strictly below N. -/
def prefixProduct : ℕ → ℚ
  | 0 => 1
  | n+1 => prefixProduct n * weight n

def block (q : ℕ) : ℚ :=
  ∏ r ∈ allowedResidues, correction (96*q+r)

theorem allowed_residue_card : allowedResidues.card = 27 := by decide

theorem correction_ge_one (x : ℕ) : 1 ≤ correction x := by
  unfold correction
  have h : (0 : ℚ) ≤ 1/(3*(x : ℚ)) := by positivity
  linarith

theorem weight_ge_one (x : ℕ) : 1 ≤ weight x := by
  unfold weight
  split
  · exact correction_ge_one x
  · exact le_rfl

theorem prefix_ge_one (N : ℕ) : 1 ≤ prefixProduct N := by
  induction N with
  | zero => simp [prefixProduct]
  | succ N ih =>
    change 1 ≤ prefixProduct N * weight N
    calc
      1 ≤ prefixProduct N := ih
      _ = prefixProduct N * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (weight_ge_one N) (by linarith)

theorem prefix_mono (a b : ℕ) (h : a ≤ b) : prefixProduct a ≤ prefixProduct b := by
  induction b with
  | zero =>
    have he : a = 0 := by omega
    simp [he]
  | succ b ih =>
    by_cases he : a = b+1
    · simp [he]
    · have hb : a ≤ b := by omega
      calc
        prefixProduct a ≤ prefixProduct b := ih hb
        _ = prefixProduct b * 1 := by ring
        _ ≤ prefixProduct (b+1) := by
          change prefixProduct b * 1 ≤ prefixProduct b * weight b
          exact mul_le_mul_of_nonneg_left (weight_ge_one b) (by linarith [prefix_ge_one b])

theorem prefix_add (a b : ℕ) :
    prefixProduct (a+b) = prefixProduct a * (∏ r ∈ Finset.range b, weight (a+r)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ]
    change prefixProduct (a+b) * weight (a+b) = _
    rw [ih] <;> ring

/-- A positive block contains precisely the 27 allowed residue positions. -/
theorem positive_block (q : ℕ) (hq : 1 ≤ q) :
    prefixProduct (96*(q+1)) = prefixProduct (96*q) * block q := by
  rw [show 96*(q+1) = 96*q+96 by omega, prefix_add, block, allowedResidues, Finset.prod_filter]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  have hr96 : r < 96 := Finset.mem_range.mp hr
  have hm : (96*q+r)%96 = r := by omega
  have h2 : (96*q+r)%2 = r%2 := by omega
  have h3 : (96*q+r)%3 = r%3 := by omega
  have h24 : (96*q+r)%24 = r%24 := by omega
  have hmin : 5 ≤ 96*q+r := by omega
  have hne : 96*q+r ≠ 5 := by omega
  simp [weight, hm, h2, h3, h24, hmin, hne]

/-- An elementary symmetric bound for integer powers. -/
theorem symmetric_power (t : ℚ) (m : ℕ) (ht : 0 ≤ t)
    (h : (m : ℚ)*t < 2) :
    (1+t)^m ≤ (2+(m : ℚ)*t)/(2-(m : ℚ)*t) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    simp only [Nat.cast_succ] at h ⊢
    have hm : (m : ℚ)*t < 2 := by nlinarith
    have hd0 : 0 < 2-(m : ℚ)*t := sub_pos.mpr hm
    have hd1 : 0 < 2-((m : ℚ)+1)*t := sub_pos.mpr h
    rw [pow_succ]
    calc
      _ ≤ ((2+(m : ℚ)*t)/(2-(m : ℚ)*t))*(1+t) :=
        mul_le_mul_of_nonneg_right (ih hm) (by linarith)
      _ = ((2+(m : ℚ)*t)*(1+t))/(2-(m : ℚ)*t) := by ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ hd0 hd1).2
        have hn : 0 ≤ t^2*((m : ℚ)^2*t+(m : ℚ)*t+2) := by positivity
        nlinarith only [hn]

def uniform (q : ℕ) : ℚ := 1+1/(288*(q : ℚ))

theorem uniform_ge_one (q : ℕ) : 1 ≤ uniform q := by
  unfold uniform
  have h : (0 : ℚ) ≤ 1/(288*(q : ℚ)) := by positivity
  linarith

theorem correction_block_bound (q r : ℕ) (hq : 1 ≤ q) :
    correction (96*q+r) ≤ uniform q := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (show 0 < q by omega)
  have hden : (288 : ℚ)*(q : ℚ) ≤ 3*((96*q+r : ℕ) : ℚ) := by
    push_cast
    linarith [show (0 : ℚ) ≤ (r : ℚ) by positivity]
  have hp : (0 : ℚ) < 288*(q : ℚ) := by positivity
  unfold correction uniform
  exact add_le_add_left (one_div_le_one_div_of_le hp hden) 1

theorem block_bound (q : ℕ) (hq : 1 ≤ q) : block q ≤ (uniform q)^27 := by
  unfold block
  calc
    _ ≤ ∏ r ∈ allowedResidues, uniform q := by
      apply Finset.prod_le_prod
      · intro r hr
        exact le_trans (by norm_num) (correction_ge_one _)
      · intro r hr
        exact correction_block_bound q r hq
    _ = _ := by rw [Finset.prod_const, allowed_residue_card]

/-- The exponent 288 is exactly 32*27/3. -/
theorem uniform_power_bound (q : ℕ) (hq : 1 ≤ q) :
    (uniform q)^288 ≤ (2*(q : ℚ)+1)/(2*(q : ℚ)-1) := by
  have hq' : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have ht : (0 : ℚ) ≤ 1/(288*(q : ℚ)) := by positivity
  have he : (288 : ℚ)*(1/(288*(q : ℚ))) = 1/(q : ℚ) := by
    field_simp [ne_of_gt (show (0 : ℚ) < (q : ℚ) by linarith)]
  have hlt : (288 : ℚ)*(1/(288*(q : ℚ))) < 2 := by
    rw [he]
    apply (div_lt_iff₀ (show (0 : ℚ) < (q : ℚ) by linarith)).2
    linarith
  have hp := symmetric_power (1/(288*(q : ℚ))) 288 ht (by simpa using hlt)
  change (uniform q)^288 ≤ (2+(288 : ℚ)*(1/(288*(q : ℚ))))/(2-(288 : ℚ)*(1/(288*(q : ℚ)))) at hp
  rw [he] at hp
  have hratio : (2+1/(q : ℚ))/(2-1/(q : ℚ)) = (2*(q : ℚ)+1)/(2*(q : ℚ)-1) := by
    have hpos : (0 : ℚ) < (q : ℚ) := by linarith
    have hden : (0 : ℚ) < 2*(q : ℚ)-1 := by linarith
    have hden' : (0 : ℚ) < 2-1/(q : ℚ) := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hq'
      norm_num at h
      linarith
    field_simp [ne_of_gt hpos, ne_of_gt hden, ne_of_gt hden']
  simpa only [hratio] using hp

theorem block_ge_one (q : ℕ) : 1 ≤ block q := by
  unfold block
  have h : ∀ s : Finset ℕ, (1 : ℚ) ≤ ∏ r ∈ s, correction (96*q+r) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert r s hr ih =>
      rw [Finset.prod_insert hr]
      calc
        1 ≤ ∏ x ∈ s, correction (96*q+x) := ih
        _ = 1*(∏ x ∈ s, correction (96*q+x)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (correction_ge_one _) (by linarith)
  exact h _

theorem block_power_bound (q : ℕ) (hq : 1 ≤ q) :
    (block q)^32 ≤ ((2*(q : ℚ)+1)/(2*(q : ℚ)-1))^3 := by
  have h0 : 0 ≤ block q := by linarith [block_ge_one q]
  have h1 : 0 ≤ uniform q := by linarith [uniform_ge_one q]
  have hb := block_bound q hq
  have hu := uniform_power_bound q hq
  calc
    _ ≤ ((uniform q)^27)^32 := by gcongr
    _ = ((uniform q)^288)^3 := by rw [← pow_mul, ← pow_mul] <;> norm_num
    _ ≤ _ := by gcongr

/-- First complete block certificate, including exceptional representative 5. -/
theorem first_block_bound : (prefixProduct 96)^32 ≤ (40 : ℚ)^3 := by
  norm_num [prefixProduct, weight, correction]

/-- Induction telescopes all complete blocks: the denominator at q
is the numerator at q-1. -/
theorem complete_blocks_bound (q : ℕ) :
    (prefixProduct (96*(q+1)))^32 ≤ (40 : ℚ)^3*(2*(q : ℚ)+1)^3 := by
  induction q with
  | zero => simpa using first_block_bound
  | succ q ih =>
    have hq : 1 ≤ q+1 := by omega
    have hpos : (0 : ℚ) < 2*(q : ℚ)+1 := by positivity
    have hratio : (2*((q+1 : ℕ) : ℚ)+1)/(2*((q+1 : ℕ) : ℚ)-1) =
        (2*(q : ℚ)+3)/(2*(q : ℚ)+1) := by
      push_cast; ring_nf
    have hb := block_power_bound (q+1) hq
    rw [hratio] at hb
    rw [positive_block (q+1) hq, mul_pow]
    calc
      _ ≤ ((40 : ℚ)^3*(2*(q : ℚ)+1)^3)*
          ((2*(q : ℚ)+3)/(2*(q : ℚ)+1))^3 := by
        apply mul_le_mul ih hb (by positivity)
        positivity
      _ = (40 : ℚ)^3*(2*((q+1 : ℕ) : ℚ)+1)^3 := by
        push_cast
        field_simp [ne_of_gt hpos] <;> ring

/-- For R >= 288 the complete-block envelope already implies the
normalized bound, with no logarithmic approximation. -/
theorem large_prefix_bound (R : ℕ) (hR : 288 ≤ R) :
    (prefixProduct (R+1))^32 ≤ (R : ℚ)^3 := by
  let q := R/96
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hfloor : 96*q ≤ R := by dsimp [q]; omega
  have hceil : R+1 ≤ 96*(q+1) := by dsimp [q]; omega
  have hq' : (3 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hf : 96*(q : ℚ) ≤ (R : ℚ) := by exact_mod_cast hfloor
  have hlin : 40*(2*(q : ℚ)+1) ≤ (R : ℚ) := by linarith
  calc
    _ ≤ (prefixProduct (96*(q+1)))^32 := by
      have h := prefix_mono _ _ hceil
      have hn : 0 ≤ prefixProduct (R+1) := by linarith [prefix_ge_one (R+1)]
      gcongr
    _ ≤ (40 : ℚ)^3*(2*(q : ℚ)+1)^3 := complete_blocks_bound q
    _ = (40*(2*(q : ℚ)+1))^3 := by ring
    _ ≤ _ := by gcongr

/-- A finite interval certificate reduces all small records to six
rational endpoint calculations. -/
theorem interval_certificate (R a b : ℕ) (ha : a ≤ R) (hb : R ≤ b)
    (h : (prefixProduct (b+1))^32 ≤ (a : ℚ)^3) :
    (prefixProduct (R+1))^32 ≤ (R : ℚ)^3 := by
  have hp := prefix_mono (R+1) (b+1) (by omega)
  have hn : 0 ≤ prefixProduct (R+1) := by linarith [prefix_ge_one (R+1)]
  have ha' : (a : ℚ) ≤ (R : ℚ) := by exact_mod_cast ha
  calc
    _ ≤ (prefixProduct (b+1))^32 := by gcongr
    _ ≤ (a : ℚ)^3 := h
    _ ≤ _ := by gcongr

theorem small_prefix_bound (R : ℕ) (hR : 1 ≤ R) (hsmall : R < 288) :
    (prefixProduct (R+1))^32 ≤ (R : ℚ)^3 := by
  by_cases h4 : R ≤ 4
  · exact interval_certificate R 1 4 hR h4 (by norm_num [prefixProduct, weight, correction])
  by_cases h12 : R ≤ 12
  · exact interval_certificate R 5 12 (by omega) h12 (by norm_num [prefixProduct, weight, correction])
  by_cases h30 : R ≤ 30
  · exact interval_certificate R 13 30 (by omega) h30 (by norm_num [prefixProduct, weight, correction])
  by_cases h72 : R ≤ 72
  · exact interval_certificate R 31 72 (by omega) h72 (by norm_num [prefixProduct, weight, correction])
  by_cases h174 : R ≤ 174
  · exact interval_certificate R 73 174 (by omega) h174 (by norm_num [prefixProduct, weight, correction])
  · exact interval_certificate R 175 287 (by omega) (by omega) (by norm_num [prefixProduct, weight, correction])

/-- Main product target: the power bound for every positive record. -/
theorem family_product_bound (R : ℕ) (hR : 1 ≤ R) :
    (prefixProduct (R+1))^32 ≤ (R : ℚ)^3 := by
  by_cases h : 288 ≤ R
  · exact large_prefix_bound R h
  · exact small_prefix_bound R hR (by omega)

#print axioms allowed_residue_card
#print axioms correction_ge_one
#print axioms weight_ge_one
#print axioms prefix_ge_one
#print axioms prefix_mono
#print axioms prefix_add
#print axioms positive_block
#print axioms symmetric_power
#print axioms uniform_ge_one
#print axioms correction_block_bound
#print axioms block_bound
#print axioms uniform_power_bound
#print axioms block_ge_one
#print axioms block_power_bound
#print axioms first_block_bound
#print axioms complete_blocks_bound
#print axioms large_prefix_bound
#print axioms interval_certificate
#print axioms small_prefix_bound
#print axioms family_product_bound

end CollatzRunyan.FamilyCorrectionProduct
