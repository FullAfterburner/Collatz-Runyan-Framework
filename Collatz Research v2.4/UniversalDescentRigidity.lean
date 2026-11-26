import Mathlib

/-!
# Distinct odd visits and universal descent research
Standalone integer arithmetic. The caller supplies the ranked odd visits
and the multiplicative trajectory identity. Sorting the odd visits of an
actual trajectory and proving that identity are not formalized here.
This does not assert universal descent.
-/
namespace CollatzRunyan.UniversalDescentRigidity

/-- Exact polynomial certificate for the sixth-power correction bound. -/
theorem correction_six_identity (x : ℤ) :
    (3*x)^6*(x+1)-(3*x+1)^6*(x-1) =
      243*x^5+675*x^4+405*x^3+117*x^2+17*x+1 := by
  ring

theorem correction_six_bound (x : ℤ) (hx : 0 ≤ x) :
    (3*x+1)^6*(x-1) ≤ (3*x)^6*(x+1) := by
  have hp : 0 ≤ 243*x^5+675*x^4+405*x^3+117*x^2+17*x+1 := by
    positivity
  rw [← correction_six_identity] at hp
  exact sub_nonneg.mp hp

/-- A correction at x is bounded using any smaller positive rank L. -/
theorem ranked_correction_bound (L x : ℤ) (hL : 1 ≤ L) (hx : L ≤ x) :
    (3*x+1)^6*(L-1) ≤ (3*x)^6*(L+1) := by
  have hx0 : 0 ≤ x := by omega
  have hx3 : 0 ≤ 3*x := by omega
  have hpow : (3*x)^6 ≤ (3*x+1)^6 := by
    gcongr <;> omega
  have hgap := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hpow)
  have hbase := correction_six_bound x hx0
  have h : 0 ≤ (3*x)^6*(L+1)-(3*x+1)^6*(L-1) := by
    calc
      0 ≤ ((3*x)^6*(x+1)-(3*x+1)^6*(x-1)) +
          (x-L)*((3*x+1)^6-(3*x)^6) :=
        add_nonneg (sub_nonneg.mpr hbase) hgap
      _ = _ := by ring
  exact sub_nonneg.mp h

def visitProduct (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n+1 => visitProduct f n * f n

theorem visitProduct_pos (f : ℕ → ℤ) (a : ℕ)
    (hf : ∀ i, i < a → 0 < f i) : 0 < visitProduct f a := by
  induction a with
  | zero => norm_num [visitProduct]
  | succ a ih =>
    exact mul_pos (ih (fun i hi => hf i (by omega))) (hf a (by omega))

theorem visitProduct_pow (f : ℕ → ℤ) (a e : ℕ) :
    visitProduct (fun i => f i ^ e) a = visitProduct f a ^ e := by
  induction a with
  | zero => simp [visitProduct]
  | succ a ih => simp only [visitProduct, ih, mul_pow]

/-- Telescoping envelope for odd visits sorted by increasing value.
The rank inequality is an explicit hypothesis. -/
theorem ranked_product_envelope (m : ℤ) (x : ℕ → ℤ) (a : ℕ)
    (hm : 2 ≤ m) (hx : ∀ i, i < a → m+2*(i : ℤ) ≤ x i) :
    (m-1)*visitProduct (fun i => (3*x i+1)^6) a ≤
      (m+2*(a : ℤ)-1)*visitProduct (fun i => (3*x i)^6) a := by
  induction a with
  | zero => simp [visitProduct]
  | succ a ih =>
    have hp := ih (fun i hi => hx i (by omega))
    have hL : 1 ≤ m+2*(a : ℤ) := by omega
    have hstep := ranked_correction_bound (m+2*(a : ℤ)) (x a) hL
      (hx a (by omega))
    have hxa : 0 ≤ x a := by have h := hx a (by omega); omega
    have hnum : 0 ≤ (3*x a+1)^6 := by positivity
    have hden : 0 ≤ visitProduct (fun i => (3*x i)^6) a := by
      apply le_of_lt
      apply visitProduct_pos
      intro i hi
      have hxi : 0 < x i := by have h := hx i (by omega); omega
      positivity
    simp only [visitProduct, Nat.cast_succ]
    calc
      (m-1)*(visitProduct (fun i => (3*x i+1)^6) a * (3*x a+1)^6) =
          ((m-1)*visitProduct (fun i => (3*x i+1)^6) a)*(3*x a+1)^6 := by ring
      _ ≤ ((m+2*(a : ℤ)-1)*visitProduct (fun i => (3*x i)^6) a)*(3*x a+1)^6 :=
        mul_le_mul_of_nonneg_right hp hnum
      _ = visitProduct (fun i => (3*x i)^6) a * ((3*x a+1)^6*(m+2*(a : ℤ)-1)) := by ring
      _ ≤ visitProduct (fun i => (3*x i)^6) a * ((3*x a)^6*(m+2*(a : ℤ)+1)) :=
        mul_le_mul_of_nonneg_left hstep hden
      _ = _ := by ring

/-- A non-descending multiplicative balance implies the polynomial envelope. -/
theorem nondescending_coefficient_bound (M A m : ℤ) (x : ℕ → ℤ) (a : ℕ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hm : 2 ≤ m)
    (hx : ∀ i, i < a → m+2*(i : ℤ) ≤ x i)
    (hbalance : M*visitProduct (fun i => 3*x i) a ≤
      A*visitProduct (fun i => 3*x i+1) a) :
    M^6*(m-1) ≤ A^6*(m+2*(a : ℤ)-1) := by
  have hv : 0 < visitProduct (fun i => 3*x i) a := by
    apply visitProduct_pos
    intro i hi
    have h := hx i hi
    omega
  have hv6 : 0 < visitProduct (fun i => (3*x i)^6) a := by
    rw [visitProduct_pow]
    positivity
  have hleft : 0 ≤ M*visitProduct (fun i => 3*x i) a :=
    mul_nonneg hM hv.le
  have hp : (M*visitProduct (fun i => 3*x i) a)^6 ≤
      (A*visitProduct (fun i => 3*x i+1) a)^6 := by gcongr
  rw [mul_pow, mul_pow, ← visitProduct_pow (fun i => 3*x i) a 6,
    ← visitProduct_pow (fun i => 3*x i+1) a 6] at hp
  have he := ranked_product_envelope m x a hm hx
  have hm0 : 0 ≤ m-1 := by omega
  have hA6 : 0 ≤ A^6 := by positivity
  have hc : (M^6*(m-1))*visitProduct (fun i => (3*x i)^6) a ≤
      (A^6*(m+2*(a : ℤ)-1))*visitProduct (fun i => (3*x i)^6) a := by
    calc
      _ = (m-1)*(M^6*visitProduct (fun i => (3*x i)^6) a) := by ring
      _ ≤ (m-1)*(A^6*visitProduct (fun i => (3*x i+1)^6) a) :=
        mul_le_mul_of_nonneg_left hp hm0
      _ = A^6*((m-1)*visitProduct (fun i => (3*x i+1)^6) a) := by ring
      _ ≤ A^6*((m+2*(a : ℤ)-1)*visitProduct (fun i => (3*x i)^6) a) :=
        mul_le_mul_of_nonneg_left he hA6
      _ = _ := by ring
  by_contra! hn
  exact (not_lt_of_ge hc) (mul_lt_mul_of_pos_right hn hv6)

/-- A strict violation of the envelope forces the endpoint below the start. -/
theorem distinct_visit_descent (M A m y : ℤ) (x : ℕ → ℤ) (a : ℕ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hm : 2 ≤ m)
    (hx : ∀ i, i < a → m+2*(i : ℤ) ≤ x i)
    (hidentity : M*y*visitProduct (fun i => 3*x i) a =
      A*m*visitProduct (fun i => 3*x i+1) a)
    (hgap : A^6*(m+2*(a : ℤ)-1) < M^6*(m-1)) : y < m := by
  by_contra! hy
  have hv : 0 < visitProduct (fun i => 3*x i) a := by
    apply visitProduct_pos
    intro i hi
    have h := hx i hi
    omega
  have hmpos : 0 < m := by omega
  have hb : (M*visitProduct (fun i => 3*x i) a)*m ≤
      (A*visitProduct (fun i => 3*x i+1) a)*m := by
    calc
      _ = M*m*visitProduct (fun i => 3*x i) a := by ring
      _ ≤ M*y*visitProduct (fun i => 3*x i) a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy hM) hv.le
      _ = A*m*visitProduct (fun i => 3*x i+1) a := hidentity
      _ = _ := by ring
  have hbalance : M*visitProduct (fun i => 3*x i) a ≤
      A*visitProduct (fun i => 3*x i+1) a := by
    by_contra! hn
    exact (not_lt_of_ge hb) (mul_lt_mul_of_pos_right hn hmpos)
  exact (not_lt_of_ge (nondescending_coefficient_bound M A m x a hM hA hm hx hbalance)) hgap

end CollatzRunyan.UniversalDescentRigidity

#print axioms CollatzRunyan.UniversalDescentRigidity.correction_six_identity
#print axioms CollatzRunyan.UniversalDescentRigidity.correction_six_bound
#print axioms CollatzRunyan.UniversalDescentRigidity.ranked_correction_bound
#print axioms CollatzRunyan.UniversalDescentRigidity.visitProduct_pos
#print axioms CollatzRunyan.UniversalDescentRigidity.visitProduct_pow
#print axioms CollatzRunyan.UniversalDescentRigidity.ranked_product_envelope
#print axioms CollatzRunyan.UniversalDescentRigidity.nondescending_coefficient_bound
#print axioms CollatzRunyan.UniversalDescentRigidity.distinct_visit_descent
