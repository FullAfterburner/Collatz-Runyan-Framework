import Mathlib

/-!
# Logarithmic deficit rigidity
Integer arithmetic for a sorted finite sequence of distinct odd values
not divisible by three. The caller supplies the multiplicative trajectory
identity. The asymptotic logarithmic consequence is not formalized here.
This is not a proof of universal descent.
-/
namespace CollatzRunyan.LogarithmicDeficitRigidity

theorem odd_spacing (x y : ℤ) (hxy : x < y)
    (hx : x % 2 = 1) (hy : y % 2 = 1) : x+2 ≤ y := by
  omega

theorem three_free_spacing (x y z : ℤ) (hxy : x < y) (hyz : y < z)
    (hx : x % 2 = 1) (hy : y % 2 = 1) (hz : z % 2 = 1)
    (hx3 : x % 3 ≠ 0) (hy3 : y % 3 ≠ 0) (hz3 : z % 3 ≠ 0) :
    x+6 ≤ z := by
  have h1 := odd_spacing x y hxy hx hy
  have h2 := odd_spacing y z hyz hy hz
  by_contra! h
  have he1 : y = x+2 := by omega
  have he2 : z = x+4 := by omega
  have hxmod : x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases hxmod with hmod | hmod
  · apply hy3
    rw [he1, Int.add_emod, hmod] <;> norm_num
  · apply hz3
    rw [he2, Int.add_emod, hmod] <;> norm_num

theorem even_index_rank (m : ℤ) (x : ℕ → ℤ) (a : ℕ)
    (h0 : m ≤ x 0) (hpair : ∀ i, i+2 < a → x i+6 ≤ x (i+2))
    (j : ℕ) (hj : 2*j < a) : m+6*(j : ℤ) ≤ x (2*j) := by
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have hj' : 2*j < a := by omega
    have hp := hpair (2*j) (by omega)
    have h := ih hj'
    have he : 2*(j+1) = 2*j+2 := by omega
    change m+6*((j+1 : ℕ) : ℤ) ≤ x (2*(j+1))
    rw [he, Nat.cast_add, Nat.cast_one]
    omega

theorem sorted_rank (m : ℤ) (x : ℕ → ℤ) (a i : ℕ)
    (hi : i < a) (h0 : m ≤ x 0)
    (hinc : ∀ j, j+1 < a → x j < x (j+1))
    (hodd : ∀ j, j < a → x j % 2 = 1)
    (hthree : ∀ j, j < a → x j % 3 ≠ 0) :
    m+3*(i : ℤ)-1 ≤ x i := by
  have hpair : ∀ j, j+2 < a → x j+6 ≤ x (j+2) := by
    intro j hj
    exact three_free_spacing (x j) (x (j+1)) (x (j+2))
      (hinc j (by omega)) (hinc (j+1) (by omega))
      (hodd j (by omega)) (hodd (j+1) (by omega)) (hodd (j+2) hj)
      (hthree j (by omega)) (hthree (j+1) (by omega)) (hthree (j+2) hj)
  let j := i/2
  have hj : 2*j < a := by dsimp [j]; omega
  have he := even_index_rank m x a h0 hpair j hj
  by_cases h : i % 2 = 0
  · have hEq : i = 2*j := by dsimp [j]; omega
    rw [hEq, Nat.cast_mul]
    norm_num
    omega
  · have hEq : i = 2*j+1 := by dsimp [j]; omega
    have hs := odd_spacing (x (2*j)) (x (2*j+1))
      (hinc (2*j) (by omega)) (hodd (2*j) hj) (hodd (2*j+1) (by omega))
    rw [hEq, Nat.cast_add, Nat.cast_mul]
    norm_num
    omega

theorem correction_nine_identity (x : ℤ) :
    (3*x)^9*(x+1)-(3*x+1)^9*(x-2) =
      39366*x^8+96228*x^7+91854*x^6+51030*x^5+18144*x^4+
      4212*x^3+621*x^2+53*x+2 := by
  ring

theorem correction_nine_bound (x : ℤ) (hx : 0 ≤ x) :
    (3*x+1)^9*(x-2) ≤ (3*x)^9*(x+1) := by
  have hp : 0 ≤ 39366*x^8+96228*x^7+91854*x^6+51030*x^5+18144*x^4+
      4212*x^3+621*x^2+53*x+2 := by positivity
  rw [← correction_nine_identity] at hp
  exact sub_nonneg.mp hp

theorem ranked_nine_bound (L x : ℤ) (hL : 2 ≤ L) (hx : L ≤ x) :
    (3*x+1)^9*(L-2) ≤ (3*x)^9*(L+1) := by
  have hx0 : 0 ≤ x := by omega
  have hx3 : 0 ≤ 3*x := by omega
  have hpow : (3*x)^9 ≤ (3*x+1)^9 := by
    gcongr <;> omega
  have hgap := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hpow)
  have hbase := correction_nine_bound x hx0
  have h : 0 ≤ (3*x)^9*(L+1)-(3*x+1)^9*(L-2) := by
    calc
      0 ≤ ((3*x)^9*(x+1)-(3*x+1)^9*(x-2)) +
          (x-L)*((3*x+1)^9-(3*x)^9) :=
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
    (hm : 4 ≤ m) (hx : ∀ i, i < a → m+3*(i : ℤ)-1 ≤ x i) :
    (m-3)*visitProduct (fun i => (3*x i+1)^9) a ≤
      (m+3*(a : ℤ)-3)*visitProduct (fun i => (3*x i)^9) a := by
  induction a with
  | zero => simp [visitProduct]
  | succ a ih =>
    have hp := ih (fun i hi => hx i (by omega))
    have hL : 2 ≤ m+3*(a : ℤ)-1 := by omega
    have hstep := ranked_nine_bound (m+3*(a : ℤ)-1) (x a) hL
      (hx a (by omega))
    rw [show m+3*(a : ℤ)-1-2 = m+3*(a : ℤ)-3 by ring,
        show m+3*(a : ℤ)-1+1 = m+3*(a : ℤ) by ring] at hstep
    have hxa : 0 ≤ x a := by have h := hx a (by omega); omega
    have hnum : 0 ≤ (3*x a+1)^9 := by positivity
    have hden : 0 ≤ visitProduct (fun i => (3*x i)^9) a := by
      apply le_of_lt
      apply visitProduct_pos
      intro i hi
      have hxi : 0 < x i := by have h := hx i (by omega); omega
      positivity
    simp only [visitProduct, Nat.cast_succ]
    calc
      (m-3)*(visitProduct (fun i => (3*x i+1)^9) a * (3*x a+1)^9) =
          ((m-3)*visitProduct (fun i => (3*x i+1)^9) a)*(3*x a+1)^9 := by ring
      _ ≤ ((m+3*(a : ℤ)-3)*visitProduct (fun i => (3*x i)^9) a)*(3*x a+1)^9 :=
        mul_le_mul_of_nonneg_right hp hnum
      _ = visitProduct (fun i => (3*x i)^9) a * ((3*x a+1)^9*(m+3*(a : ℤ)-3)) := by ring
      _ ≤ visitProduct (fun i => (3*x i)^9) a * ((3*x a)^9*(m+3*(a : ℤ))) :=
        mul_le_mul_of_nonneg_left hstep hden
      _ = _ := by ring

/-- A non-descending multiplicative balance implies the polynomial envelope. -/
theorem nondescending_coefficient_bound (M A m : ℤ) (x : ℕ → ℤ) (a : ℕ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hm : 4 ≤ m)
    (hx : ∀ i, i < a → m+3*(i : ℤ)-1 ≤ x i)
    (hbalance : M*visitProduct (fun i => 3*x i) a ≤
      A*visitProduct (fun i => 3*x i+1) a) :
    M^9*(m-3) ≤ A^9*(m+3*(a : ℤ)-3) := by
  have hv : 0 < visitProduct (fun i => 3*x i) a := by
    apply visitProduct_pos
    intro i hi
    have h := hx i hi
    omega
  have hv6 : 0 < visitProduct (fun i => (3*x i)^9) a := by
    rw [visitProduct_pow]
    positivity
  have hleft : 0 ≤ M*visitProduct (fun i => 3*x i) a :=
    mul_nonneg hM hv.le
  have hp : (M*visitProduct (fun i => 3*x i) a)^9 ≤
      (A*visitProduct (fun i => 3*x i+1) a)^9 := by gcongr
  rw [mul_pow, mul_pow, ← visitProduct_pow (fun i => 3*x i) a 9,
    ← visitProduct_pow (fun i => 3*x i+1) a 9] at hp
  have he := ranked_product_envelope m x a hm hx
  have hm0 : 0 ≤ m-3 := by omega
  have hA6 : 0 ≤ A^9 := by positivity
  have hc : (M^9*(m-3))*visitProduct (fun i => (3*x i)^9) a ≤
      (A^9*(m+3*(a : ℤ)-3))*visitProduct (fun i => (3*x i)^9) a := by
    calc
      _ = (m-3)*(M^9*visitProduct (fun i => (3*x i)^9) a) := by ring
      _ ≤ (m-3)*(A^9*visitProduct (fun i => (3*x i+1)^9) a) :=
        mul_le_mul_of_nonneg_left hp hm0
      _ = A^9*((m-3)*visitProduct (fun i => (3*x i+1)^9) a) := by ring
      _ ≤ A^9*((m+3*(a : ℤ)-3)*visitProduct (fun i => (3*x i)^9) a) :=
        mul_le_mul_of_nonneg_left he hA6
      _ = _ := by ring
  by_contra! hn
  exact (not_lt_of_ge hc) (mul_lt_mul_of_pos_right hn hv6)

/-- A strict violation of the envelope forces the endpoint below the start. -/
theorem distinct_visit_descent (M A m y : ℤ) (x : ℕ → ℤ) (a : ℕ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hm : 4 ≤ m)
    (hx : ∀ i, i < a → m+3*(i : ℤ)-1 ≤ x i)
    (hidentity : M*y*visitProduct (fun i => 3*x i) a =
      A*m*visitProduct (fun i => 3*x i+1) a)
    (hgap : A^9*(m+3*(a : ℤ)-3) < M^9*(m-3)) : y < m := by
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

/-- Connect the ranked envelope to a finite strictly increasing list of
odd, three-free visits. Ordering and the trajectory identity are hypotheses. -/
theorem sorted_visit_descent (M A m y : ℤ) (x : ℕ → ℤ) (a : ℕ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hm : 4 ≤ m)
    (hfloor : ∀ i, i < a → m ≤ x i)
    (hinc : ∀ i, i+1 < a → x i < x (i+1))
    (hodd : ∀ i, i < a → x i % 2 = 1)
    (hthree : ∀ i, i < a → x i % 3 ≠ 0)
    (hidentity : M*y*visitProduct (fun i => 3*x i) a =
      A*m*visitProduct (fun i => 3*x i+1) a)
    (hgap : A^9*(m+3*(a : ℤ)-3) < M^9*(m-3)) : y < m := by
  apply distinct_visit_descent M A m y x a hM hA hm _ hidentity hgap
  intro i hi
  exact sorted_rank m x a i hi (hfloor 0 (by omega)) hinc hodd hthree

end CollatzRunyan.LogarithmicDeficitRigidity

#print axioms CollatzRunyan.LogarithmicDeficitRigidity.odd_spacing
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.three_free_spacing
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.even_index_rank
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.sorted_rank
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.correction_nine_identity
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.correction_nine_bound
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.ranked_nine_bound
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.visitProduct_pos
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.visitProduct_pow
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.ranked_product_envelope
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.nondescending_coefficient_bound
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.distinct_visit_descent
#print axioms CollatzRunyan.LogarithmicDeficitRigidity.sorted_visit_descent
