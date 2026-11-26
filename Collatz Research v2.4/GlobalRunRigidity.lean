import Mathlib

namespace CollatzRunyan.GlobalRunRigidity

/-- The incoming run equation determines the minimum modulo three. -/
theorem incoming_residue (T m : ℤ) (h : (T*m) % 3 = 2) :
    (T % 3 = 1 → m % 3 = 2) ∧ (T % 3 = 2 → m % 3 = 1) := by
  rw [Int.mul_emod] at h
  constructor
  · intro ht
    rw [ht] at h
    omega
  · intro ht
    rw [ht] at h
    omega

/-- Three lower bounds on the positive odd core of a run. -/
theorem core_lower (P u m : ℤ) (hu : 0 < u) (ho : u % 2 = 1)
    (hm : m = P*u-1) :
    (m % 3 = 2 → (P % 3 = 1 ∨ P % 3 = 2) → 3 ≤ u) ∧
    (m % 3 = 1 → P % 3 = 1 → 5 ≤ u) := by
  have he : (P*u) % 3 = (m+1) % 3 := by
    rw [show P*u = m+1 by linarith]
  rw [Int.mul_emod] at he
  constructor
  · intro hr hp
    rcases hp with hp | hp
    · rw [hp] at he
      omega
    · rw [hp] at he
      omega
  · intro hr hp
    rw [hp] at he
    omega

/-- A larger minimum odd core gives a smaller peak/minimum ratio.
Cross-multiplication avoids division and rounding. -/
theorem run_ratio_identity (P Q c u : ℤ) :
    (Q*c-1)*(P*u-1)-(Q*u-1)*(P*c-1) = (Q-P)*(u-c) := by
  ring

theorem run_ratio_bound (P Q c u : ℤ) (hp : P ≤ Q) (hc : c ≤ u) :
    (Q*u-1)*(P*c-1) ≤ (Q*c-1)*(P*u-1) := by
  have h := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hc)
  rw [← run_ratio_identity P Q c u] at h
  exact sub_nonneg.mp h

/-- Finite ordered product. -/
def runProduct (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n+1 => runProduct f n * f n

theorem runProduct_nonneg (f : ℕ → ℤ) (hf : ∀ i, 0 ≤ f i) (n : ℕ) :
    0 ≤ runProduct f n := by
  induction n with
  | zero => norm_num [runProduct]
  | succ n ih => exact mul_nonneg ih (hf n)

theorem runProduct_mono (f g : ℕ → ℤ) (hf : ∀ i, 0 ≤ f i)
    (hle : ∀ i, f i ≤ g i) (n : ℕ) : runProduct f n ≤ runProduct g n := by
  have hg : ∀ i, 0 ≤ g i := fun i => le_trans (hf i) (hle i)
  induction n with
  | zero => simp [runProduct]
  | succ n ih =>
    change runProduct f n * f n ≤ runProduct g n * g n
    exact mul_le_mul ih (hle n) (hf n) (runProduct_nonneg g hg n)

theorem runProduct_mul (f g : ℕ → ℤ) (n : ℕ) :
    runProduct (fun i => f i*g i) n = runProduct f n * runProduct g n := by
  induction n with
  | zero => norm_num [runProduct]
  | succ n ih =>
    simp only [runProduct, ih]
    ring

/-- Global envelope, assuming the product identity supplied by cyclic closure. -/
theorem global_envelope (m y lo hi : ℕ → ℤ) (n : ℕ) (E : ℤ)
    (hm : 0 < runProduct m n)
    (hy : ∀ i, 0 ≤ y i) (hl : ∀ i, 0 ≤ lo i)
    (hcross : ∀ i, y i * lo i ≤ hi i * m i)
    (hcycle : runProduct y n = E * runProduct m n) :
    E * runProduct lo n ≤ runProduct hi n := by
  have h := runProduct_mono (fun i => y i * lo i) (fun i => hi i * m i)
    (fun i => mul_nonneg (hy i) (hl i)) hcross n
  rw [runProduct_mul, runProduct_mul, hcycle] at h
  by_contra! hn
  have hh := mul_lt_mul_of_pos_right hn hm
  have hbad : runProduct hi n * runProduct m n <
      (E * runProduct m n) * runProduct lo n := by
    calc
      runProduct hi n * runProduct m n <
          (E * runProduct lo n) * runProduct m n := hh
      _ = (E * runProduct m n) * runProduct lo n := by ring
  exact (not_lt_of_ge h) hbad

/-- The residue-refined envelope excludes the run pattern (1,2), (1,1)
which survives the envelope using only the lower minimum 3. -/
theorem strict_refinement_example :
    (4 : ℤ)*5*3 ≤ 8*8 ∧ 4*13*19 > 20*44 := by
  norm_num

end CollatzRunyan.GlobalRunRigidity

#print axioms CollatzRunyan.GlobalRunRigidity.incoming_residue
#print axioms CollatzRunyan.GlobalRunRigidity.core_lower
#print axioms CollatzRunyan.GlobalRunRigidity.run_ratio_identity
#print axioms CollatzRunyan.GlobalRunRigidity.run_ratio_bound
#print axioms CollatzRunyan.GlobalRunRigidity.runProduct_nonneg
#print axioms CollatzRunyan.GlobalRunRigidity.runProduct_mono
#print axioms CollatzRunyan.GlobalRunRigidity.runProduct_mul
#print axioms CollatzRunyan.GlobalRunRigidity.global_envelope
#print axioms CollatzRunyan.GlobalRunRigidity.strict_refinement_example
