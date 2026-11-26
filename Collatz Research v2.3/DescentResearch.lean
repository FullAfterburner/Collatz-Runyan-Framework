import Mathlib

/-!
# Deterministic Collatz descent: formalization candidate (v2.3)

Standalone extension of the existing Collatz–Runyan descent certificate.
Designed for Lean 4.19.0 / Mathlib 4.19.0. This source has not been
compiled in the authoring environment. Run `lake env lean DescentResearch.lean`.
The shortcut Collatz conjecture is represented as a proposition, NOT an axiom
or a theorem claimed without proof. All statements below are conditional where
necessary. The audit at the end is executed when the file is checked.
-/

namespace CollatzRunyan.Descent

/-- One shortcut step: an odd step includes its first division by two. -/
def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The value after exactly k shortcut iterations. -/
def orbit : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => shortcut (orbit k n)

def parity (n : ℕ) : ℕ := n % 2

def factor (n : ℕ) : ℕ := if n % 2 = 0 then 1 else 3

/-- Exact affine identity for one shortcut step. -/
theorem step_affine (n : ℕ) :
    2 * shortcut n = factor n * n + parity n := by
  by_cases h : n % 2 = 0
  · simp [shortcut, factor, parity, h] <;> omega
  · simp [shortcut, factor, parity, h] <;> omega

theorem shortcut_pos (n : ℕ) (hn : 0 < n) : 0 < shortcut n := by
  unfold shortcut
  split <;> omega

theorem orbit_pos (k n : ℕ) (hn : 0 < n) : 0 < orbit k n := by
  induction k with
  | zero => simpa [orbit] using hn
  | succ k ih => exact shortcut_pos (orbit k n) ih

theorem orbit_add (k l n : ℕ) :
    orbit (k + l) n = orbit l (orbit k n) := by
  induction l with
  | zero => simp [orbit]
  | succ l ih =>
    change shortcut (orbit (k + l) n) =
      shortcut (orbit l (orbit k n))
    exact congrArg shortcut ih

/-- Multiplicative coefficient of the actual parity history. -/
def coeffA : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, n => factor (orbit k n) * coeffA k n

/-- Additive coefficient of the actual parity history. -/
def coeffC : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => factor (orbit k n) * coeffC k n + 2^k * parity (orbit k n)

/-- Number of odd shortcut steps in the first k iterations. -/
def oddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => oddCount k n + parity (orbit k n)

theorem factor_eq_pow (n : ℕ) : factor n = 3 ^ parity n := by
  by_cases h : n % 2 = 0
  · simp [factor, parity, h]
  · have h1 : n % 2 = 1 := by omega
    simp [factor, parity, h, h1]

theorem coeffA_eq_pow (k n : ℕ) : coeffA k n = 3 ^ oddCount k n := by
  induction k with
  | zero => simp [coeffA, oddCount]
  | succ k ih =>
    change factor (orbit k n) * coeffA k n =
      3 ^ (oddCount k n + parity (orbit k n))
    rw [factor_eq_pow, ih, pow_add]
    ac_rfl

/-- The trajectory hypothesis is now derived, not postulated. -/
theorem affine_trajectory (k n : ℕ) :
    2^k * orbit k n = coeffA k n * n + coeffC k n := by
  induction k with
  | zero => simp [orbit, coeffA, coeffC]
  | succ k ih =>
    change 2^(k+1) * shortcut (orbit k n) =
      (factor (orbit k n) * coeffA k n) * n +
        (factor (orbit k n) * coeffC k n + 2^k * parity (orbit k n))
    calc
      2^(k+1) * shortcut (orbit k n) =
          2^k * (2 * shortcut (orbit k n)) := by rw [pow_succ] <;> ring
      _ = 2^k * (factor (orbit k n) * orbit k n + parity (orbit k n)) := by
        rw [step_affine]
      _ = factor (orbit k n) * (2^k * orbit k n) + 2^k * parity (orbit k n) := by
        ring
      _ = _ := by rw [ih] <;> ring

theorem affine_trajectory_pow (k n : ℕ) :
    2^k * orbit k n = 3^(oddCount k n) * n + coeffC k n := by
  rw [affine_trajectory, coeffA_eq_pow]

/-- Natural-number form of the certificate, avoiding truncated subtraction. -/
theorem descent_iff_certificate (k n : ℕ) :
    orbit k n < n ↔ coeffA k n * n + coeffC k n < 2^k * n := by
  rw [← affine_trajectory]
  exact (mul_lt_mul_left (show 0 < (2:ℕ)^k by positivity)).symm

/-- These are propositions, not assumed axioms. -/
def UniversalDescent : Prop := ∀ n : ℕ, 1 < n → ∃ k : ℕ, orbit k n < n

def ShortcutConvergence : Prop := ∀ n : ℕ, 0 < n → ∃ k : ℕ, orbit k n = 1

def UniversalCertificate : Prop :=
  ∀ n : ℕ, 1 < n → ∃ k : ℕ, coeffA k n * n + coeffC k n < 2^k * n

/-- Strong induction proves convergence, IF universal descent is proved. -/
theorem descent_implies_convergence (h : UniversalDescent) : ShortcutConvergence := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro hn
  by_cases h1 : n = 1
  · exact ⟨0, by simpa [orbit] using h1⟩
  · obtain ⟨k, hk⟩ := h n (by omega)
    obtain ⟨l, hl⟩ := ih (orbit k n) hk (orbit_pos k n hn)
    exact ⟨k + l, (orbit_add k l n).trans hl⟩

theorem convergence_implies_descent (h : ShortcutConvergence) : UniversalDescent := by
  intro n hn
  obtain ⟨k, hk⟩ := h n (by omega)
  exact ⟨k, by omega⟩

theorem descent_iff_convergence : UniversalDescent ↔ ShortcutConvergence :=
  ⟨descent_implies_convergence, convergence_implies_descent⟩

theorem certificate_iff_descent : UniversalCertificate ↔ UniversalDescent := by
  constructor
  · intro h n hn
    obtain ⟨k, hk⟩ := h n hn
    exact ⟨k, (descent_iff_certificate k n).2 hk⟩
  · intro h n hn
    obtain ⟨k, hk⟩ := h n hn
    exact ⟨k, (descent_iff_certificate k n).1 hk⟩

theorem certificate_iff_convergence : UniversalCertificate ↔ ShortcutConvergence :=
  certificate_iff_descent.trans descent_iff_convergence

/-- Elementary infinite residue-class certificates. -/
theorem even_descends (n : ℕ) (hn : 0 < n) (he : n % 2 = 0) :
    orbit 1 n < n := by
  simp [orbit, shortcut, he] <;> omega

theorem shortcut_four_add_one (q : ℕ) : shortcut (4*q+1) = 6*q+2 := by
  have h : (4*q+1) % 2 ≠ 0 := by omega
  simp [shortcut, h] <;> omega

theorem orbit_two_four_add_one (q : ℕ) : orbit 2 (4*q+1) = 3*q+1 := by
  change shortcut (shortcut (4*q+1)) = 3*q+1
  rw [shortcut_four_add_one]
  have h : (6*q+2) % 2 = 0 := by omega
  simp [shortcut, h] <;> omega

theorem four_add_one_descends (q : ℕ) (hq : 0 < q) :
    orbit 2 (4*q+1) < 4*q+1 := by
  rw [orbit_two_four_add_one]
  omega

/-- Any failure of convergence would produce a non-descending seed. -/
theorem nonconvergence_implies_nondescending
    (h : ¬ ShortcutConvergence) :
    ∃ n : ℕ, 1 < n ∧ ∀ k : ℕ, n ≤ orbit k n := by
  classical
  have hd : ¬ UniversalDescent := fun d => h (descent_implies_convergence d)
  unfold UniversalDescent at hd
  push_neg at hd
  exact hd

end CollatzRunyan.Descent

-- Audit each declaration individually after checking the source.
#print axioms CollatzRunyan.Descent.step_affine
#print axioms CollatzRunyan.Descent.shortcut_pos
#print axioms CollatzRunyan.Descent.orbit_pos
#print axioms CollatzRunyan.Descent.orbit_add
#print axioms CollatzRunyan.Descent.factor_eq_pow
#print axioms CollatzRunyan.Descent.coeffA_eq_pow
#print axioms CollatzRunyan.Descent.affine_trajectory
#print axioms CollatzRunyan.Descent.affine_trajectory_pow
#print axioms CollatzRunyan.Descent.descent_iff_certificate
#print axioms CollatzRunyan.Descent.descent_implies_convergence
#print axioms CollatzRunyan.Descent.convergence_implies_descent
#print axioms CollatzRunyan.Descent.descent_iff_convergence
#print axioms CollatzRunyan.Descent.certificate_iff_descent
#print axioms CollatzRunyan.Descent.certificate_iff_convergence
#print axioms CollatzRunyan.Descent.even_descends
#print axioms CollatzRunyan.Descent.shortcut_four_add_one
#print axioms CollatzRunyan.Descent.orbit_two_four_add_one
#print axioms CollatzRunyan.Descent.four_add_one_descends
#print axioms CollatzRunyan.Descent.nonconvergence_implies_nondescending
