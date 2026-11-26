import Mathlib

/-!
# Collatz–Runyan: Binary Conjugation

A two-sector lift of shortcut Collatz. The Boolean sector is independent
of arithmetic parity. Physical interpretations are not axioms of this module.
The signed projection is a representation; zero is not a physical sector.
-/

namespace CollatzRunyan.BinaryConjugation

 def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

 def orbit (k n : ℕ) : ℕ :=
  match k with
  | 0 => n
  | k + 1 => shortcut (orbit k n)

structure State where
  magnitude : ℕ
  sector : Bool
  deriving DecidableEq

 def conjugate (s : State) : State := ⟨s.magnitude, !s.sector⟩
 def step (s : State) : State := ⟨shortcut s.magnitude, s.sector⟩
 def evolve (k : ℕ) (s : State) : State := ⟨orbit k s.magnitude, s.sector⟩
 def signed (s : State) : ℤ :=
  if s.sector then -(s.magnitude : ℤ) else (s.magnitude : ℤ)

 theorem conjugate_involution (s : State) : conjugate (conjugate s) = s := by
  cases s with
  | mk n b => cases b <;> rfl

 theorem conjugate_ne_self (s : State) : conjugate s ≠ s := by
  cases s with
  | mk n b => cases b <;> simp [conjugate]

 theorem step_conjugate (s : State) : step (conjugate s) = conjugate (step s) := by
  rfl

 theorem evolve_conjugate (k : ℕ) (s : State) :
    evolve k (conjugate s) = conjugate (evolve k s) := by
  rfl

 theorem evolve_zero (s : State) : evolve 0 s = s := by
  cases s
  rfl

 theorem evolve_succ (k : ℕ) (s : State) :
    evolve (k + 1) s = step (evolve k s) := by
  rfl

 theorem signed_conjugate (s : State) : signed (conjugate s) = -signed s := by
  cases s with
  | mk n b => cases b <;> simp [signed, conjugate]

 theorem signed_orbit_reflection (k : ℕ) (s : State) :
    signed (evolve k (conjugate s)) = -signed (evolve k s) := by
  rw [evolve_conjugate, signed_conjugate]

 def parity (s : State) : ℕ := s.magnitude % 2

 theorem parity_history_invariant (k : ℕ) (s : State) :
    parity (evolve k (conjugate s)) = parity (evolve k s) := by
  rfl

-- Divisibility by every power of two is invariant under reflection.
 theorem two_power_dvd_neg (k : ℕ) (z : ℤ) :
    (2 : ℤ)^k ∣ -z ↔ (2 : ℤ)^k ∣ z := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    calc
      z = -(-z) := by simp
      _ = -((2 : ℤ)^k * a) := by rw [ha]
      _ = (2 : ℤ)^k * -a := by simp
  · rintro ⟨a, ha⟩
    exact ⟨-a, by rw [ha, mul_neg]⟩

-- Exact finite valuation, expressed without choosing a convention at zero.
 def ExactValuation (k : ℕ) (z : ℤ) : Prop :=
  (2 : ℤ)^k ∣ z ∧ ¬ ((2 : ℤ)^(k+1) ∣ z)

 theorem exactValuation_neg (k : ℕ) (z : ℤ) :
    ExactValuation k (-z) ↔ ExactValuation k z := by
  simp only [ExactValuation, two_power_dvd_neg]

 theorem valuation_history_invariant (j k : ℕ) (s : State) :
    ExactValuation j (signed (evolve k (conjugate s))) ↔
    ExactValuation j (signed (evolve k s)) := by
  rw [signed_orbit_reflection, exactValuation_neg]

-- Odd numerator of the accelerated map in each sector.
 def oddNumerator (s : State) : ℤ :=
  if s.sector then 3 * signed s - 1 else 3 * signed s + 1

 theorem oddNumerator_conjugate (s : State) :
    oddNumerator (conjugate s) = -oddNumerator s := by
  cases s with
  | mk n b => cases b <;> simp [oddNumerator, signed, conjugate] <;> ring

 theorem accelerated_exponent_invariant (j : ℕ) (s : State) :
    ExactValuation j (oddNumerator (conjugate s)) ↔
    ExactValuation j (oddNumerator s) := by
  rw [oddNumerator_conjugate, exactValuation_neg]

 theorem return_conjugate_iff (k : ℕ) (s : State) :
    evolve k (conjugate s) = conjugate s ↔ evolve k s = s := by
  rw [evolve_conjugate]
  constructor
  · intro h
    have h' := congrArg conjugate h
    simpa only [conjugate_involution] using h'
  · intro h
    rw [h]

 def ExactPeriod (p : ℕ) (s : State) : Prop :=
  0 < p ∧ evolve p s = s ∧ ∀ j : ℕ, 0 < j → j < p → evolve j s ≠ s

 theorem exactPeriod_conjugate (p : ℕ) (s : State) :
    ExactPeriod p (conjugate s) ↔ ExactPeriod p s := by
  unfold ExactPeriod
  constructor
  · rintro ⟨hp, hreturn, hminimal⟩
    refine ⟨hp, (return_conjugate_iff p s).mp hreturn, ?_⟩
    intro j hj hjp h
    exact hminimal j hj hjp ((return_conjugate_iff j s).mpr h)
  · rintro ⟨hp, hreturn, hminimal⟩
    refine ⟨hp, (return_conjugate_iff p s).mpr hreturn, ?_⟩
    intro j hj hjp h
    exact hminimal j hj hjp ((return_conjugate_iff j s).mp h)

 theorem hits_one_iff (n : ℕ) :
    (∃ k, evolve k ⟨n, false⟩ = ⟨1, false⟩) ↔
    (∃ k, evolve k ⟨n, true⟩ = ⟨1, true⟩) := by
  constructor
  · rintro ⟨k, h⟩
    exact ⟨k, congrArg conjugate h⟩
  · rintro ⟨k, h⟩
    exact ⟨k, congrArg conjugate h⟩

-- Conditional transport of an affine trajectory identity from v25.
-- No claim is made here that a particular external v25 theorem is imported.
 theorem affine_transport (k n a c : ℕ)
    (h : (2 : ℤ)^k * (orbit k n : ℤ) = (3 : ℤ)^a * (n : ℤ) + (c : ℤ)) :
    (2 : ℤ)^k * signed (evolve k ⟨n, true⟩) =
      (3 : ℤ)^a * signed ⟨n, true⟩ - (c : ℤ) := by
  change (2 : ℤ)^k * -(orbit k n : ℤ) = (3 : ℤ)^a * -(n : ℤ) - (c : ℤ)
  rw [mul_neg, mul_neg, h]
  ring

-- Any magnitude-only observable is conjugation invariant.
 theorem observable_invariant {α : Type*} (F : ℕ → α) (s : State) :
    F (conjugate s).magnitude = F s.magnitude := by
  rfl

example : ExactValuation 2 (oddNumerator ⟨137, false⟩) := by
  norm_num [ExactValuation, oddNumerator, signed]

example : ExactValuation 2 (oddNumerator ⟨137, true⟩) := by
  norm_num [ExactValuation, oddNumerator, signed]

end CollatzRunyan.BinaryConjugation
