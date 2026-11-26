import Mathlib

namespace CollatzRunyan.CycleCoreRigidity

-- Truncated ternary information in a single exact core transition.
theorem core_mod_power (a b c j : ℕ) (u v : ℤ) (hj : j ≤ a)
    (h : (3 : ℤ)^a * u - (2 : ℤ)^(b+c) * v = 1 - (2 : ℤ)^b) :
    (3 : ℤ)^j ∣ ((2 : ℤ)^(b+c) * v - ((2 : ℤ)^b - 1)) := by
  have hp : (3 : ℤ)^a = (3 : ℤ)^j * (3 : ℤ)^(a-j) := by
    rw [← pow_add]
    exact congrArg (fun l : ℕ => (3 : ℤ)^l) (by omega)
  refine ⟨(3 : ℤ)^(a-j) * u, ?_⟩
  calc
    _ = (3 : ℤ)^a * u := by linear_combination -h
    _ = _ := by rw [hp]; ring

theorem powers_coprime (j e : ℕ) : IsCoprime ((3 : ℤ)^j) ((2 : ℤ)^e) := by
  have h : IsCoprime (3 : ℤ) 2 := ⟨1, -1, by norm_num⟩
  exact h.pow

theorem core_divisibility_iff (a b c j : ℕ) (u v : ℤ) (hj : j ≤ a)
    (h : (3 : ℤ)^a * u - (2 : ℤ)^(b+c) * v = 1 - (2 : ℤ)^b) :
    ((3 : ℤ)^j ∣ v) ↔ ((3 : ℤ)^j ∣ ((2 : ℤ)^b - 1)) := by
  obtain ⟨w, hw⟩ := core_mod_power a b c j u v hj h
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(2 : ℤ)^(b+c) * z - w, ?_⟩
    calc
      (2 : ℤ)^b - 1 = (2 : ℤ)^(b+c) * v - (3 : ℤ)^j * w := by linear_combination -hw
      _ = _ := by rw [hz]; ring
  · rintro ⟨z, hz⟩
    apply (powers_coprime j (b+c)).dvd_of_dvd_mul_left
    refine ⟨w + z, ?_⟩
    calc
      (2 : ℤ)^(b+c) * v = (3 : ℤ)^j * w + ((2 : ℤ)^b - 1) := by linear_combination hw
      _ = _ := by rw [hz]; ring

-- A family of positive integer trajectories that appear closed modulo
-- arbitrarily high powers of six, but actually descend after four steps.
def shortcut (x : ℤ) : ℤ :=
  if x % 2 = 0 then x / 2 else (3*x+1)/2

def shadowParam : ℕ → ℤ
  | 0 => 0
  | h+1 => 36 * shadowParam h + 5

theorem shadow_param_nonneg (h : ℕ) : 0 ≤ shadowParam h := by
  induction h with
  | zero => simp [shadowParam]
  | succ h ih => simp only [shadowParam]; linarith

theorem shadow_param_pow (h : ℕ) : 1 + 7 * shadowParam h = (36 : ℤ)^h := by
  induction h with
  | zero => norm_num [shadowParam]
  | succ h ih =>
    rw [shadowParam, pow_succ]
    rw [← ih]
    ring

theorem shadow_steps (w : ℤ) :
    shortcut (16*w+3) = 24*w+5 ∧
    shortcut (24*w+5) = 36*w+8 ∧
    shortcut (36*w+8) = 18*w+4 ∧
    shortcut (18*w+4) = 9*w+2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : (16*w+3) % 2 ≠ 0 := by omega
    simp only [shortcut, if_neg h]
    omega
  · have h : (24*w+5) % 2 ≠ 0 := by omega
    simp only [shortcut, if_neg h]
    omega
  · have h : (36*w+8) % 2 = 0 := by omega
    simp only [shortcut, if_pos h]
    omega
  · have h : (18*w+4) % 2 = 0 := by omega
    simp only [shortcut, if_pos h]
    omega

def fourSteps (x : ℤ) : ℤ := shortcut (shortcut (shortcut (shortcut x)))

theorem shadow_not_cycle (h : ℕ) :
    ∃ n : ℤ, 1 < n ∧ 0 < fourSteps n ∧ fourSteps n < n ∧
      (6 : ℤ)^h ∣ (n - fourSteps n) := by
  let w := shadowParam h
  have hw : 0 ≤ w := shadow_param_nonneg h
  obtain ⟨h1,h2,h3,h4⟩ := shadow_steps w
  have ht : fourSteps (16*w+3) = 9*w+2 := by
    unfold fourSteps
    rw [h1,h2,h3,h4]
  refine ⟨16*w+3, by omega, ?_, ?_, ?_⟩
  · rw [ht]; omega
  · rw [ht]; omega
  · rw [ht]
    refine ⟨(6 : ℤ)^h, ?_⟩
    calc
      _ = 1 + 7*w := by ring
      _ = (36 : ℤ)^h := shadow_param_pow h
      _ = ((6 : ℤ)*6)^h := by norm_num
      _ = (6 : ℤ)^h * (6 : ℤ)^h := by rw [mul_pow]

#print axioms core_mod_power
#print axioms powers_coprime
#print axioms core_divisibility_iff
#print axioms shadow_param_nonneg
#print axioms shadow_param_pow
#print axioms shadow_steps
#print axioms shadow_not_cycle

end CollatzRunyan.CycleCoreRigidity
