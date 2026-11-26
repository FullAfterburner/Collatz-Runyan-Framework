import Mathlib

open scoped BigOperators

/-!
# Collatz–Runyan: nonuniform prime-power corrections
Exact weighted balance and a two-exception modular obstruction.
The segment lemmas are stated for integer transition chains. Applying the
multiplier lemma to a concrete gap word requires its product congruence.
No universal cycle exclusion or historical novelty is asserted.
-/
namespace CollatzRunyan.PrimePowerCorrections

-- Exact, nonuniform correction balance for a finite chain.
theorem correction_chain (m x : ℕ → ℤ) (n : ℕ) :
    (∀ i : ℕ, i < n → m i * x (i+1) = 3*x i+1) →
    (∑ i ∈ Finset.range n, (m i-3)*x (i+1)) =
      (n : ℤ)+3*(x 0-x n) := by
  induction n with
  | zero =>
      intro hs
      simp
  | succ n ih =>
      intro hs
      have hp := ih (fun i hi => hs i (Nat.lt.step hi))
      have ht := hs n (Nat.lt_succ_self n)
      rw [Finset.sum_range_succ, hp]
      push_cast
      linear_combination ht

-- In a closed chain all endpoint corrections cancel.
theorem cycle_weighted_balance (m x : ℕ → ℤ) (n : ℕ)
    (hs : ∀ i : ℕ, i < n → m i*x (i+1) = 3*x i+1)
    (hc : x n = x 0) :
    (∑ i ∈ Finset.range n, (m i-3)*x (i+1)) = (n : ℤ) := by
  rw [correction_chain m x n hs, hc]
  ring

-- The ordinary portions of a chain have multiplier 3 modulo q.
theorem ordinary_segment (q : ℤ) (m x : ℕ → ℤ) (n : ℕ) :
    (∀ i : ℕ, i < n → q ∣ m i-3) →
    (∀ i : ℕ, i < n → m i*x (i+1) = 3*x i+1) →
    q ∣ 3*(x n-x 0)-(n : ℤ) := by
  induction n with
  | zero =>
      intro hg hs
      simp
  | succ n ih =>
      intro hg hs
      have hp := ih (fun i hi => hg i (Nat.lt.step hi))
        (fun i hi => hs i (Nat.lt.step hi))
      obtain ⟨t, ht⟩ := hg n (Nat.lt_succ_self n)
      obtain ⟨s, hS⟩ := hp
      have hstep := hs n (Nat.lt_succ_self n)
      refine ⟨s-t*x (n+1), ?_⟩
      change 3*(x (n+1)-x 0)-((n+1 : ℕ) : ℤ) = _
      push_cast
      calc
        3*(x (n+1)-x 0)-((n : ℤ)+1) =
            (3*(x n-x 0)-(n : ℤ))-(m n-3)*x (n+1) := by
          linear_combination hstep
        _ = _ := by rw [hS, ht]; ring

-- If M = 2*m*3^s modulo q and M = 3^(s+2) modulo q,
-- cancellation of the ordinary factors gives 2*m = 9 modulo q.
theorem exception_multiplier (q M m : ℤ) (s : ℕ)
    (hc : IsCoprime q ((3 : ℤ)^s))
    (hM : q ∣ M-2*m*3^s)
    (hD : q ∣ M-3^(s+2)) : q ∣ 2*m-9 := by
  obtain ⟨u, hu⟩ := hM
  obtain ⟨v, hv⟩ := hD
  apply hc.dvd_of_dvd_mul_left
  refine ⟨v-u, ?_⟩
  calc
    (3 : ℤ)^s*(2*m-9) = (M-3^(s+2))-(M-2*m*3^s) := by
      rw [pow_add]
      norm_num <;> ring
    _ = _ := by rw [hu, hv]; ring

-- The first exception is a gap of one (multiplier 2).
-- u and v are the lengths of the two ordinary segments.
-- The two exceptional transitions and the ordinary segment congruences
-- force q | 2*u+3*v+5, i.e. q | 3*a-L for a=u+v+2, L=u+1.
theorem two_exception_count (q m x0 x1 y z u v : ℤ)
    (hfirst : 2*x1 = 3*x0+1)
    (hmiddle : q ∣ 3*(y-x1)-u)
    (hsecond : m*z = 3*y+1)
    (hreturn : q ∣ 3*(x0-z)-v)
    (hgap : q ∣ 2*m-9) : q ∣ 2*u+3*v+5 := by
  obtain ⟨s, hs⟩ := hmiddle
  obtain ⟨r, hr⟩ := hreturn
  obtain ⟨t, ht⟩ := hgap
  refine ⟨t*z-2*s-3*r, ?_⟩
  calc
    2*u+3*v+5 = (2*m-9)*z-2*(3*(y-x1)-u)-3*(3*(x0-z)-v) := by
      linear_combination -2*hsecond - 3*hfirst
    _ = _ := by rw [ht, hs, hr]; ring

-- Connect the arithmetic obstruction to two actual ordinary chains.
theorem two_exception_segments (q m x0 : ℤ) (u v : ℕ)
    (f g M N : ℕ → ℤ)
    (hfirst : 2*f 0 = 3*x0+1)
    (hM : ∀ i : ℕ, i < u → q ∣ M i-3)
    (hf : ∀ i : ℕ, i < u → M i*f (i+1) = 3*f i+1)
    (hsecond : m*g 0 = 3*f u+1)
    (hN : ∀ i : ℕ, i < v → q ∣ N i-3)
    (hg : ∀ i : ℕ, i < v → N i*g (i+1) = 3*g i+1)
    (hclose : g v = x0)
    (hgap : q ∣ 2*m-9) : q ∣ 2*(u : ℤ)+3*(v : ℤ)+5 := by
  have hp := ordinary_segment q M f u hM hf
  have hr := ordinary_segment q N g v hN hg
  rw [hclose] at hr
  exact two_exception_count q m x0 (f 0) (f u) (g 0) (u : ℤ) (v : ℤ)
    hfirst hp hsecond hr hgap

-- [1,13] has a=2, k=14, D=16375, B=5 and L=1.
-- The prime 5 alone misses this obstruction; 25 detects it.
theorem higher_power_two_exception_example :
    (25 : ℤ) ∣ ((2 : ℤ)^14-3^2) ∧
    (5 : ℤ) ∣ (5 : ℤ) ∧
    ¬ (25 : ℤ) ∣ (3*2-1 : ℤ) := by norm_num

#print axioms correction_chain
#print axioms cycle_weighted_balance
#print axioms ordinary_segment
#print axioms exception_multiplier
#print axioms two_exception_count
#print axioms two_exception_segments
#print axioms higher_power_two_exception_example

end CollatzRunyan.PrimePowerCorrections
