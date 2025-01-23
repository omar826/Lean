import Mathlib
/-
lexicographic ordering of argument defn
search for theorems - #leansearch "type here"
# GCD
-/
def hcfsimple (a b : ℕ) : ℕ :=
  if b=0 then a else
  if a<b then hcfsimple b a else
  hcfsimple (a-b) b

#eval hcfsimple 6 27 -- 3

def hcf (a b : ℕ) : ℕ :=
  if h: b=0 then a else
  if h': a < b then hcf b a else
  have h1: a%b < b := by -- Tactic mode
    apply Nat.mod_lt
    simp [Nat.pos_iff_ne_zero]
    assumption -- basically like exact h
  have: a%b < a := by
    apply Nat.lt_of_lt_of_le h1
    apply Nat.le_of_not_gt h'
  hcf (a%b) b

  /-
  **Theorem** ∃ irrational numbers a and b s.t. a pair a^b is rational
  -/

  noncomputable abbrev sqrt2 : ℝ := Real.sqrt 2

  theorem rt2_rt2_rt2:
    (sqrt2^sqrt2)^sqrt2 = 2 := by
    rw[← Real.rpow_mul, Real.mul_self_sqrt]
    -- 3 goals - rt2^rt2, 0≤ 2, 0≤ rt2
    -- . focuses on the first goal
    -- 1st goal
    . simp
    -- 2nd goal
    . simp
    -- 3rd goal
    . simp
