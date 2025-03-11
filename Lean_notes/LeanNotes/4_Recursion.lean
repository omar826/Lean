import Mathlib

--# Double

def Nat.double (n: Nat): Nat :=
  match n with
  | 0 => 0
  | Nat.succ m => Nat.succ (Nat.succ (Nat.double m))
#eval Nat.double 3 -- 6


/-
lexicographic ordering of argument defn
search for theorems - #leansearch "type here"
# GCD
-/
def hcfsimple (a b : ℕ) : ℕ :=
  if b=0 then a
  else
  if a<b then hcfsimple b a
  else hcfsimple (a-b) b

#eval hcfsimple 6 27 -- 3

def hcf (a b : ℕ) : ℕ :=
  if h: b=0 then a else
  if h': a < b then hcf b a
  else -- not(h) and not(h')
  have h1: a%b < b := by -- Tactic mode
    apply Nat.mod_lt
    simp [Nat.pos_iff_ne_zero]
    -- goal: not(b=0)
    assumption-- basically like exact h
  have h2: a%b < a := by
    apply Nat.lt_of_lt_of_le h1
    apply Nat.le_of_not_gt h'
  -- h1 and h2 prove termination
  hcf (a%b) b

/-
**Theorem** ∃ irrational numbers a and b s.t. a pair a^b is rational
# noncomputable
defns that are not computable. usually for existence proofs without explicit construction

# abbrev
renaming an expression
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

theorem irr_pow_irr_rat:
  ∃ (a b: ℝ), Irrational (a) ∧ Irrational (b) ∧ ¬ Irrational (a^b) := by
  by_cases h: Irrational (sqrt2 ^ sqrt2)
  -- 2 goals
  case pos =>
    use sqrt2 ^ sqrt2, sqrt2
    simp [h, rt2_rt2_rt2]
    -- goal: Irrational sqrt2
    simp [irrational_sqrt_two]
  case neg =>
    use sqrt2, sqrt2
    simp [irrational_sqrt_two, h]


--structure contains irrational a,b s.t a^b is rational

structure irrational_pair where
  (a b: ℝ)
  (irr_a: Irrational a)
  (irr_b: Irrational b)
  (rat_ab: ¬ Irrational (a^b))

-- function returns irrational pair

noncomputable def irr_pair: irrational_pair := by
  --goal: irrational_pair
  apply Classical.choice
  --goal: nonempty irrational_pair
  let ⟨a, b, irr_a, irr_b, rat_ab⟩ := irr_pow_irr_rat
  --goal: a,b ∈ ℝ, Irrational a, Irrational b, ¬ Irrational (a^b)
  exact ⟨a, b, irr_a, irr_b, rat_ab⟩

/-
Classical.choice - axiom of choice
-/
