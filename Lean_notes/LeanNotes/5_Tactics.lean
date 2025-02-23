import mathlib
/-
by - tactic mode
-/
example (a b c: ℝ ): a*b*c = b*(c*a) := by
  -- goal: a*b*c = b*(c*a)
  rw [mul_comm a b]
  -- goal: b*a*c = b*(c*a)
  rw [mul_assoc b a c]
  -- goal: b*(a*c) = b*(c*a)
  rw [mul_comm a c]
/-
# mul_comm
mul_comm a b: a*b = b*a, a b: lean infers types
mul_comm: infers a and b
mul_comm a: a*? = ?*a

-/
#check mul_comm -- a*b = b*a

/-
# apply
apply is a tactic that takes a theorem and applies it to the current goal
if theorem is A → B,
and goal is of type B,
then new goals are of type A
-/

example: 4 ≤ 8 := by
  --goal: 4 ≤ 5
  apply Nat.succ_le_succ
  --goal: casea: 3≤ 7
  apply Nat.succ_le_succ
  --goal: casea: 2≤ 6
  apply Nat.succ_le_succ
  --goal: casea: 1≤ 5
  apply Nat.succ_le_succ
  --goal: casea: 0≤ 4
  apply Nat.zero_le
  --goal: no goals

/-
# repeat
repeat is a tactic that applies a tactic to the current goal until it fails
-/

example: 4 ≤ 8 := by
  repeat
    apply Nat.succ_le_succ
  --goals: 3≤ 7, 2≤ 6, 1≤ 5, 0≤ 4
  apply Nat.zero_le (4) -- argument can be provided if needed
  --goal: no goals

/-
# have
have is a tactic that introduces a new hypothesis
-/

example: 4 ≤ 8 := by
  have h1: 0 ≤ 4 := by
    --goal: 0 ≤ 4
    apply Nat.zero_le
  have h2: 1 ≤ 5 := by
    apply Nat.succ_le_succ h1
  have h3: 2 ≤ 6 := by
    apply Nat.succ_le_succ h2
  --goal: 4 ≤ 8
  apply Nat.succ_le_succ
  --goal: 3 ≤ 7
  apply Nat.succ_le_succ
  --goal: 2 ≤ 6
  apply h3

/-
# exact
exact is a tactic that closes the current goal if the goal is exactly the same as the argument
so we could have used exact h3 above.
-/

#check Nat.le_of_succ_le_succ-- n.succ ≤ m.succ → n ≤ m
#check Nat.succ_le_succ -- n≤ m → n.succ≤ m.succ
#check Nat.le_step -- n≤ m → n≤ m.succ
#check Nat.le_refl -- True → n ≤ n

def someNat : Nat := by
  --goal: ℕ
  apply Nat.succ
  --goal: ℕ
  apply Nat.succ
  apply Nat.add
  --goals: ℕ, ℕ
  --goals indexed by .s
  . exact 2
  . apply Nat.succ
    apply Nat.zero

#eval someNat -- 5

/-
# first
first | tactic 1| tactic2
applies tactic 1 if applicable else tactic2
-/

example: 4 ≤ 8 := by
  first| apply Nat.le_refl | apply Nat.le_step
  -- goal: 4≤ 7
  repeat (first| apply Nat.le_refl | apply Nat.le_step)
  -- goal: No goals

/-
# decide
its a function from prop to bool
checks basic numerical propositions
# by decide
resolves goal if it is a simple numerical prop
-/

#eval decide (1=1) -- true
#eval decide (1<1) -- false

example: 4≤ 8 := by
  decide

/-
# macro
macros are used to define new tactics or expressions
tactic - indicator for tactics
term - indicator for expressions

macro "name": tactic/term =>
  `(tactic|...)
  or
  `(term|...)

$variable - variable substitution
-/

macro "nat_le": tactic =>
  `(tactic| repeat(first| apply Nat.le_refl | apply Nat.le_step))

example: 4 ≤ 8 := by
  nat_le
  -- goal: No goals

macro "repeating" r:term "finish" f:term : tactic =>
  `(tactic| repeat(first| apply $f | apply $r))

example: 4 ≤ 8 := by
  repeating Nat.le_step finish Nat.le_refl
  -- goal: No goals
