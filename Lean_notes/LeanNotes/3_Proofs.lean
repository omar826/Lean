/-
# Propositions
-/
#check And-- Prop→ Prop→ Prop
#check Or-- Prop→ Prop→ Prop
#check Not-- Prop→ Prop

variable (p q r : Prop)
#check p ∧ q -- Prop
#check And p q
#check p ∨ q
#check Or p q
#check (p ∧ q) → r
/-
#guard_msgs in - adds error msg as comments
-/
theorem twosum: 2+2=4 :=
 sorry

 /-
 Theorems- named proposition and its proof
 Axiom - proposition without proof
 Example -unnamed proposition with proof
 -/

 #check Nat.zero_le -- Nat → 0 ≤ n
 #check Nat.le_refl -- Nat → n ≤ n
 #check Nat.zero_le 5 -- 0 ≤ 5
 #check Nat.le -- Nat → Nat → Prop
 #check Nat.succ -- Nat → Nat
 #eval Nat.succ 5 -- 6
 #check Nat.succ_le_succ -- {a b: Nat} → a ≤ b → a.succ ≤ b.succ
 #check Nat.le_step-- {a b: Nat} → a ≤ b → a ≤ b.succ
 -- Propositions cannot be evaluated if they can neither be proved nor disproved

theorem zero_le_five: 0 ≤ 5 := Nat.zero_le 5
example: 1 ≤ 1 := Nat.le_refl 1
example: True := trivial
example: 3+2=5 := rfl
example: 3≤ 5 :=
    Nat.le_step (Nat.le_step (Nat.le_refl 3))

/-
# Proof Irrelevance
any 2 proofs of the same theorem are definitionally equal

**#print**  - shows the proof of a theorem
**show** -

-/

theorem t1: p→ q→ p:=
    fun hp: p => fun hq: q => hp
#print t1

/-
And.intro - p → q → p ∧ q
And.left - p ∧ q → p
And.right - p ∧ q → q

aruments to And.intro is hp and hq where
hp and hq have types p and q respectively
p and q have types Prop
* hp and hq are proofs of p and q respectively
-/
variable (p q: Prop)
variable (hp: p)(hq: q)
#check And.intro
#check And.intro hp hq
#check fun (hp:p)(hq:q) => And.intro hp hq

theorem and_commutative: p ∧ q → q ∧ p :=
    fun h: p ∧ q => And.intro h.right h.left

theorem and_commutative'(h:p ∧ q): q ∧ p :=
    And.intro h.right h.left

/-
⟨hp, hq⟩ ≝ And.intro hp hq
-/

#check (⟨hp, hq⟩: p∧ q) -- p ∧ q
 /-
 # using function without namespace
 expression.fun ≝ namespace.fun expression
 eg) h.right ≝ And.right h
 -/

example (h: p ∧ q): q ∧ p :=
    ⟨h.right, h.left⟩

/-
right commutativity by default
-/

example (h: p∧ q): q∧ p∧ q :=
    ⟨h.right, h.left, h.right⟩

example (h: p∧ q): q∧ p∧ q :=
    ⟨h.right, ⟨ h.left, h.right⟩⟩

/-
Or.inl \Or.intro_left q hp- p → p ∨ q
creates  a proof of p ∨ q from a proof of p

Or.inr/ Or.intro_right p hq- q → p ∨ q

Or.elim hporq hpr hqr - p ∨ q → (p → r) → (q → r) → r

-/
variable (p q r: Prop)

example (h: p∨ q): q∨ p :=
    Or.elim h
        (fun hp: p =>
        show q ∨ p from Or.inr hp)
        (fun hq: q =>
        show q ∨ p from Or.inl hq)

example (h: p∨ q): q∨ p :=
    Or.elim h
        (fun hp: p => Or.inr hp)
        (fun hq: q => Or.inl hq)

/-
# proofs by functions
eg) theorem and_commutative: p ∧ q → q ∧ p :=
    fun h: p ∧ q => And.intro h.right h.left
* states that if we have proof of p ∧ q
we can create a proof of q ∧ p
* proof of p is of type p
* type of theorem is p ∧ q → q ∧ p
* h.left is a proof of p
* h.right is a proof of q
* logical statements are function types
and proofs are functions that transform proof of one statement to another
-/

/-
# Negation
¬ p ≝ p → false
-/

example (hpq: p → q): ¬ q → ¬ p :=
    fun hnq: ¬ q =>(
    fun hp: p =>
    show False from hnq (hpq hp)
    )
-- ¬ q → ¬ p : is a function takes proof of not q to proof of not p
-- ¬ p is a function that takes proof of p to false

/-
# False
False.elim - false → p
absurd - p → ¬ p → q
-/

example (h: False): p :=
    False.elim h

example (hnp: ¬ p)(hq: q)(hqp: q → p): r :=
    absurd (hqp hq) hnp

/-
# True
True.intro -
-/
