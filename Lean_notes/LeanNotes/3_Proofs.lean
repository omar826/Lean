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
