
/-
# FOL
**language** - set(array) of constants
**functions** - array
**predicates** - relations
**variables** - x, y, z, ... countably infinite
**terms** - objects built from variables, constants, functions
**logical connectives** - ∧, ∨, ¬, →, ↔
**quantifiers** - ∀, ∃
**formulas** - expressions built from terms, predicates, logical connectives, quantifiers
**axioms** - formulas assumed to be true eg) p ∨ ¬p for classical namespace in lean
**proofs** - constructed from axioms and inference rules:
  * modus ponens: p, p → q ⊢ q
  * universal generalization: p ⊢ ∀x p, means p is true for all x
  * existential instantiation: ∃x p ⊢ p[t/x] where t is a term
  t/x means t is substituted for x
eg) For natural numbers:
  * constants: 0, 1, 2, ...
  * functions: +, *, succ ...
  * predicates: =, <, ≤, ...
-/
/-
# Logic in Lean
**Propositions** - types
**Proofs** - terms of type proposition
**logical connectives** - inductive types or constructed from inductive types:
  * And, Or, Not
  * True, False
  * implies, iff
  * forall, exists
**quantifiers**:
  * ∀x:α, P x is (x:α) → P x
  * ∃x:α, P x is exists fun x:α => P x
  * proof of existence is a pair of:
    * x:α st P x is true
    * proof that P x is true
.m - infers preexisting variable is imlicit argument
-/
theorem les_trans {a b c: Nat}: a ≤ b → b ≤ c → a ≤ c := by
  intro h1 h2
  induction h2 with
  | refl => exact h1
  | step h ih =>
    /-
    h1: a ≤ b
    h2: b ≤ c
    h: b ≤ m
    ih: a ≤ m → a ≤ m.succ
    -/
    sorry
