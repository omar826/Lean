import mathlib4
/-
= and ==
folding, flattening, and mapping
-/

inductive FinTree (α: Type) where
  | leaf(a: α ): FinTree α
  | node : {n: ℕ } → (Fin n → FinTree α) → FinTree α

/-
          T
        / | \
      3  /\  \
        7  6  5
-/

namespace FinTree

def ofBinTree {α: Type} : BinTree α → FinTree α
  | BinTree.leaf a => FinTree.leaf a
  | BinTree.node t₁ t₂ =>
  let family: Fin 2 → FinTree α := λ i =>
    match i with
    | ⟨0, _⟩  => leaf 3
    | ⟨1, _⟩  => ofBinTree ⟨ | .node(.leaf 7) (.leaf 6)⟩
    | ⟨ 2,0⟩ => node (n := 3) λ i => leaf 7
