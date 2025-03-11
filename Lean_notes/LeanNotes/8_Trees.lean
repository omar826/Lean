import mathlib
inductive BoolTree (α: Type) where
  | leaf: α → BoolTree α
  | node: (Bool → BoolTree α) → BoolTree α
-- (function from Bool to BoolTree α) to BoolTree
namespace BoolTree

def eg1: BoolTree Nat := node (fun _ => leaf 2)

def tolist {α : Type}: BoolTree α → List α
  | leaf a => [a]
  | node f => tolist (f true) ++ tolist (f false)

#eval tolist eg1 -- [2,2]

inductive listtree (α: Type) where
  | leaf (a: α): listtree α
  | node (l: List (listtree α)): listtree α
  deriving Repr, Inhabited

#check List.foldl

def listsum (l: List Nat): Nat :=
  l.foldl (fun (sum) n => sum + n) 0

#eval listsum [1,2,3] -- 6

#check List.map

def evens (l: List Nat): List Nat :=
  l.map (fun n => n*2)

#eval evens [1,2,3] -- [2,4,6]

def listtill (n: Nat): List Nat :=
  match n with
  | 0 => []
  | n+1 => n :: listtill n

#eval listtill 3 -- [2,1,0]

def listtillflat (n: ℕ ): List ℕ :=
  (listtill n).flatMap listtill

#eval listtillflat 3 -- [1,0,0]

end BoolTree

-- Fin n - type of natural numbers less than n
