import mathlib

inductive mynat where
  | zero: mynat
  | succ (n: mynat): mynat
  deriving Repr

namespace mynat
#eval succ (succ zero)--mynat.succ (mynat.succ mynat.zero)

def add (m n: mynat): mynat :=
  match m, n with
  | zero, n => n
  | succ m', n => succ (add m' n)

#eval succ zero |>.add <| succ <| succ zero -- succ (succ (succ zero))

/-
using + for add
-/
instance: Add mynat where
  add := add

#eval succ zero + succ zero -- succ (succ zero)

-- introducing new symbol
infix:65 " ++ " => add

#eval succ zero ++ succ zero -- succ (succ zero)

theorem zero_add (n: mynat): zero + n = n :=by
  rfl
theorem add_zero (n: mynat): n + zero = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    show add (succ n') zero = succ n'
    unfold add
    simp
    exact ih
end mynat

universe u v
inductive myprod (α: Type u)(β: Type v) where
  | pair (fst: α)(snd: β): myprod α β

structure myprod' (α: Type u) (β: Type v) where
  fst : α
  snd : β

example: myprod Nat Nat := myprod.pair 1 2
example: myprod' Nat Nat := {fst := 1, snd := 2}
example: myprod' Nat Nat := ⟨ 1, 2 ⟩

def myprod.fst {α: Type u}{β: Type v}: myprod α β → α
  | myprod.pair a _ => a

def myprod.snd {α: Type u}{β: Type v}: myprod α β → β
  | myprod.pair _ b => b

#eval myprod.fst (myprod.pair 1 2) -- 1

/-
sum type - disjoint union of types
inl - in left
inr - in right
-/
inductive mysum (α: Type u)(β: Type v) where
  | inl (a: α): mysum α β
  | inr (b: β): mysum α β

def mysum.eg1: mysum Nat Bool := mysum.inl 1
#check mysum.eg1 -- mysum Nat Bool
#eval mysum.eg1 -- mysum.inl 1

--unit type
inductive myunit where
  | star: myunit

def myunit.eg: myunit := myunit.star
#check myunit.eg -- myunit
#eval myunit.eg -- myunit.star

--empty type/ false proposition
inductive myfalse where

--true proposition
inductive mytrue where
  | trivial: mytrue

/-
mk - creates a new instance of a structure
-/

inductive myand (a b: Prop) where
  | mk (left: a)(right: b): myand a b
-- left is proof of a
-- right is proof of b
-- both left and right are required to conclude myand a b
-- mk packages left and right into a proof of myand a b
inductive myor (a b: Prop) where
  | inl (left: a): myor a b
  | inr (right: b): myor a b
-- inl or inr can conclude myor a b by itself
--note that left and right are just names for arguments

-- existential quantifier
inductive myexists {α: Type u}(p: α → Prop) where
  | mk (w: α)(proof: p w): myexists p

-- proof that there exists an even number
def even( n: Nat): Prop := n % 2 = 0
def even_proof: myexists even := myexists.mk 2 rfl

namespace mynat

def mul (m n: mynat): mynat :=
  match m with
  | zero => zero
  | succ m' => add n (mul m' n)

inductive le: mynat → mynat → Prop where
  | refl (n: mynat): le n n
  | step (m n: mynat): le m n → le m (succ n)

def one: mynat := succ zero
def two: mynat := succ one

instance: LE mynat where
  le := le

example: zero ≤ two := by
  repeat apply le.step
  apply le.refl

theorem zero_le (n: mynat): zero ≤ n := by
  induction n with
  | zero => apply le.refl
  | succ n' ih =>
    apply le.step
    exact ih

theorem le_refl (n: mynat): n ≤ n :=by
  apply le.refl

theorem le_trans {m n k: mynat}: m ≤ n → n ≤ k → m ≤ k := by
  intro h1 h2
  --h1 is proof of m ≤ n
  --h2 is proof of n ≤ k
  cases h1
  case refl =>
    --h1 is le.refl n, meaning m = n
    exact h2
  case step n' h3 =>
    --h1 is le.step m n' h3, meaning h3: m ≤ n' and n = succ n'
    --goal: m ≤ k
    induction h2 with
    --le is inductively defined with base case le.refl
    --and step case ih: m ≤ k' to prove m ≤ k'.succ
    |refl =>
      --h2 is le.refl k, meaning n = k
      --goal: m ≤ n'.succ
      apply le.step
      --goal: m ≤ n'
      exact h3
    |step k' h4 ih=>
      --h2 is le.step n k' h4, meaning h4: n ≤ k' and k = succ k'
      --ih: m ≤ k'
      --goal: m ≤ k'.succ
      apply le.step
      --goal: m ≤ k'
      exact ih
/-
# rec
used for defining recursive functions on inductive types
def inductivetype.rec {motive} (base case)(inductive case)
# motive
{motive: inductivetype → Type}
-/

#check rec (motive := λ _ => mynat)--mynat → (mynat → mynat→ mynat) → mynat→ mynat

--base case: mynat
-- inductive step function: mynat → mynat → mynat
-- step input: mynat
-- output: mynat
noncomputable def fctrl: mynat → mynat:=
  rec
    one
    (λ n fctrl_n => mul (succ n) fctrl_n)

example: fctrl zero = one := rfl

def tuple: ℕ → Type
  | 0 => Unit
  | n+1 => ℕ × tuple n

theorem tuple1: (tuple 1) = (ℕ × Unit) := by
  unfold tuple
  unfold tuple
  rfl
