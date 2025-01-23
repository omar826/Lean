/-
# Function Abstraction
write functions without naming them
start expression with λ or fun
↦ is typed as \map
-/

#check λ (x : Nat) ↦  x + 5 -- Nat → Nat
#check λ x ↦ x + 5 -- Lean can infer Nat → Nat

#eval (λ x ↦ x + 5) 3 -- 8

--# multiple arguments

#check λ x:Nat ↦ λ y: Bool ↦ if not y then x else 0 -- Nat → Bool → Nat
#check λ (x: Nat) (y: Bool) ↦ if not y then x else 0 -- Nat → Bool → Nat
#check λ x y ↦ if not y then x else 0 -- Lean can infer Nat → Bool → Nat

-- function composition
def f(n: Nat): String := toString n
#eval f 5 -- "5"

def g(s: String): Bool := s.length>0

#check λ x ↦ g (f x) -- Nat → Bool

#check λ (a b c: Type) (f: a → b) (g: b → c) ↦ g ∘ f -- Type → Type → Type → (a → b) → (b → c) → a → c

/-
argument names only have local scope
# Function Definition
-/

def sum (x: Nat) (y: Nat): Nat := x + y
def sum' (x y: Nat) := x + y
def sum'' := λ (x y: Nat) ↦ x + y
def sum''' (x: Nat) := λ y: Nat ↦ x + y

#check sum -- Nat → Nat → Nat
#check sum' -- Nat → Nat → Nat
#check sum'' -- Nat → Nat → Nat
#check sum''' -- Nat → Nat → Nat

def greater (x y: Nat):=
  if x > y then x
  else y

/-
# Local Definitions
-/

#check let x := 5; x + 3 -- Nat
#eval let x := 5; x + 3 -- 8

def sum2 (x y: Nat): Nat :=
  let z := x + y
  z + z
#eval sum2 3 4 -- 14

def add2 :=
  let y:= Nat; fun x: y ↦ x + 2
#eval add2 3 -- 5

/-
# Variables
-/

def apply (α β: Type) (f: α → β) (x: α): β := f x
#check apply -- Type → Type → (α → β) → α → β

variable (α β: Type)
variable (f: α → β)
variable (x: α)

def apply' := f x
#check apply' -- Type → Type → (α → β) → α → β

#print apply'
/-
#print - shows internal structure of an object
-/

/-
# Sections
limit the scope of variables
need not be named
-/
section blah
  variable (α β: Type)
  variable (g: α → β)
  variable (x: α)

  def apply'' := g x
end blah

/-
# Namespaces
group definitions and limit their scopes
-/

namespace foo
  def a := 5
  def b := 7
end foo

--#check a -- error
#check foo.a -- Nat
open foo
#check a -- Nat

/-
# Dependent Type Theory
Type depends on argument
-/

#check @List.cons--{α : Type u_1} → α → List α → List α

/-
# Implicit Arguments
_ - infer argument
{α: Type} - implicit named argument
@ - before function call makes the arguments explicit

-/
#check id -- {u}{α: Type u}(a: α) → α. returns a.
#check id 1 -- Nat
#eval id 1 -- 1
#check id "hello" -- String
#check @id Nat -- Nat → Nat
#check @id Nat 1 -- Nat
#check @id _ 1 -- Nat

def doublelist (l: List α ){α : Type} := l++l
#check doublelist -- (α : Type) (l : List α) : {α✝ : Type} → List α
def doublelist' (α : Type) (l: List α): List α  := l++l
#eval doublelist' Nat [1,2]--[1,2,1,2]
#eval doublelist' _ [1,2]--[1,2,1,2]

def doublelist'' {α : Type} (l: List α):= l++l
#eval doublelist'' [1,2]--[1,2,1,2]
#eval @doublelist'' _ [1,2]--[1,2,1,2]

--#eval doublelist'' Nat [1,2] -- error implicit argument not to be provided
/-
# Named Arguments
-/
#eval doublelist'' (l := [1,2]) (α := Nat) -- [1,2,1,2]

/-
# Curried Functions
one argument at a time
-/

def h (m : Int) (n: Nat) : Int := m - n
def h': Int → Nat → Int := λ m ↦ λ n ↦ m - n

def composeSelf (f : Nat → Nat) (n : Nat) : Nat := f (f n)
def composeSelf' : (Nat → Nat) → (Nat → Nat) := λ f ↦ λ n ↦ f (f n)
