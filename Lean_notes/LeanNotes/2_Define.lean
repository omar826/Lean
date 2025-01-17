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
