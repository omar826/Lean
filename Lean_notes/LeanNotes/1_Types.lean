/-
# Meta Commands
#check - returns type of the expression
#eval - evaluates the expression
- every expression has a type
# Unicodes
→ - \to
∧ - \and
∨ - \or
¬ - \not
∀ - \forall
∃ - \exists
↔ - \iff
× - \times
≠ - \ne
≤ - \le
≥ - \ge
∈ - \in
∉ - \notin
∅ - \emptyset
∩ - \cap
∪ - \cup
⊆ - \subseteq
⊇ - \supseteq
⊂ - \subset
⊃ - \supset
α - \a
β - \b
ℕ - \Nat
# Comments
- single line comments are written using --
- multi line comments are written using /- -/
- headings are written using #
- subheadings are written using ##
- bullet points are written using -
-/

#check 1 -- Nat
#check 1 + 1 -- Nat
#check 1 + 1 = 2 -- Prop
#check Nat -- Type
#check Type -- Type 1
#check Type 1 -- Type 2
#check Type 2 -- Type 3 etc
#check Prop -- Type

/-
# Define a constant
def <--name> : <--type> := <--expression>
-/
def a : Nat := 1
#check a -- Nat

def b : Bool := true
#check b && false-- Bool
#check b || false -- Bool
#check b → false -- Prop
#check b ↔ false -- Prop

#eval b && false -- false

/-
# Functions
def <--name> ( arg : arg_type) : output_type := <--expression>.
## Function Types
arg_type → output_type
-/

def f (x : Nat) : Nat := x + 1
#check f -- Nat → Nat
#check f 1 -- Nat
#check Nat → Nat -- Type

#check Nat → Nat → Nat -- Type
#check Nat → (Nat → Nat) -- Type
#check (Nat → Nat) → Nat -- Type

/-
# Cartesian Product
(a,b) has type type_a × type_b
-/
#check (1,2) -- Nat × Nat or Prod Nat Nat
#check (1,2).1 -- Nat
#eval (1,2).1 -- 1
#check (Nat, Bool) -- Type × Type

#check Nat × Nat -- Type
#check Nat × Bool -- Type
#check Prod Nat Bool -- Type

/-
# multiple arguments
f(x,y) has type type_x → type_y → type_output

→ is right associative
i.e. A → B → C is equivalent to A → (B → C)
-/

def sum (x : Nat) (y : Nat) : Nat := x + y
#check sum -- Nat → Nat → Nat
#check sum 1 -- Nat → Nat
#check sum 1 2 -- Nat
#eval sum 1 2 -- 3

/-
# Universes
Type 0 is a universe containing Nat, Bool, Nat → Nat, etc
Type n+1 is a universe containing Type n etc
-/

#check [1,2,3] -- List Nat
#check List Nat -- Type
#check List -- List.{u} (α : Type u) : Type u
-- here u is a variable representing a universe
-- ∴ List a has type type_a
#check List Type -- Type 1

#check Prod -- Prod.{u v} (α : Type u) (β : Type v) : Type (max u v)
#check Prod Nat Bool -- Type
#check Prod Nat Type -- Type 1

/-
# Explicitly Declare Universe Variables
-/
universe u
def F (α : Type u) : Type u := α × α
#check F -- Type u → Type u

/-
# Local Universe Variables
-/
def G (α : Type _) : Type _ := α × α
#check G -- Type u_1 → Type u_1

def H.{u2} (α : Type u2) : Type u2 := α × α
#check H -- Type u2 → Type u2
