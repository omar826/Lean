/-
# Inductive types
inductive (name) where
  | (constructor) : (type) → (name)
  | (constructor) : (type) → (name)

  | - is optional, we can use ',' to separate constructors

-/

inductive day where
  | monday : day
  | tuesday : day
  | wednesday: day
  | thursday: day
  | friday: day
  | saturday: day
  | sunday: day
-- new type day is created
-- the 7 constructors live in the day namespace

#check day -- Type
#check day.monday -- day

open day
#check monday -- day

-- day may be omitted in the constructor
inductive day' where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

/-
# match
used for pattern matching in inductive types
-/

def day_to_num (d: day): Nat :=
  match d with
  | monday => 1
  | tuesday => 2
  | wednesday => 3
  | thursday => 4
  | friday => 5
  | saturday => 6
  | sunday => 7

#eval day_to_num monday -- 1

def is_1or0 (n: Nat): Bool :=
  match n with
  | 0 => true
  | 1 => true
  | _ => false

#eval is_1or0 3 -- false
#print day_to_num -- prints defn of day_to_num

/-
* rep - defines recursion on inductive types
* repr - string representation of constructors
-/

#check day.rec

inductive day'' where
  | monday : day''
  | tuesday : day''
  | wednesday: day''
  | thursday: day''
  | friday: day''
  | saturday: day''
  | sunday: day''
  deriving Repr
#eval monday -- day.monday
#eval day'.monday -- day'.monday
#eval day''.monday -- day''.monday

#check monday
#check day''.monday

def fib (n: Nat): Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n+2 => (fib (n+1)) + (fib (n))

#check fib 5 -- Nat
#eval fib 8 -- 21
-- partial def because termination not proved

/-
# Predefined inductive types
## Prod
Prod.mk : α → β → α × β
Prod.mk a b = (a, b)
Prod α β = α × β
Prod.fst Prod.mk a b = a
Prod.snd Prod.mk a b = b
-/

#check Nat.lt_succ_self -- ∀ (n : ℕ), n < n.succ
def numSteps (step: Nat → Nat)(h : ∀n: Nat, step (n + 1) ≤ n)
    (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    have h1: step (n + 1) < n + 1 := by
      apply Nat.lt_add_one_of_le
      apply h
    numSteps step h (step (n + 1)) + 1
    termination_by n

#check Nat.lt_add_one_of_le -- ∀ (n m : ℕ), n.succ ≤ m → n < m

/-
structure - like inductive types but with named fields
if sqrt is a structure, sqrt.mk is a constructor
⟨,⟩ - can also be used to construct a structure
{field1 := val1, field2 := val2} - can be used to construct a structure
-/

structure Natsqrt (n: Nat) where
  val: Nat
  issqrt: val*val = n -- issqrt is a proof that val*val = n

#check Natsqrt -- Nat → Type
#check Natsqrt.mk -- Natsqrt.mk {n: Nat}(val: Nat)(isSqrt: val*val = n): Natsqrt n
#check Natsqrt.issqrt-- Natsqrt.issqrt {n: Nat} (self: Natqrt n): self.val * self.val = n

def sqrt4: Natsqrt 4 := ⟨2, rfl⟩
def sqrt9: Natsqrt 9 := Natsqrt.mk 3 rfl

#check sqrt4 -- Natsqrt 4
#eval sqrt4 -- {val := 2, issqrt := rfl}
#eval sqrt4.val -- 2

/-
let - local defn of variable
have - local hypothesis that requires a proof
-/
def sqrt_prod {m n: Nat} (sqn: Natsqrt n)(sqm: Natsqrt m): Natsqrt (m*n) :=
  let
