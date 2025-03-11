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
  let val : Nat := sqm.val * sqn.val
  have h: val* val = m*n := by
    --goal: val*val = m*n
    unfold val
    --goal: sqm.val*sqn.val*sqm.val*sqn.val = m*n
    simp [← sqm.issqrt,← sqn.issqrt]
    --goal: sqm.val*sqn.val*(sqm.val*sqn.val) =
    --sqm.val*sqm.val*(sqn.val*sqn.val)
    rw[← Nat.mul_assoc]
    --goal: sqm.val*sqn.val*sqm.val*sqn.val =
    --sqm.val*sqm.val*(sqn.val*sqn.val)
    rw[Nat.mul_assoc sqm.val sqn.val sqm.val]
    rw[Nat.mul_comm sqn.val sqm.val]
    rw[← Nat.mul_assoc]
    --goal: sqm.val*sqm.val*sqn.val*sqn.val =
    --sqm.val*sqm.val*(sqn.val*sqn.val)
    rw[Nat.mul_assoc (sqm.val*sqm.val) sqn.val sqn.val]
    --goal: no goals
  ⟨val, h⟩

/-
# enumerative inductive types
deriving Repr - automatically generates a string representation allowing values to be printed by #eval
deriving Inhabited - automatically generates a default value usually the first constructor
deriving DecidableEq - automatically generates a decidable equality between values
-/

inductive ans where
  | yes : ans
  | no : ans
  | maybe : ans
  deriving Repr, Inhabited, DecidableEq

--using Repr
#eval ans.yes -- ans.yes
#eval repr ans.yes -- "ans.yes"

#check ans.yes -- ans
#check repr ans.yes -- Std.Format (text)

--using Inhabited
#eval (default: ans) -- ans.yes

--using DecidableEq
#eval ans.yes = ans.no -- false


/-defining a function on the inductive type.
values of inductive type can be mentioned without the namespace (eg: ans.yes)
-/
def ans.or (a b: ans): ans :=
  match a, b with
  | yes, _ => yes
  | _, yes => yes
  | no, no => no
  | _, _ => maybe

#eval ans.or ans.yes ans.no -- ans.yes
/-
open - opens the namespace
open...in - opens the namespace only in the following block
-/

open ans in
#eval or maybe no -- ans.maybe

def ans.not (a: ans): ans :=
  match a with
  | yes => by
    apply no
  | no => by
    exact yes
  | maybe => maybe

/-
# non-recursive inductive type
-/

inductive answer where
  | just (a: ans): answer
  | because (a: ans)(reason: String): answer

example: answer := answer.just ans.yes

-- shortened version of answer

def answer.short (a: answer) : ans :=
  match a with
  | just a' => a'
  | because a' _ => a'

--different notation for match

def answer.short': answer → ans
  | just a' => a'
  | because a' _ => a'

def eg1: answer := answer.because ans.no "no reason"

open answer in
#eval short eg1 -- ans.no
--different way to apply function - dot notation
#eval eg1.short -- ans.no

#eval answer.short' eg1 -- ans.no

--long answer
inductive long_answer where
  | just (a: ans): long_answer
  | because (a: long_answer)(reason: String): long_answer

def long_answer.eg3: long_answer :=
  long_answer.because
    (long_answer.because
      (long_answer.just ans.yes)
      "idk")
    "not sure"

--short answer
def long_answer.short: long_answer → ans
  | long_answer.just a => a
  | long_answer.because a _ => long_answer.short a

--expanded version
def long_answer.short': long_answer → ans:=
  λ a =>
    match a with
    | long_answer.just a' => a'
    | long_answer.because a' _ => long_answer.short' a'

--long answer from short
def ans.just (a: ans): long_answer :=
  long_answer.just a

def ans.because (a: long_answer)(reason: String): long_answer :=
  long_answer.because a reason

--examples
def long_answer.eg4: long_answer :=
  ans.yes.just.because "idk"

def long_answer.eg5: long_answer :=
  because (just ans.yes) "idk"

-- |>. - takes output of previous function as input to the next
def long_answer.eg6: long_answer :=
  ans.yes
  |>.just
  |>.because "idk"
