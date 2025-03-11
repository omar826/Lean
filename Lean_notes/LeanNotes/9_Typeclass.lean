import Mathlib
/-
# Type classes
type classes are defined similar to structures
-/

class Alone where
  (alone: Bool)

#check Alone.alone--Bool
--create an instance before synthesizing
instance: Alone := ⟨true⟩--unnamed instance

--synthesis displays the instance
#synth Alone--instAlone

instance inst2 : Alone := ⟨false⟩
instance inst3 : Alone := ⟨true⟩

#synth Alone--inst3

#check Alone--Type
#check Alone.alone--[self: Alone] → Bool
#eval Alone.alone--true
-- instance

def myAlone {hi: Alone} : Bool := hi.alone
