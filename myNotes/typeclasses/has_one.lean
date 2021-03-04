import .my_has_mul

namespace hidden

universe u

@[class]  
structure has_one (α : Type u) extends has_mul α := 
-- mul : α → α → α  inherited from has_mul
/-
defines that there is some notion of "one" for any given type of object
given that there exists a mul function for that type
-/
(one: α)
/-
Defines a left identity for one and any value of a of type α
-/
(one_mul : ∀ (a : α ), mul one a = a)
/-
Defines a right indentity for one and any value of a of type α
-/
(mul_one : ∀ (a : α ), mul a one = a )
--        ^^^^^^^^^^^^^^ propositions
-- These are proofs for these properties

end hidden