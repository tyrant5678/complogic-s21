namespace hidden

universe u
/-
Syntactic alternative:
class has_mul (α : Type u) := (mul : α → α → α)
-/
/-
creating the has_mul'' typeclass
can create a member of the type class for any type that has a func
that is of type α → α → α
-/
structure has_mul'' (α : Type u): Type (u+1) := 
(mul : α → α → α)
--Creating bool and nat members of has_mul''
def has_mul''_bool : has_mul'' bool := has_mul''.mk band
def has_mul''_nat : has_mul'' nat := has_mul''.mk nat.mul

/-
has_mul''_bool has a field called mul, and can check this type to
see that has_mul''_bool.mul is of type bool → bool → bool

Further, we can see that has_mul''_bool.mul called with 2 args is a bool as well.
-/
axioms (b1 b2 : bool)
#check has_mul''_bool.mul
#check has_mul''_bool.mul b1 b2

--The same deal exists w/ nats
def n1 := 3
def n2 := 4
--This line evals to 12!
#eval has_mul''_nat.mul 3 4

--Can we make the type implicit?
structure has_mul' {α : Type u}: Type (u+1) := 
(mul : α → α → α)

-- Now we've made the type i mplicit!
def has_mul'_bool : has_mul'  := has_mul'.mk band
def has_mul'_nat : has_mul'  := has_mul'.mk nat.mul
 
-- we can now use our implem entation of mul ANYWHERE!
def my_fancy_mul : ℕ → ℕ → ℕ 
| n1 n2 := has_mul'_nat.mul  n1 n2

#eval my_fancy_mul 3 4

-- but we still have to know the name of our typeclass instance...

-- This is our final implementation, a Typeclass in Lean.
@[class] -- This denote we are defining a type class using a structure
structure has_mul (α : Type u): Type (u+1) := 
(mul : α → α → α)

--Creating "instances" of members of their typeclasses
instance has_mul_bool : has_mul bool := has_mul.mk band
instance has_mul_nat : has_mul nat := has_mul.mk nat.mul
/-
When we create typeclass instances, they get stored in a database and
the typeclass inference mechanism can find these instances by type.
-/

/-
What do typeclasses give us?
-/

/-
Implicit instance arguments
-/

--allows us to define some polymorphic function with the assumption
--that there exists a mul function for that type
def my_fancy_mul' (α : Type) [tc : has_mul α]: α → α → α := tc.mul

#eval my_fancy_mul' nat 2 3
end hidden
