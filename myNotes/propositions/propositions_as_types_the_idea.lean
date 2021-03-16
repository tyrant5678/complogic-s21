/-
Propositions as types: the very idea.
-/

/-
Prop        Sort 0
Type 0      Sort 1
Type 1      Sort 2
Type 2      Sort 3       
...         ...
-/

/-
Idea #1. Use types to represent
logical propositions and values of
these types to represent "evidence" 
or "proofs" of truth. A type that
is inhabited we then judge to be
logically true, and one that is 
uninhabited we judge to be false. 
-/

/-
Idea #2. When we use values of a
type only to represent evidence
of logical truth, then it doesn't
really matter *which* value of a
type we pick as evidence. To the 
first order, we don't care which
proof of a theorem a mathematician
produces, only that there is at
least one. And indeed, any proof
will do to justify a judgment that
a proposition is true. So when we
represent propositions as types and
proofs as values, in some sense we
want every proof of a given type to
be equivalent to any other. We want
every value of a "logical" type to
be equivalent to any other. Making
this equivalence of proof terms is
one of the main purposes of the last
of Lean's type universes, which we 
now introduce: Prop. 
-/

inductive its_raining : Prop 
| i_see_rain_falling : its_raining   --- both of these serve as evidence to show the prop is true
| i_hear_rain_on_roof : its_raining  --- |

-- THE ABOVE IS A TRUE PROPOSITION BECAUSE IT IS AN INHABITED TYPE

inductive one_equals_two : Prop

-- THE ABOVE IS A FALSE PROPOSITION BECAUSE IT IS AN UNIHABITED TYPE

inductive streets_wet : Prop
| i_see_wet_streets : streets_wet
| i_feel_wet_streets : streets_wet

open its_raining streets_wet

/-
def, lemma, and theorem all mean the same thing when
it comes to defining propositions, generally, the difference
comes to the natural english understanding of the word

lemma - intermediate proof
theorem - final big boi result
def - just defining some arbitrary data type  
-/
def proof_1'' : its_raining := i_see_rain_falling
def proof_2'' : its_raining := i_hear_rain_on_roof

lemma proof_1' : its_raining := i_see_rain_falling
lemma proof_2' : its_raining := i_hear_rain_on_roof

theorem proof_1 : its_raining := i_hear_rain_on_roof
theorem proof_2 : its_raining := i_see_rain_falling
/-
Don't care which val of a propositional type is used.
Values built by different constructors in Type n are
always NOT equal. This is the idea that "constructors
are injective and disjoint."

Consequence: No proof irrelevance :(

What can we do to fix this?
-/

/-
Prop        Sort 0
Type 0      Sort 1
Type 1      Sort 2
Type 2      Sort 3       
...         ...
-/

/-
In order to fix this issue, we just have to define our propositions as living in Prop rather
than Type n.
-/
/-
We just don't care which value of a
propositional type is used. When we 
see *equality* we'll find that values
build by different constructors in 
Sort n, for n > 0, are always NOT
equal, whereas all values of a type
in Sort 0, or Prop, are deemed equal.
Because different proof terms are
equivalent, they carry no information
beyond being evidence of truth. This
is the principle of proof irrelevance.
-/

/-
Just as we can represent propositions
as types, we can represent *predicates*
as type families, i.e., propositions
with parameters.
-/

inductive day : Type 
| su | mo | tu | we | th | fr | sa 

open day

/-
A type family indexed by day representing
the predicate ⟨ always_rains_on d ⟩, where
d is a parameter of type day. Providing a
value for d yields a specific proposition
in the family of propositions we've defined, 
namely one claims that a specific day, d, is
always rainy. 
-/

/-
When you see something like Type → Prop, this means you
are creating a predicate with a parameter.
-/
inductive always_rains_on : day → Prop
| mo_rainy : ∀ (d : day), (d = mo) → always_rains_on d

#check always_rains_on
#check always_rains_on su
#check always_rains_on mo
#check always_rains_on tu



lemma bad_tuesdays : always_rains_on tu := _  -- stuck
lemma bad_fridays : always_rains_on tu := _   -- stuck
lemma bad_mondays : always_rains_on mo := mo_rainy mo _

