/-
HIGHER-ORDER FUNCTION WARMUP
-/

/-
1. Write a function, double, that takes
a natural number and returns its double.
Write it using the following recursive
definition:
- double 0 = 0
- double (n' + 1) = double n' + 2
-/


-- ANSWER HERE

def double : ℕ → ℕ
| 0 := 0
| (n' + 1) := double n'+2

/-
2. Write a function, map_list_nat, that 
takes as its arguments (1) a list, l, of 
natural numbers, and (2) a function, f, 
from nat to nat, and that returns a new 
list of natural numbers constructed by 
applying f to each element of l. Make f
the first argument and l the second. The
function will work by case analysis and
recursion on l.
-/

-- ANSWER HERE
 def map_list_nat : list nat → (ℕ → ℕ) → list nat
 | list.nil _ := list.nil
 | (list.cons h t) f := list.cons (f h) (map_list_nat t f)
/-
3. Test your map_list_nat function by
applying it to several lists, both empty
and not, passing double as the function
value. Include [], [2], and [1,2,3] in
your set of test inputs and use comments
to document the expected return values.
-/
def l1 : list nat:= list.nil
def l2 := list.cons 2 list.nil 
def l3 := list.cons 1 (list.cons 2 (list.cons 3 (list.nil)))

--should be empty list
#eval map_list_nat l1 nat.succ
--should be [3]
#eval map_list_nat l2 nat.succ
--should be [2,3,4]
#eval map_list_nat l3 nat.succ

/-
4. In Lean, repr is an "overloaded"
function. When applied to a value of a
type for which it's defined (we'll see 
later  how that happens) it returns a
string representation of the value. It
is defined for the nat type, and so 
when applied to a nat value it returns
a corresponding string. It's "toString"
for Lean. Here's an example.
-/

#eval repr 5

/-
Write a function map_list_nat_string
that takes a list of nat values and
returns a list of strings in which
each nat in the given list has been
converted to a string using repr.
-/

-- ANSWER HERE
def map_list_nat_string : list nat → list string
| list.nil := list.nil 
| (list.cons h t) := list.cons (repr h) (map_list_nat_string t)

/-
5. Write a function, filterZeros,
that takes a list of natural numbers
and returns the same list but with any
and all zero values removed. Given
[0], for example, it should return
[]; given [1,2,0,3,4,0, 0, 5] it 
should return [1,2,3,4,5].
-/

-- ANSWER HERE
def filterZeros : list nat → list nat
| list.nil := list.nil
| (list.cons 0 t) := filterZeros t
| (list.cons h t) := list.cons h (filterZeros t)

/-
6. Write a function, isEqN, that
takes a natural number, n, and returns
a function that takes a natural number,
m, and returns true (tt) if m = n and
that returns false (ff) otherwise. Be
sure to test your function.
-/

-- ANSWER HERE
def isEqN : ℕ → (ℕ → bool)
| n := λ m, 
        if n=m then tt else ff

--expected: ℕ → bool 
#check isEqN 2
--expected: tt
#eval isEqN 2 2
--expected: ff
#eval isEqN 2 3
/-
7.
Write a function filterNs that takes
a function, pred, from nat to bool 
and a list, l, of natural numbers, and
that returns a list like l but with all
the numbers that satisfy the predicate
function removed. Test your function
using isEqN to produce a few predicate
functions (functions that for a given
argument return true or false).
-/

-- ANSWER HERE
def filterNs : (ℕ → bool) → list nat → list nat
| _ list.nil := list.nil 
| f (list.cons h t) := if f h
                       then filterNs f t
                       else list.cons h (filterNs f t)

#eval filterNs (isEqN 2) l3
/-
8. Write a function, iterate, that 
takes as its arguments (1) a function, 
f, of type nat → nat, and (2) a natural
number, n, and that returns a function 
that takes an argument, (m : nat), and
that returns the result of applying f 
to m n times. For example, if n = 3, it
should return f (f (f m)). The result
of applying f zero times is just m.
Hint: use case analysis on n, and 
recursion. Test your function using 
nat.succ, your double function, and
(nat.add 4) as function arguments. 
-/

-- ANSWER HERE
def iterate : (ℕ → ℕ) → ℕ → (ℕ → ℕ)
| f 0 := λ (m : ℕ), m
| f (n+1) := λ (m : ℕ), f (iterate f n (m))

--testing w/ nat.succ
--expected: 6
#eval iterate nat.succ 5 1
--expected: 1
#eval iterate nat.succ 0 1
--testing w/ double
--expected: 32
#eval iterate double 4 2
--expected 56
#eval iterate double 0 56
--testing w/ nat.add 4
--expected: 25
#eval iterate (nat.add 4) 5 5
--expected 5
#eval iterate (nat.add 4) 0 5
/-
9. Write a function, list_add, that takes
a list of natural numbers and returns the
sum of all the numbers in the list.
-/

-- ANSWER HERE
def list_add : list nat → ℕ
| list.nil := 0
| (list.cons h t) := h + (list_add t)

/-
10. Write a function, list_mul, that takes
a list of natural numbers and returns the
product of all the numbers in the list.
-/

-- ANSWER HERE
def list_mult : list nat → ℕ
| list.nil := 1
| (list.cons h t) := h * (list_mult t)

/-
11. Write a function, list_has_zero, that
takes a list of natural numbers and returns
tt if the list contains any zero values and
that returns false otherwise. Use isEqN in
your solution. Test your solution on both
empty and non-empty lists including lists
that both have and don't have zero values.
-/

-- ANSWER HERE
def list_has_zero : list nat → bool
| list.nil := ff
| (h::t) := if (isEqN 0 h) then tt else list_has_zero t

def l4 := [1,0,9,2,3]
def l5 := [0,0,0,0,0]

#eval list_has_zero l1
#eval list_has_zero l2
#eval list_has_zero l4
#eval list_has_zero l5

/-
12. Write a function, compose_nat_nat,
that takes two functions, f : ℕ → ℕ,
and g : ℕ → ℕ, and that returns a
function that takes a nat, n, and that
returns g (f n). Test your function 
using at least nat.succ and double as
argument values.
-/

-- ANSWER HERE
def compose_nat_nat : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ)
| f g := λ n, g (f n)

#eval compose_nat_nat nat.succ double 3
#eval compose_nat_nat double nat.succ 3
/-
13. Write a polymorphic map_box function
of type 

Π (α β : Type u), 
  (α → β) → box α → box β  
  
that takes a function, f, of type 
(α → β), and a box, b, containing a 
value of type α and that returns a 
box containing that value transformed
by the application of f.  
-/
universe u
-- ANSWER HERE

--creating the box data type here, taken from the box.lean file

structure box (α : Type u) : Type u :=
(val : α)

def map_box : Π {α β : Type u}, (α → β) → box α → box β :=
λ (α β:Type u) (f : α → β),
  λ b,
    box.mk (f b.val)

def map_box' : Π {α β : Type u}, (α → β) → box α → box β
| _ _ f bo := box.mk (f bo.val)

#reduce map_box' (nat.add 5) (box.mk 2345)
/-
14. 
Write a function, map_option, that
takes a function, f, of type α → β
and an option α and that transforms
it into an option β, where none goes
to none, and some (a : α) goes to
some b, where b is a transformed by 
f.
-/

-- ANSWER HERE
def map_option {α β : Type u} : (α → β) → option α → option β
| f (some a) := some (f a) 
| _ none := none

/-
15. Write three functions, default_nat,
default_bool, and default_list α, each
taking no arguments (other than a type,
argument, α, in the third case), and 
each returning a default value of the
given type: a nat, a bool, and a list.
Don't overthink this: Yes, a function
that takes no arguments is basically 
a constant. You'll need to declare a
universe variable for the list problem.
-/

-- ANSWER HERE

def default_nat : ℕ := 0
def default_bool : bool := ff
def default_list (α : Type u): list α := list.nil
