/-
true,
false,
true and true
true and false
(true and false) and true
-/

inductive bool_expr : Type 
| lit_expr : bool → bool_expr
| and_expr : bool_expr → bool_expr → bool_expr
-- is equiv to...
inductive bool_expr' : Type
| TT : bool_expr'
| FF : bool_expr'
| and_expr : bool_expr' → bool_expr' → bool_expr'

open bool_expr

def true_expr : bool_expr := lit_expr tt
def false_expr : bool_expr := lit_expr ff
def e3 := and_expr (lit_expr tt) (lit_expr ff)
def e4 := and_expr e3 (lit_expr tt)

notation e1 && e2 := and_expr e1 e2
notation '['b']' = lit_expr b
def e3' := (lit_expr tt) && (lit_expr ff)
def e4' := e3 && (lit_expr ff)
-- That's syntax!

-- semantics

def bool_eval : bool_expr → bool
| TT := tt
| FF := ff
| (and_expr e1 e2) := band (bool_eval e1) (bool_eval e2)

#eval bool_eval e4'

-- We've now created the syntax and semantics of a small language!
