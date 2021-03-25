/-
A total func

-- set theoretic view of a func
sqr : ℕ → ℕ := { (0,0) , (1,1), (2,4), (3,9)}
-/

/-
Computational representation of the function
-/

def sqr : ℕ → ℕ := λ n, n*n 

#eval sqr 3

/-
Logical, declarative predicate that defines the same function
-/

inductive sqr_pred : ℕ → ℕ → Prop
| in_sqr_pred : ∀ (n1 n2 : ℕ), (n2=n1*n1) → sqr_pred n1 n2

open sqr_pred

--explicit proof term

example : sqr_pred 3 9 := in_sqr_pred _ _ (eq.refl _)

-- same thing but in tactic mode

example : sqr_pred 3 9 :=
begin
  apply in_sqr_pred _ _,
  exact eq.refl 9,
end

-- same exercise but for 4 and 16

example : sqr_pred 4 16 := in_sqr_pred _ _ (eq.refl _)

example : sqr_pred 4 16 :=
begin
  apply in_sqr_pred _ _,
  -- can also use "exact eq.refl _" b/c lean infers the 16 here
  exact eq.refl 16,
end

example : sqr_pred 3 15 :=
begin
  apply in_sqr_pred _ _,
  -- this doesn't work b/c eq.refl CANNOT proivde a proof that 3*3=15
  exact eq.refl _,
end

/-

-/

-- may want to write specification, then implement, then write some function to verify
theorem verification : ∀ (n1 n2 : ℕ ), sqr_pred n1 n2 → sqr n1 = n2 :=
begin
  assume n1 n2,
  assume h,
  cases h,
  -- simplify using the function sqr
  simp [sqr], 
  apply eq.symm _,
  assumption,
end

/--
Patial func:

sqr_evn, sqr but only defined for even numbers
-/

def evn : ℕ → bool := λ n, n%2=0

inductive sqr_ev_pred : ℕ → ℕ → Prop
| in_sqr_ev_pred : ∀ (n1 n2 : ℕ), (n1%2=0) → (n2 = n1 * n1) → sqr_ev_pred n1 n2

open sqr_ev_pred
 -- unfold replaces a definition on the left of a := with the value on the right
example : sqr_ev_pred 4 16 :=
begin
  apply in_sqr_ev_pred,
  exact eq.refl 0,
  exact eq.refl 16,
end