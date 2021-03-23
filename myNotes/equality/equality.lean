

/-
Properties and Relations: Type Families
-/

#check @eq

--  Π {α : Sort u_1}, α → α → Prop

#check eq 1 0 -- 1 = 0
#check eq 1 1 -- 1 = 1

/-
Introduction: construct a term
-/

-- eq is type, refl is its sole constructor
#check @eq.refl

-- ∀ {α : Sort u_1} (a : α), a = a

-- want to construct a value of type eq 1 0 (impossible!)
example : eq 1 0 := _
-- try to construct a term of type eq 1 1, which we do by calling eq.refl
example : eq 1 1 := eq.refl 1

/-
Elimination: use a term to create something new
-/

#check @eq.subst

-- ∀ {α : Sort u_1} {P : α → Prop} {a b : α}, a = b → P a → P b

axioms  -- some assumptions we can work with
  (Person : Type) 
  (Kevin Robert : Person) 
  (livesInCville : Person → Prop)
  (klic : livesInCville Kevin)
  (keqr : Kevin = Robert)


-- write proof term
example : livesInCville Robert := 
-- use eq.subst to show that Kevin = Robert and that b/c Kevin lives in CVille, so
-- does Robert
  eq.subst keqr klic


-- use eq.subst
example : livesInCville Robert :=
begin
  apply eq.subst,
  exact keqr,
  exact klic,
end

universe u
theorem eq_is_symm : ∀ {α : Sort u} (a b : α), a = b → b = a :=
begin
  assume α a b,
  assume h,
  -- rw (rewrite) takes proof of equality and rewrite every occurence of the prop
  -- eg, if you have h a=b and you need to prove b=a, you will now need to prove
  -- b=b after rewrite
  rw h,
end

theorem eq_is_symm' : ∀ {α : Sort u} (a b : α), a = b → b = a :=
  λ (α a b h), eq.subst h (eq.refl a)


#check @eq.symm

-- tactic script
theorem eq_is_trans' : 
  ∀ {α : Sort u} (a b c : α), a = b → b = c → a = c :=
begin
 assume α a b c,
 assume a_eql_b b_eql_c,
 rw a_eql_b,
 rw b_eql_c,
end

 /-
 ALT DEF:
 -/
 
 theorem eq_is_trans : 
  ∀ {α : Sort u} (a b c : α), a = b → b = c → a = c :=
begin
  intros α a b c ab bc,
  rw ab,
  --two options: rw bc and exact bc, both will accomplish the goal
  -- a third option: assumption, just says that if you have some assumption that
  -- would prove curr. goal, you can just use that
  assumption,
end

-- HW: prove eq_is_trans by writing a proof term explicitly

#check @equivalence



/-
section relation
variables {α : Sort u} {β : Sort v} (r : β → β → Prop)
local infix `≺`:50 := r

def reflexive := ∀ x, x ≺ x

def symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

def transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

def equivalence := reflexive r ∧ symmetric r ∧ transitive r

def total := ∀ x y, x ≺ y ∨ y ≺ x

def mk_equivalence (rfl : reflexive r) (symm : symmetric r) (trans : transitive r) : equivalence r :=
⟨rfl, symm, trans⟩

def irreflexive := ∀ x, ¬ x ≺ x

def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

def empty_relation := λ a₁ a₂ : α, false

def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

def inv_image (f : α → β) : α → α → Prop :=
λ a₁ a₂, f a₁ ≺ f a₂

lemma inv_image.trans (f : α → β) (h : transitive r) : transitive (inv_image r f) :=
λ (a₁ a₂ a₃ : α) (h₁ : inv_image r f a₁ a₂) (h₂ : inv_image r f a₂ a₃), h h₁ h₂

lemma inv_image.irreflexive (f : α → β) (h : irreflexive r) : irreflexive (inv_image r f) :=
λ (a : α) (h₁ : inv_image r f a a), h (f a) h₁

inductive tc {α : Sort u} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c
end relation
-/

theorem eq_is_equiv : ∀ (α : Sort u), equivalence (@eq α)  := 
begin
end