-- Proof of transitivity of implies
example : ∀ (P Q R : Prop), (P → Q) → (Q → R) → (P → R) :=
begin
  assume P Q R,
  assume pimpq qimpr,
  assume p,
  apply qimpr,
  apply pimpq p,
end

-- same as above, but using straight up lean rather than tactic mode
example : ∀ (P Q R : Prop), (P → Q) → (Q → R) → (P → R) :=
λ P Q R pq qr p,
  qr (pq p)

example : ∀ (P : Prop), P ∧ ¬P → false :=
begin
  assume (P : Prop),
  assume (pnp : P ∧ ¬ P),
  cases pnp with p np,
  apply np p,
end

-- proof that a natural number is or is not zero
example : ∀ (n : nat), n = 0 ∨ n ≠ 0 :=
begin
  assume n,
  cases n,
  apply or.inl,
  apply refl,
  apply or.inr,
  assume nneqzero,
  cases nneqzero,
end

-- same as above
example : ∀ (n : nat), n = 0 ∨ n ≠ 0 :=
λ (n : nat),
  match n with
  | nat.zero := or.inl (eq.refl _)
  | nat.succ n' := or.inr (λ (nneqzero),
                            match nneqzero with
                            end)
  end

-- proof that there exists some number, m, such that m=n+2 for all n ∈ ℕ.
example : ∀ (n : ℕ), ∃ m, m = n+2 :=
begin
  assume n,
  apply exists.intro (n+2),
  apply refl,
end