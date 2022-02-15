/-
If P is a proposition then so is ¬P.
-/

axiom excl_middle : ∀ (P : Prop), P ∨ ¬ P

axiom KevinIsFromCville : Prop

example : KevinIsFromCville ∨ ¬ KevinIsFromCville :=
excl_middle KevinIsFromCville

/-
To construct a proof of Π for some proposition P,
we need to show that there can be no proof of P.
To show there can be no proof of P we assume that
there is a proof of P and show that this leads to
a contradition.

What do we mean by a contradiction.
-/

#check false

namespace hidden

def not (P : Prop) : Prop := P → false 

end hidden

#check not

example : ¬ 0 = 1 := 
begin
  show not (0 = 1),
  -- the result of this application
  -- is the proposition (0=1) → false.
  assume h,
  cases h,
end

example : false → KevinIsFromCville :=
begin
  assume f,
  cases f,
end

/-
For any proposition at all, if false is
true then that proposition, P, is true. 
One way to understand this is that if false
is true, then anything is true, because if
it's true, it's true, and if it's false it's
also true.
-/
theorem exfalso : ∀ (P : Prop), false → P :=
begin
  intro P,
  assume f,
  cases f,
end

theorem non_contradition : ∀ (P : Prop), ¬ (P ∧ ¬P) :=
begin 
  intro P,
  assume h,
  cases h with p np,
  have f := _,
end

/-
Is the following proposition valid in Lean
-/

example : ∀ (P : Prop), ¬ ¬ P → P :=
begin
  intro P,
  assume h,
  -- no use of classical reasoning allowed.
  -- stuck! this is not a theorem in
  -- the constructive logic of Lean
  -- or Coq, or ...
end

#check classical.em

/-
∀ (p : Prop), p ∨ ¬p
-/

example : ∀ (P : Prop), ¬ ¬ P → P :=
begin
  intro P,
  assume h,
  -- stuck! this is not a theorem in
  -- the constructive logic of Lean
  -- or Coq, or ...
  have o := classical.em P,
  cases o,
  assumption,
  contradiction,
  /-
  have f := h o,
  cases f,
  -/
end

/-
If we assume the law of the excluded middle,
then negation elimination, ¬¬P → P, is valid.
-/

/-
That ¬¬P → P is the essence of proof by 
contradiction. Let's start by noting that
we now have two different proof techniques
involving contradictions.

In "proof by negation," we prove ¬P by 
assuming P and showing that that leads
to a contradiction (essentially a proof
of false). That is, to prove ¬P we prove
P → false.

By contrast, proof by contradiction seeks
to prove P by assuming ¬P and showing that
that leads to a contradiction. That is, we
seek to show ¬P → false, which is just what
we mean by ¬¬P. *THEN*, having showing ¬¬P,
we apply (classical) negation elimination
to deduce P. 

What we've seen today, then, is that while
proof by negation is "constructively valid"
proof by contradiction is *not*. However it
is valid if we assume the classically axiom 
of the excluded middle. That's precisely 
what allows us to infer P from ¬¬P, as we
have just seen.
-/
