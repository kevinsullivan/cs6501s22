import .bool_lang
import .bool_lang_semantics

-- IGNORE THIS FILE FOR NOW

namespace bool_lang
-- PROPERTIES?

/-
A property of an expression, e, is that e
evaluates to true. Let's call this property
evaluates_to_true.
-/
def evaluates_to_true : bool_expr → Prop 
| e := eval e = tt
/-
This definition brxoke when we added an interpretation,
i, as a second argument to eval.
-/

open bool_expr 

example : evaluates_to_true TT :=
begin
  unfold evaluates_to_true,
  trivial,
end
--ditto last comment

example : evaluates_to_true (TT * FF) :=
begin
  unfold evaluates_to_true,
  simp [eval],
  apply rfl,  -- false
end
--ditto last comment

-- Property of an individual expression
example : evaluates_to_true (TT * TT) :=
begin
  unfold evaluates_to_true,
  simp [eval],
  apply rfl,  -- false
end
--ditto last comment


-- Property of the language as a whole: 
-- evaluation is deterministic.

-- HOMEWORK

/-
What deterministic means is that if you evaluate the same
expression twice (in the same environment) that you'll get
the same answer. A language with a statement that returns 
a truly random number wouldn't have this property. Show that
evaluation is deterministic for our "Bool" language.
-/

def eval_is_deterministic : 
  ∀ (e : bool_expr) (i : bool_var → boo) (b1 b2 : boo), 
  b1 = (eval e i) → 
  b2 = (eval e i) → 
  b1 = b2 := 
begin
  intros e i b1 b2 h1 h2,
  rw h1,
  rw h2,
end


def nat_eq : ℕ → ℕ → bool
| nat.zero nat.zero := bool.tt
| nat.zero _ := bool.ff
| _ nat.zero := bool.ff
| (nat.succ n') (nat.succ m') := nat_eq n' m'

#reduce nat_eq 0 0
#reduce nat_eq 0 1
#reduce nat_eq 1 0
#reduce nat_eq 1 1

def init := var_interp_1

#reduce init X
#reduce init Y
#reduce init Z

def st_1 := override init X ff

#reduce st_1 X
#reduce st_1 Y
#reduce st_1 Z

def st_2 := override (st_1) Z ff

#reduce st_2 X
#reduce st_2 Y
#reduce st_2 Z


end bool_lang