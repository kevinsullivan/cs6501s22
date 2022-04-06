import .bool_expr
import .bool_var
import .bool_semantics
import .set_T

namespace bool_lang
open bool_lang.bool_expr
open bool_lang.bool_var

-- Workspace for top-down development

def reduce_or : list bool → bool
| list.nil := ff
| (h::t) := bor h (reduce_or t)

def get_interp_values : bool_expr → list interp → list bool
| _ list.nil := []
| e (h::t) := ((eval e) h) :: get_interp_values e t

/- 
The function, interps_of_vars, below, returns list of 
the first 2^n interpretations for a set of vars of size
n. The implementation of this function assumes that the
n variables have indices from 0 to n-1. This constraint
could be relaxed by use of Lean's finset type. 
-/

def right_bit (n : nat) := n % 2

def nth_interp : nat → interp
| 0 := λ v, ff
| (n' + 1) := 
  override 
    (nth_interp n') 
    (V n')
    (if (right_bit n') = 0 then ff else tt)

def interps_of_vars_helper : nat → list interp
| 0 := [λ v, ff]
| (n' + 1) := (nth_interp (n'+1))::(interps_of_vars_helper n')

def pow : nat → nat → nat
| n 0 := 1
| n (m'+1) := n * (pow n m')

def interps_of_vars (vs : cset bool_var) : list interp :=
  let s := size vs in (interps_of_vars_helper ((pow 2 s)-1))

-- Jack: returns list of interpretations for set of variables
def interps_of_vars' : cset bool_var → list interp
| list.nil := [λ v, ff]
| (h::t) := 
  let l := interps_of_vars' t in
    list.append 
      l 
      (list.map (λ i, override i h tt) l)

-- Returns set of all distinct variables in a given expr, e
def get_var_set : bool_expr → cset bool_var
| TT := []
| FF := []
| (var v) := [v]
| (conj e1 e2) := union var_eq (get_var_set e1) (get_var_set e2)
| (disj e1 e2) := union var_eq (get_var_set e1) (get_var_set e2)
| (not e) := get_var_set e

def is_satisfiable : bool_expr → bool
| e := reduce_or 
  (
    get_interp_values 
      e 
      (
        interps_of_vars 
          (
            get_var_set 
              e
          )
      )
  )

/-
Specification, existential quantification
-/
def satisfiable (e : bool_expr) : Prop :=
  ∃ (i : interp), eval e i = tt

/-
Specification, computational case analysis
-/
def satisfiable' (e : bool_expr) : Prop :=
  is_satisfiable e = tt

end bool_lang
