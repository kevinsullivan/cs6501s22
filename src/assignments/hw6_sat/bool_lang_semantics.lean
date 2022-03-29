import .bool_lang

namespace bool_lang

open bool_expr
-- OPERATIONS
def eval : bool_expr → (bool_var → bool) → bool
| TT _ := tt
| FF _ := ff
| (var v) i := i v
| (conj e1 e2) i := and (eval e1 i) (eval e2 i)
| (disj e1 e2) i := or (eval e1 i) (eval e2 i)
| (neg e) i := not (eval e i)

open bool_var

def var_eq : bool_var → bool_var → bool
| (V n1) (V n2) := n1 = n2  -- coercion here

def override : (bool_var → bool) → bool_var → bool → (bool_var → bool) :=
λ i v' b, 
  λ v, if (var_eq v v') then b else (i v)



end bool_lang