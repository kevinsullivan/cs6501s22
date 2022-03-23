import .expr 
import .interp

-- semantics : assign nat value to any expr given interp

open nat_expr

def eval : nat_expr → nat_var_interp → nat
| (lit n) _ := n
| (var v) i := i v
| (dec e) i := (eval e i) - 1
| (inc e) i := (eval e i) + 1
| (add e1 e2) i := (eval e1 i) + (eval e2 i)
