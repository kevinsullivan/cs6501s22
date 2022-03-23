import .var -- expression ADT

-- data type
inductive nat_expr : Type
| lit (n : nat)
| var (v : nat_var) 
| dec (e : nat_expr) 
| inc (e : nat_expr) 
| add (e1 e2 : nat_expr)

open nat_expr

-- notations
notation `[`n`]` := lit n     -- we overload []
notation `[`v`]` := var v     -- there and here
postfix `++` :=  inc
notation e1 + e2 := add e1 e2

