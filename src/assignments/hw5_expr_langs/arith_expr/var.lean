-- SYNTAX

-- Variables ADT

-- data type
inductive nat_var 
| Δ (n : ℕ)

open nat_var

-- operations
def nat_var_eq : nat_var → nat_var → bool
| (Δ n) (Δ m) :=  n = m   -- coercion here

-- notationss
notation e1 = e2 := nat_var_eq e1 e2
