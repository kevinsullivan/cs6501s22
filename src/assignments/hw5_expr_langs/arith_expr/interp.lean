import .var

-- type
def nat_var_interp := (nat_var → nat)

-- operations
def override : 
  nat_var_interp → 
  nat_var → 
  nat → 
  nat_var_interp :=
λ i v n,
  λ x, 
    if (nat_var_eq x v) 
    then n 
    else i x
