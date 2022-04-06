import .bool_sat_dev

namespace bool_lang
open bool_lang.bool_var

/-
Write a few test cases here, expressed as little
theorems to be proved. 
-/

def X := (bool_var.V 0)
def Y := (bool_var.V 1)
def Z := (bool_var.V 2)

open bool_expr

def e1 := bool_expr.TT
def e1' := bool_expr.FF
def e2 := bool_expr.var X
def e3 := bool_expr.var Y
def e4 := bool_expr.conj e2 e3

#reduce get_var_set e1
#reduce size (get_var_set e1)
#reduce interps_of_vars (get_var_set e1)

#reduce interps_of_vars_helper 0
#reduce interps_of_vars_helper 1


#reduce size (interps_of_vars (get_var_set e1))
#eval is_satisfiable e1
#eval is_satisfiable e1'

#reduce get_var_set e2
#reduce size (get_var_set e2)
#reduce interps_of_vars (get_var_set e2)
#reduce get_interp_values e2 (interps_of_vars (get_var_set e2))
#eval is_satisfiable e2


#reduce get_var_set e4
#reduce interps_of_vars (get_var_set e4)
#eval is_satisfiable e4


end bool_lang