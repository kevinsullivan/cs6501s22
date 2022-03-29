import .bool_lang

open bool_lang 
open bool_lang.bool_var
open bool_lang.bool_expr


def X := V 0
def Y := V 1
def Z := V 2

def be1 := TT
def be2 := FF
def ve1 := var X
def be3 := conj be1 be2
def be4 := neg be3

def var_interp_1 : bool_var → bool
| v := tt

def var_interp_2 : bool_var → bool
| (V 0) := tt
| (V 1) := ff
| (V 2) := tt
| _ := tt

-- REFACTOR INTO TEST FILE
#reduce eval be4
#reduce eval (conj (disj be2 be4) be3)
#check X
#check (var X)
#reduce eval ((var X) * (var Y)) var_interp_1
#reduce eval ((var X) * (var Y)) var_interp_2
#reduce eval ((be2 + be4) * be3)




