
def add_1 : list nat → list nat
| [] := []
| (h::t) := (h+1)::add_1 t

def add_2 : list nat → list nat
| [] := []
| (h::t) := (h+2)::add_2 t

def sqr_list : list nat → list nat 
| [] := []
| (h::t) := (h*h)::sqr_list t 

def f : (nat → nat) → list nat → list nat
| fn [] := []
| fn (h::t) := (fn h)::(f fn t) 

universe u 
def map {α β : Type u} : (α → β) → list α → list β 
| fn [] := []
| fn (h::t) := (fn h)::(map fn t) 

-- write expr to reduce list of nat to list of bool computing parity of each elt
-- even -> true 


#reduce map (λ n, n%2) [1, 2, 3, 4, 5]    -- expect is [1,0,1,0,1]
#reduce map (λ s, string.length s) ["Hello", "Lean"]

#reduce f (λ n, n + 1) [1, 2, 3]
#reduce f (λ n, n * n) [1, 2, 3]

#reduce add_1 []
#reduce add_1 [1, 2, 3]
#reduce add_2 [1, 2, 3]
#reduce sqr_list [2,3,4]

/-
Reduce a list of natural numbers to the sum of all the elements
-/

def sum_of_elts : list nat → nat
| [] := 0
| (h::t) := h + sum_of_elts t

#reduce sum_of_elts [0, 1, 2, 3, 4, 5]

def prod_of_elts : list nat → nat
| [] := 1
| (h::t) := h * sum_of_elts t

def reduce_elts : (nat → nat → nat) → nat → list nat → nat
| f id [] := id
| f id (h::t) := f h (reduce_elts f id t)

#reduce reduce_elts nat.add 0 [1,2,3,4,5]
#reduce reduce_elts nat.mul 1 [1,2,3,4,5]

def reduce {α β : Type u} : (α → β → β) → β → list α → β 
| f id [] := id
| f id (h::t) := f h (reduce f id t)


def red_strs : string → nat → nat 
| s n := s.length + n

#reduce reduce red_strs 0 ["hello", "lean", "!"]

#reduce reduce nat.add 0 (map (λ n, n%2) [1,2,3,4,5])


def map_reduce { α β γ : Type u} : (β → γ → γ) → γ → (α → β) → list α → γ
| red_op id map_fn l := reduce red_op id (map map_fn l)

#reduce map_reduce nat.add 0 (λ n, n%2) [1,2,3,4,5]