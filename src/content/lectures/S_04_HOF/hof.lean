
/-
Let's look at three functions, each transforming
one list into another by converting each element
in the argument list, through the application of
a function, into a corresponding element in the
resulting list. Try to see the commonalities and
the dimesions of variation. 
-/


-- map each n in argument list to n+1 in result
-- e.g., add_1 [1, 2, 3] = [2, 3, 4]
def add_1 : list nat → list nat
| [] := []
| (h::t) := (h+1)::add_1 t

example : add_1 [] = [] := rfl
example : add_1 [1, 2, 3] = [2, 3, 4] := rfl 


-- map each n in argument list to n+2 in result
-- e.g., add_2 [1, 2, 3] = [3, 4, 5] 
def add_2 : list nat → list nat
| [] := []
| (h::t) := (h+2)::add_2 t

example : add_2 [] = [] := rfl
example : add_2 [1, 2, 3] = [3, 4, 5] := rfl 


-- map each n in argument list to n^2 in result
-- e.g., add_2 [1, 2, 3] = [1, 4, 9] 
def sqr_list : list nat → list nat 
| [] := []
| (h::t) := (h*h)::sqr_list t 

example : sqr_list [1, 2, 3] = [1, 4, 9] := rfl 


/-
One *dimension of variation* is in the function applied
to each element of the given argument list to compute 
the  corresponding element of the result list. We abstract
from these variations, replacing the applications of these
with applications of the function passed as an argument.
The result is a map function that can convert any list of
natural numbers to another list of natural numbers by
applying a given function (of type nat → nat) to each
element in the given list to compute its corresponding 
value in the list to be returned. 
-/
def map_nat : (nat → nat) → list nat → list nat
| fn [] := []
| fn (h::t) := (fn h)::(map_nat fn t) 

example : map_nat (nat.succ) [1, 2, 3] = [2, 3, 4] := rfl
example : map_nat (λ n, n * n) [1, 2, 3] = [1, 4, 9] := rfl


/-
A second, orthogonal, dimension of variation is in the
types of elements in the argument and results lists. In 
the general case, a map function can take in a list of 
values of any type, α, and convert it to a corresponding
list of elements of type β by applying a function of type
α → β to each element of the first list to calculate the
corresponding elements of the second list. 
-/
universe u 
def map {α β : Type u} : (α → β) → list α → list β 
| fn [] := []
| fn (h::t) := (fn h)::(map fn t) 

example: map nat.succ [1, 2, 3] = [2, 3, 4] := rfl


/-
Practice: write an expression to convert a list of nat to 
a list of bool, where each bool is the parity (oddness on
a scale of {0, 1}) of its corresponding value.
-/

-- Answer

example : 
  map (λ n, n%2) [1, 2, 3, 4, 5] = [1, 0, 1, 0, 1] 
:= rfl 
  
 /-
 Practice: write an expression that uses map to convert
 a list of strings to a list of their lengths.
 -/
 
 example :
  map (λ s, string.length s) ["Hello", "Lean"] = [5, 4] 
:= rfl



/-
*******************************************
The foldr, or reduce, higher-order function
*******************************************
-/

/-
As before, we'll start with a few concrete examples
and from them will work to a general definition of 
the folr ("right fold") operation on lists of values.
-/

/-
Example #1 Reduce a list of natural numbers to the sum 
of all its elements.
-/

def sum_of_elts : list nat → nat
| [] := 0
| (h::t) := h + sum_of_elts t

example : sum_of_elts [0, 1, 2, 3, 4, 5] = 15 := rfl

def prod_of_elts : list nat → nat
| [] := 1
| (h::t) := h * sum_of_elts t

-- we can write tests like this
-- but then we have to use our eyes 
#reduce prod_of_elts []     -- expect 1
#reduce prod_of_elts [2]    -- expect 2

-- it's better to let the type checker do the work
example : prod_of_elts [] = 1 := rfl
-- The following tests catch an error I made in class!
example : prod_of_elts [2] = 2 := rfl
example : prod_of_elts [1, 2, 3, 4, 5] = 120 := rfl
-- Practice: find and fix the bug

/-
Clearly the two reduction functions we've looked at, 
sum_of_elts and prod_of_elts vary *dependently* in two
dimensions: (1) the value returned for the base case of
an empty list, (2) the function used to produce a final
answer by combining the head of a non-empty list with
the result of reducing the tail of the list (which we
do recursively).
-/
def reduce_elts : (nat → nat → nat) → nat → list nat → nat
| f id [] := id
| f id (h::t) := f h (reduce_elts f id t)

example : reduce_elts nat.add 0 [1,2,3,4,5] = 15 := rfl
example : reduce_elts nat.mul 1 [1,2,3,4,5] = 120 := rfl


/-
We can also generalize over the type of list elements
and the type of the reduced return result. As an example
of a case where list elements are of one type and the
result of the reduction is of another type, think of a
function, all_even, that takes a list of natural numbers
and returns true if and only if all are even (otherwise
false). The key to understanding our algorithm is to see
it as applying one operation one time, with two cases.
If the list is empty, return a "base case" value for 
this case, otherwise apply a function to two aguments,
the head of the list and the reduction of the tail to
compute the final result. That's it. (The computation 
of the result for the tail is by recursion.) The operation
that combines the head of the list with the answer for
the rest of the list thus takes two arguments, the first
of the input list element type, the second, the answer
for the rest of the list, which will be of the second
type: bool, in our example. 
-/
def reduce {α β : Type u} : (α → β → β) → β → list α → β 
| f id [] := id
| f id (h::t) := f h (reduce f id t)

/-
As an example, use reduce to implement a function
that reduces any list of strings to a single number
that is the sum of their lengths.
-/

/-
First let's write the reduce operator, which will
take the string at the head of a list of strings
along with the reduction of the rest of the list
(computed by recursion) and that will then return
the answer for the whole list: both head and tail.
-/ 

def red_strs : string → nat → nat 
| s n := s.length + n


-- example: sum of lengths of list of strings
example : 
  reduce red_strs 0 ["hello", "lean", "!"] = 10 
:= rfl

-- example: number of odd numbers in a list of nats
example : 
  reduce nat.add 0 (map (λ n, n%2) [1,2,3,4,5]) = 3 
:= rfl

/-
Finally a generalized map/reduce function, taking
a reduction operator, its value for when a list is
empty, an element conversion function, and a list 
of elements, and that (1) maps it by applying the
element conversion function elementwise to produce
a new list, which (2) is then reduced to a final
result.
-/
def map_reduce { α β γ : Type u} : (β → γ → γ) → γ → (α → β) → list α → γ
| red_op id map_fn l := reduce red_op id (map map_fn l)

-- Use reduce to compute number of odd values in a list
#reduce map_reduce nat.add 0 (λ n, n%2) [1,2,3,4,5]

/- 
Use partial evaluation to define a funciton that 
takes any list of natural numbers to the number of
odd values in the list.
-/

def count_odds := map_reduce nat.add 0 (λ n, n%2)
example : count_odds [1,2,3,4,5] = 3 := rfl

/-
The map and reduce functions are function-building
machines. Here we've applied map_reduce to (1) a
reduction operator, (2) it's identity, and (3) an
element mapping function to produce a function that
counts the number of odd values in a list of nats.
map_reduce nat.add 0 (λ n, n%2)
-/


/-
Practice: use map_reduce to convert a list of
interpretations for an expression, e, 
-/

/-
Practice: Identify the places in the SAT solver
code that I/Kevin will provide where special cases
of map or reduce functions are used and replace 
them with uses of the higher-order list map and
reduce functions while maintaining correctness 
of the code.

The versions in the Lean library are called
list.map and list.foldr (for "fold right"). You 
may, and should, use Lean's versions for this
assignment.
-/

#check @list.map
#check @list.foldr

-- Yay!