-- My collaborator of this final project is Derek Johnson.

import .option .list

namespace hidden

/-
You can write test cases in this file.
-/

universes u v

def mul_two (a: ℕ ) :ℕ := a*2

--
def poly_map
  {α β : Type u} 
  {t : Type u → Type u}   -- list, option
  [m : functor t]         -- functor list, functor option
  (f : α → β)
  (i : t α) :
  t β
:= functor.map f i

local infixl ` <$> `:55 := poly_map

/-
Exception propagation functor
-/
#reduce poly_map nat.succ none
#reduce poly_map nat.succ (some 0)
#reduce poly_map mul_two (some 0)
#reduce poly_map mul_two (some 2)

#reduce mul_two <$> none
#reduce mul_two <$> (some 1)
#reduce mul_two <$> (some 2)

/-
Non-deterministic (multi-valued) argument functor
-/
#reduce poly_map nat.succ []
#reduce poly_map nat.succ [1,2,3]
#reduce poly_map mul_two [1,2,3]
#reduce poly_map (λ x, ((string.length x) + 1) ) ["AAA","BB","CCCC"]

#reduce mul_two <$> []
#reduce mul_two <$> [1,2,3]
#reduce nat.succ <$> [1,2,3]
#reduce (λ x, ((string.length x) * 10) ) <$>  ["AAA","BB","CCCC"]

--
def poly_seq
  {α β : Type u} 
  {t : Type u → Type u}   -- list, option
  [m : applicative t]     -- applicative functor list, applicative functor option
  (f : t (α → β))
  (i : t α) :
  t β
:= has_seq.seq f i

local infixl `  <*>  `:55 := poly_seq

/-
Exception propagation applicative functor
-/
#reduce poly_seq (has_pure.pure nat.succ) (some 1)
#reduce poly_seq (has_pure.pure mul_two) (some 1)

#reduce (has_pure.pure nat.succ) <*> (some 1)
#reduce (has_pure.pure mul_two) <*> (some 3)
#reduce (has_pure.pure nat.add) <*>  (some 1) <*> (some 3)
#reduce (has_pure.pure nat.mul) <*>  (some 0) <*> (some 10)


/-
Non-deterministic (multi-valued) argument functor
-/
#reduce poly_seq (has_pure.pure nat.succ) [1,2,3]
#reduce poly_seq (has_pure.pure mul_two) [1,2,3]
#reduce poly_seq ( has_pure.pure string.length)  ["AAA","BB","CCCC"] 
#reduce poly_seq ( has_pure.pure (λ x, (string.length x) + 1))  ["AAA","BB","CCCC"] 


#reduce (has_pure.pure nat.succ) <*> [4,5,6]
#reduce (has_pure.pure mul_two) <*> [4,5,6]
#reduce (has_pure.pure nat.add) <*> [1,0,1] <*> [4,5]
#reduce (has_pure.pure nat.add) <*> [1,2,3] <*> [4,5,6]



def poly_bind
  {α β : Type u} 
  {t : Type u → Type u}   -- list, option
  [m : monad t]         -- Monad list, Monad option
  (i : t α) 
  (f : α → t β):  
  t β
:= has_bind.bind i f

def add_three_option (a: ℕ ): option ℕ  := pure_option (a+3)
def add_three_list (a: ℕ ): list ℕ  := [a+3]
def mul_three_list (a: ℕ ): list ℕ  := [a*3]

local infixl ` >>= `:55 := poly_bind

/-
Exception propagation Monad
-/
#reduce poly_bind (some 1) add_three_option 
#reduce poly_bind (some 5) add_three_option 
#reduce poly_bind none add_three_option 

#reduce (some 3) >>= add_three_option 
#reduce (some 0) >>= add_three_option 
#reduce none >>= add_three_option 

/-
Non-deterministic (multi-valued) Monad
-/
#reduce poly_bind [1,2,3] add_three_list
#reduce poly_bind [10,15,20] add_three_list
#reduce poly_bind [10,15,20] mul_three_list
#reduce poly_bind [] mul_three_list
#reduce poly_bind ["AAA","BB","CCCC"] (λ x, has_pure.pure (string.length x)) 
#reduce poly_bind ["1","22","333"] (λ x, has_pure.pure ((string.length x)*2) ) 


#reduce [1,2,3] >>= add_three_list
#reduce [10,15,20] >>= add_three_list
#reduce [10,15,20] >>= mul_three_list
#reduce []  >>= mul_three_list
#reduce ["1","22","333"] >>= (λ x, has_pure.pure ((string.length x)*2) ) 

end hidden