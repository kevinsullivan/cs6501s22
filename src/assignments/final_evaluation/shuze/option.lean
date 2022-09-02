-- My collaborator of this final project is Derek Johnson.
import .functor
import .applicative
import .monad
open function

universes u v

namespace hidden

/-
infix symbol for local test
-/
local infixr ` <$> `:100 := functor.map
local infixr ` <$ `:100  := functor.map_const
local infixr ` $> `:100  := functor.map_const_rev



/-
Functor const function for option
-/
def option_map_const 
  {α β : Type u} :
  α → option β → option α 
| a option.none := option.none
| a (option.some b) := option.some a

/-
Provide a proof for Functor Identity Law
-/
theorem option_map_law1 : ∀ (T : Type u), option.map (@id T) = (@id (option T)) :=
begin
assume T,
apply funext,
assume optionT,
rw [id],
induction optionT,
simp [option.map_id],
simp [option.map_id],
end

/-
Provide a proof for Functor Composition Law
-/
theorem option_map_law2: 
  ∀ (α β γ: Type u) (f: α → β) (g: β → γ) , 
     option.map (g ∘ f) = option.map g ∘ (option.map f)   :=
begin
intros,
apply funext,
assume optionA,
simp [option.map],
induction optionA,
simp [option.bind],
simp [option.bind],
end

/-
Create an instance of functor option
-/
instance option_mapper : functor option := ⟨ @option.map, @option_map_const, option_map_law1, option_map_law2  ⟩ 


/-
Local test
-/
#reduce nat.succ <$> option.none
#reduce nat.succ <$> option.some 0
#reduce nat.add 3 <$> option.some 2
#reduce id <$>  option.some 3
#reduce id <$>  option.some 4






--APPLICATIVE FUNCTOR

/-
Applicative functions for option
-/
def pure_option {α : Type u} : α → option α 
| a := some a

def seq_option : Π {α β : Type u}, option (α → β) → option α → option β
| α β none _ := none
| α β (some func) oa := functor.map func oa  -- Use's functor's option_map!

def seq_option_left : Π {α β : Type u}, option α → option β → option α
| α β none _ := none
| α β (some func) oa := functor.map_const func oa  

def seq_option_right : Π {α β : Type u}, option α → option β → option  β
| α β _ none  := none
| α β oa (some func)  := functor.map_const_rev oa func  


local infixl ` <*> `:60 := has_seq.seq
local infixl ` <* `:60  := has_seq_left.seq_left
local infixl ` *> `:60  := has_seq_right.seq_right

instance : has_pure option := ⟨ @pure_option ⟩  
instance : has_seq option := ⟨ @seq_option ⟩ 
instance : has_seq_left option := ⟨ @seq_option_left ⟩ 
instance : has_seq_right option := ⟨ @seq_option_right ⟩ 


/-
Provide a proof for Applicative Identity Law
-/
theorem option_applicative_law1 : ∀ (T : Type u), seq_option (pure_option (@id T)) = @id (option T) :=
begin
assume T,
apply funext,
assume optionT,
rw [id],
induction optionT,
-- base
simp [pure_option],
simp [seq_option],
simp [functor.map],
simp [option.map_id],
--
simp [pure_option],
simp [seq_option],
simp [functor.map],
simp [option.map_id],
end

/-
Provide a proof for Applicative Composition Law
-/
theorem option_applicative_law2 :  ∀ (α β γ: Type u) (func_g:  (α → β) )(func_f: (β → γ) ) (w:  α ),  
pure_option func_f <*> (pure_option func_g <*> pure_option w ) = (pure_option (func_f  ∘  func_g)) <*> pure_option w
:=
begin
intros,
simp [pure_option],
simp [has_seq.seq],
simp [seq_option],
simp [functor.map],
simp [function.comp],
simp [option.map],
simp [option.bind],
end

/-
Provide a proof for Applicative Homomorphism Law
-/
theorem option_applicative_law3 : 
∀ (α β: Type u) (func_f: α → β) (x:α), (pure_option func_f)  <*> (pure_option x) 
= pure_option (func_f x ) :=
begin
intros,
apply rfl,
end


/-
Provide a proof for Applicative Interchange Law
-/
theorem option_applicative_law4 : 
∀ (α β: Type u) (y: α) (func_f:  α → β  ),  (pure_option func_f) <*> (pure_option y) 
= (pure_option (λ an_F: (α → β) , an_F y )  ) <*> (pure_option func_f) :=
begin
intros,
simp [pure_option],
simp [has_seq.seq],
simp [seq_option],
simp [functor.map],
simp [option.map],
simp [option.bind],
end

/-
Create an instance of applicative option
-/
instance : applicative option := ⟨ option_applicative_law1, option_applicative_law2, option_applicative_law3, option_applicative_law4 ⟩ 


/-
Local test
-/
#reduce has_pure.pure (nat.mul) <*> some 3 <*> some 4
#reduce has_pure.pure (nat.mul) <*> none <*> some 4
#reduce has_pure.pure (nat.mul) <*> some 3 <*> none

#reduce (has_pure.pure id) <*> (some 1)

#reduce some tt <* none
#reduce some tt <* some 1 
#reduce some tt *> none
#reduce some tt *> some 1 


--Monad



def has_bind_option : Π {α β : Type u}, option α → (α → option β) → option β
| α β none _ := none
| α β (some x) func := func x 

instance : has_bind option :=⟨ @has_bind_option⟩

local infixl ` >>= `:55 := has_bind.bind
local infixl ` >> `:55  := has_bind.and_then

/-
Provide a proof for Monad Left Identity Law
-/
theorem option_monad_law1 : 
∀ (α β: Type u) (func_f:  α → option β ) ( x: α  ), 
    (pure_option x) >>= func_f  = func_f x  :=
begin
intros,
simp [pure_option],
simp [has_bind.bind],
simp [has_bind_option],
end

/-
Provide a proof for Monad Right Identity Law
-/
theorem option_monad_law2 : 
∀ (α β: Type u)  (x: option α ),
    x >>= pure_option = x  :=
begin
intros,
simp [has_bind.bind],
induction x,
-- base
simp [has_bind_option],
-- inductive step
simp [has_bind_option],
simp [pure_option],
end

/-
Provide a proof for Monad Right Associativity Law
-/
theorem option_monad_law3 : 
∀ (α β γ: Type u) (x: option α ) (func_f:  (α → option β) ) (func_g:  (β → option γ) ),
    x >>= func_f >>= func_g  = x  >>= (λ y, func_f y>>= func_g   ):=
begin
intros,
simp [has_bind.bind],
induction x,
-- base
simp [has_bind_option],
-- inductive step
simp [has_bind_option],
end

/-
Create an instance of Monad option
-/
instance : monad option := ⟨ option_monad_law1,  option_monad_law2, option_monad_law3 ⟩ 


/-
Local test
-/
#reduce some 3 >>=  (λ x, has_pure.pure (x+1))
#reduce none >>=  (λ x, has_pure.pure (x+1))
#reduce some 3 >>=  (λ x, none)

#reduce some 3 >>  some 5
#reduce none >>  some 5

end hidden