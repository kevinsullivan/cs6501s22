-- My collaborator of this final project is Derek Johnson.


import .functor
import .applicative
import .monad
universes u v


namespace hidden

/-
Functor const function for list
-/
def list_map_const 
  {α β : Type u} :
    α → list β → list α 
| a [] := []
| a (h::t) := a::list_map_const a t



/-
Provide a proof for Functor Identity Law
-/
theorem list_map_law1 : ∀ (T : Type u), list.map (@id T) = (@id (list T)) :=
begin
assume T,
apply funext,
assume listT,
rw id,
induction listT with e b h,
simp [list.map],
simp [list.map],
end

/-
Provide a proof for Functor Composition Law
-/
theorem list_map_law2: 
  ∀ (α β γ: Type u) (f: α → β) (g: β → γ) , 
     list.map (g ∘ f) = list.map g ∘ (list.map f)   :=
begin
intros,
apply funext,
assume ListA,
simp [list.map],
end

/-
Create an instance of functor list
-/
instance: functor list := ⟨ @list.map,  @list_map_const , list_map_law1, list_map_law2  ⟩ 

/-
Local test
-/
local infixr ` <$> `:100 := functor.map
local infixr ` <$ `:100  := functor.map_const
local infixr ` $> `:100  := functor.map_const_rev

#reduce nat.succ <$> [] 
#reduce nat.succ <$> [1,2,3]
#reduce nat.add 4 <$> [4,5,6]
#reduce nat.add <$> [4,5,6]
#reduce id <$> [1,2,3]
#reduce string.length <$> ["Hello", "Lean!!!"] 


#reduce nat.add <$> [1,2,3]

#reduce tt <$ [1,2,3]
#reduce 2 <$ [tt,ff,tt]
#reduce [1] <$ [tt,ff,tt]
#reduce [1,2,3] $> ff
#reduce [1,2,3] $> tt




--APPLICATIVE FUNCTOR

/-
Applicative functions for list
-/
def pure_list {α : Type u} : α → list α 
| a := [a]

def seq_list : Π {α β : Type u}, list (α → β) → list α → list β
| α β list.nil _ := list.nil
| α β (hf::tf) l := list.append (functor.map hf l) (seq_list tf l)


def seq_list_left : Π {α β : Type u}, list α → list β → list α
| α β list.nil _ := list.nil
| α β (hf::tf) l := list.append (functor.map_const hf l  ) (seq_list_left tf l)

def seq_list_right : Π {α β : Type u}, list α → list β → list  β
| α β _ list.nil  := list.nil
| α β l (hf::tf)  := list.append (functor.map_const_rev l hf ) (seq_list_right l tf )


local infixl ` <*> `:60 := has_seq.seq
local infixl ` <* `:60  := has_seq_left.seq_left
local infixl ` *> `:60  := has_seq_right.seq_right

instance : has_pure list := ⟨ @pure_list ⟩  
instance : has_seq list := ⟨ @seq_list ⟩ 
instance : has_seq_left list := ⟨ @seq_list_left ⟩ 
instance : has_seq_right list := ⟨ @seq_list_right ⟩ 


/-
Provide a proof for Applicative Identity Law
-/
theorem list_applicative_law1 : ∀ (T : Type u), seq_list (pure_list (@id T)) = @id (list T) :=
begin
assume T,
apply funext,
assume listT,
rw [id],
induction listT with a b c,
-- Base
simp [pure_list],
simp [seq_list],
simp [functor.map],
-- Induction Step
simp [pure_list],
simp [seq_list],
simp [functor.map],
apply list.append_nil,
end

/-
Provide a proof for Applicative Composition Law
-/
theorem list_applicative_law2 :  ∀ (α β γ: Type u) (func_g:  (α → β) )(func_f: (β → γ) ) (w:  α ),  
pure_list func_f <*> (pure_list func_g <*> pure_list w ) 
= (pure_list (@function.comp α β γ))  <*> pure_list func_f   <*> pure_list func_g <*> pure_list w
:=
begin
intros,
simp [pure_list],
simp [has_seq.seq],
simp [seq_list],
simp [functor.map],
simp [seq_list],
simp [functor.map],
simp [seq_list],
simp [functor.map],
end

/-
Provide a proof for Applicative Homomorphism Law
-/
theorem list_applicative_law3 : ∀ (α β: Type u) (func_f: α → β) (x:α), 
(pure_list func_f) <*> (pure_list x) = pure_list (func_f x )  :=
begin
intros,
simp [pure_list],
simp [has_seq.seq],
simp [seq_list],
simp [functor.map],
end

/-
Provide a proof for Applicative Interchange Law
-/
theorem list_applicative_law4 :  ∀ (α β: Type u) (y: α) (func_f:  α → β  ),  
(pure_list func_f) <*> (pure_list y) = (pure_list (λ an_F: (α → β) , an_F y )  ) <*> (pure_list func_f) :=
begin
intros,
simp [pure_list],
simp [has_seq.seq],
simp [seq_list],
simp [functor.map],
end


/-
Create an instance of applicative list
-/
instance : applicative list := ⟨ list_applicative_law1, list_applicative_law2, list_applicative_law3, list_applicative_law4 ⟩ 

/-
Local test
-/
#reduce has_pure.pure (nat.add) <*> [1,3] <*> [5,6,7]
#reduce has_pure.pure (nat.add) <*> [1,2,3] <*> [0,1,2]
#reduce has_pure.pure (nat.mul) <*> [2] <*> [0,1,2]
#reduce has_pure.pure (nat.succ) <*> [2,3] 

#reduce has_pure.pure (nat.add) <*> [] <*> [0,1,2]
#reduce has_pure.pure (nat.add) <*> [1,2,3]  <*> []



--Monad



def has_bind_list : Π {α β : Type u}, list α → (α → list β) → list β
| α β list.nil _ := list.nil
| α β (hf::tf) func := list.append (func hf) (has_bind_list tf func)

instance : has_bind list := ⟨@has_bind_list⟩

local infixl ` >>= `:55 := has_bind.bind
local infixl ` >> `:55  := has_bind.and_then


/-
Provide a proof for Monad Left Identity Law
-/
theorem list_monad_law1 : 
∀ (α β: Type u) (func_f:  α → list β ) ( x: α  ), 
     (pure_list x) >>= func_f  = func_f x  :=
begin
intros,
simp [pure_list],
simp [has_bind.bind],
simp [has_bind_list], 
apply list.append_nil,
end

/-
Provide a proof for Monad Right Identity Law
-/
theorem list_monad_law2 : 
∀ (α β: Type u)  (x: list α ),
    x >>= pure_list = x  :=
begin
intros,
simp [has_bind.bind],
induction x with a b c,
-- Base
simp [has_bind_list], 
-- Induction Step
simp [has_bind_list], 
simp [pure_list],
exact c,
end


/-
Provide a proof for Monad Associativity Law
-/

/-
This one is more complex because I need to show a commutative law of Monad list. 
That is "list_monad_commutative2"
(a>>=f) + (b>>=f) = (a+b) >> f
To show this, I first show a micro version  "list_monad_commutative1" which is 
f a +  (b>>=f) = (a::b) >> f
Also, I used list associativity which is 
(a+b)+c = a+(b+c)
-/

-- Step1: (a+b)+c = a+(b+c)
lemma lemma_append_assoc: 
 ∀ {β: Type u} (a b c:  list β ) ,
   (a.append(b)).append(c) = a.append(b.append(c))  :=
begin
intros,
apply list.append_assoc,
end

-- Step2: f a +  (b>>=f) = (a::b) >> f
lemma list_monad_commutative1: 
 ∀ {α β: Type u} (a:  α ) (b: list α) (f:  (α → list β) ),
    has_bind_list (a :: b) f = (f a).append(has_bind_list b f) :=
begin
intros,
induction b with x y z,
-- Base
simp [has_bind_list], 
-- Induction Step
simp [has_bind_list], 
end

-- Step3: (a>>=f) + (b>>=f) = (a+b) >> f
lemma list_monad_commutative2: 
 ∀ {α β: Type u} (a:  list α ) (b: list α) (f:  (α → list β) ),
   (has_bind_list a f).append(has_bind_list b f) = has_bind_list (a.append(b))  f  :=
begin
intros,
induction a with x y z,
-- Base
simp [has_bind.bind],
simp [has_bind_list], 
-- Induction Step
rw list_monad_commutative1,
simp [has_bind.bind],
simp [has_bind_list], 
rw lemma_append_assoc (f x) (has_bind_list y f) (has_bind_list b f),
rw z,
end


-- Final Step: Monad Associativity Law
theorem list_monad_law3 : 
 ∀ (α β γ: Type u) (x: list α ) (f:  (α → list β) ) (g:  (β → list γ) ),
    x >>= f >>= g  = x  >>= (λ y, f y>>= g) :=
begin
intros,
simp [has_bind.bind],
induction x with a b c,
-- Base
simp [has_bind_list], 
-- Induction Step
simp [has_bind_list], 
rw <- c,
rw <- list_monad_commutative2 (f a) (has_bind_list b f) g,
end


/-
Create an instance of Monad option
-/
instance : monad list := ⟨ list_monad_law1, list_monad_law2, list_monad_law3 ⟩ 

#reduce [1,2,3] >>=  (λ x, has_pure.pure (x+1))
#reduce [] >>=  (λ x, has_pure.pure (x+1))
#reduce ["AAA","BB","CCCC"] >>=  (λ x, has_pure.pure (string.length x))
#reduce ["AAA"] >>=  (λ x,  has_pure.pure (string.length x))


end hidden