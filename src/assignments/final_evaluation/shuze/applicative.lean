-- My collaborator of this final project is Derek Johnson.


/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
--import init.control.functor   -- Sullivan: comment out
import .functor                 --Sullivan: import local file
open function
universes u v

namespace hidden

class has_pure (f : Type u → Type v) :=
(pure {α : Type u} : α → f α)

export has_pure (pure)

class has_seq (f : Type u → Type v) : Type (max (u+1) v) :=
(seq  : Π {α β : Type u}, f (α → β) → f α → f β)

infixl ` <*> `:60 := has_seq.seq

class has_seq_left (f : Type u → Type v) : Type (max (u+1) v) :=
(seq_left : Π {α β : Type u}, f α → f β → f α)

infixl ` <* `:60  := has_seq_left.seq_left

class has_seq_right (f : Type u → Type v) : Type (max (u+1) v) :=
(seq_right : Π {α β : Type u}, f α → f β → f β)


infixl ` *> `:60  := has_seq_right.seq_right

#check const nat 1 1
#reduce const nat 1 2
#reduce const nat id 2 3


class applicative (f : Type u → Type v) extends functor f, has_pure f, has_seq f, has_seq_left f, has_seq_right f :=
(map := λ _ _ x y, pure x <*> y)
(seq_left  := λ α β a b, const β <$> a <*> b)
(seq_right := λ α β a b, const α id <$> a <*> b)
(applicative_id : ∀ (T : Type u), seq (pure (@id T)) = @id (f T)  )
(applicative_compo : ∀ (α β γ: Type u) (func_g:  (α → β) )(func_f: (β → γ) ) (w:  α ),  
  pure func_f <*> (pure func_g <*> pure w ) = 
  (pure (@function.comp α β γ))  <*> pure func_f <*> pure func_g <*> pure w )
(applicative_homo : ∀ (α β: Type u) (func_f: α → β) (x:α), 
  (pure func_f) <*> (pure x) = pure (func_f x )  )
(applicative_inter : ∀ (α β: Type u) (y: α) (func_f:  α → β  ),  
  (pure func_f) <*> (pure y) = (pure (λ an_F: (α → β) , an_F y )  ) <*> (pure func_f) )



end hidden

