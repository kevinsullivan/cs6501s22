namespace hidden

universes u v

/-
We've seen a function for mapping a (different) function over a list.
-/

def list_map {α : Type u} {β : Type v} : (α → β) → list α → list β
| f []      := []
| f (h::t)  := (f h)::(list_map f t) 

/-
But we can imagine analogous functions over any kind of structure that
contains objects of some arbitrary other type. For example, here is a
function for mapping a function, f, over an object of type (option α),
for any type α. 
-/

def option_map {α : Type u} {β : Type v} : (α → β) → option α → option β
| f none      := none
| f (some a)  := some (f a) 

/-
As a third example, suppose we have a binary tree type with nodes that
contain values of any type, α.
-/

inductive tree (α : Type u)
| empty : tree
| node (a : α) (left right : tree) : tree

/-
Now we can write a function for mapping trees of α values to trees
of β values in an analogous manner.
-/

def tree_map {α : Type u} {β : Type v} : (α → β) → (tree α) → (tree β)
| f tree.empty := tree.empty
| f (tree.node a l r) := tree.node (f a) (tree_map f l) (tree_map f r)


/-
The implementations of these functions differ significantly; but look
at their types:

def list_map    {α : Type u} {β : Type v} : (α → β) →   (list α)    → (list β)
def option_map  {α : Type u} {β : Type v} : (α → β) →   (option α)  → (option β)
def tree_map    {α : Type u} {β : Type v} : (α → β) →   (tree α)     → (tree β)

These types are identical but in one dimension:          ^^^^^          ^^^^^

As usual, we can try to abstract to a new parameter. 



But what is its type?
Well, question: What is the type of list? Of option? Of tree? 
Answer: Each is Type u → Type u
We can't just add a parameter, m : Type u → Type u: the *implementations* differ
We have a common abstraction but with different implementations for different types

Ad hoc polymorphism, aka, overloading, aka generics, to the rescue! The new
pattern that we see here is that the parameter of the typeclass is no longer
a concrete type (such as bool or nat), but a polymorphic type builder, i.e.,
a value such as list α, option α, or tree α (each of type, Type → Type)
-/

class functor (m : Type u → Type v) : Type (max (u+1) v) :=
(map : ∀ {α β : Type u}, (α → β) → m α → m β)

/-
As a shorthand notaton, we enable the developer to write
f<$>l as an expression that reduces to f mapped over l.
-/
local infixr ` <$> `:100 := functor.map

/-
Finally, we instantiate the typeclass once for each "type builder,"
such as list, option, or tree, over which we want to be able to map
functions using this notation. 
-/

instance list_mapper : functor list := ⟨ @list_map ⟩ 
instance option_mapper : functor option := ⟨ @option_map ⟩ 
instance tree_mapper : functor tree := ⟨ @tree_map ⟩

/-
We now have an overloaded map operator (in Haskell it's called fmap)
that can be used to map functions over lists, options, and trees. We
can now view lists, options, and trees as "functors" in the functional
programming (rather than category theory) sense of the term: that is,
as structured containers for objects of some source type that can be
"mapped" to corresponding structured containers for objects of some
destination type.
-/

#reduce nat.succ <$> [] 
#reduce nat.succ <$> [1,2,3]

#reduce nat.succ <$> option.none
#reduce nat.succ <$> option.some 0

def aTree :=
  tree.node 0 
  (tree.node 1 tree.empty tree.empty) 
  (tree.node 2 tree.empty tree.empty)

#reduce nat.succ <$> (tree.empty)
#reduce nat.succ <$> aTree


#check @functor
/-
What we've done is to make list, option, and tree
into "members of the functor typeclass," thereby
overloading the operator that the typeclass defines
for each of these otherwise unrelated types.
-/

end hidden

/-
Now let's have a quick look at Lean's functor typeclass.
It's just like ours but it adds a second function that is
to be overloaded for each type (such as list or option) 
in the functor typeclass. 
-/

#check @functor
#print functor
/-
class functor (f : Type u → Type v) : Type (max (u+1) v) :=
(map : Π {α β : Type u}, (α → β) → f α → f β)
(map_const : Π {α β : Type u}, α → f β → f α := λ α β, map ∘ const β)

The const function (polymorphic in α and β) takes a value, a, of type
α, and yields a function that takes any value of type β and returns a.

The function, map ∘ const β, thus takes any value, a, of type α, and
returns a function that converts a list of β values into a list of a
values (not just α values, but constant a values).

def const (β : Sort u₂) (a : α) : β → α := λ x, a
-/


#check @list.map

instance : functor list := ⟨ @list.map, _ ⟩

universes u v 
def list_map_const 
  {α β : Type u} :
    α → list β → list α 
| a [] := []
| a (h::t) := a::list_map_const a t

-- E.g., replace each natural number in list with tt
#eval list_map_const tt [1,2,3]

instance list_functor : functor list := ⟨ @list.map, @list_map_const ⟩

#check @option.map

def option_map_const 
  {α β : Type u} :
  α → option β → option α 
| a option.none := option.none
| a (option.some b) := option.some a

instance : functor option := ⟨ @option.map, @option_map_const ⟩ 


#reduce nat.succ <$> [1,2,3]
#reduce ff <$ [1,2,3]
#reduce [1,2,3] $> ff