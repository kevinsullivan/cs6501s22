import .bool_var
import .bool_interp

namespace bool_lang
open bool_var

#check @decidable.rec
/-
Π {p : Prop} {motive : decidable p → Sort u_1},
    (Π (h : ¬p), motive (is_false h)) → 
    (Π (h : p), motive (is_true h)) → 
    Π (n : decidable p), motive n
-/

/-
For any proposition, p, and any property, motive, of
decidable p, if you have a function that maps any
proof of ¬p to a proof that (is_false h) has motive,
then if you also have a function that takes any
proof of p to a proof of motive (is_true h), then 
you can conclude that any proof of (decidable p)
has the property, motive.
-/

def x : list interp := 
  [
    λ (v : bool_var),
      decidable.rec 
        (λ (hnc : var_eq v (V 0) = tt → false), ff) 
        (λ (hc : var_eq v (V 0) = tt), ff)
        (bool.decidable_eq (var_eq v (V 0)) tt), 
    λ (v : bool_var), ff
  ]

end bool_lang