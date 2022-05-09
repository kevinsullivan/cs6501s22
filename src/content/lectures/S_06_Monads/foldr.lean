import algebra.group.defs

def foldr {α : Type} [monoid α] : list α → α 
| [] := id
| (h::t) := op x h (foldr t)

#eval foldr [tt,ff,tt]
#eval foldr [tt,tt,tt]
#eval foldr [1,2,3,4,5]
#eval foldr ["Hello", ", ", "Lean", "!"]