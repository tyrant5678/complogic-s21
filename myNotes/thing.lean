universe u 

def fold''' {α β : Type u} : β → (α → β) → (β → β → β) → list α → β 
| id p r list.nil := id
| id p r (h::t) := r (p h) (fold''' id p r t)