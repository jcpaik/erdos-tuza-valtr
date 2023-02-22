import order

universes u v

open order_dual

def mirror2 {α : Type u} [linear_order α] {β : Sort v}  
  (f : α → α → β) : αᵒᵈ → αᵒᵈ → β :=
λ a b, f (of_dual b) (of_dual a)

def mirror3 {α : Type u} [linear_order α] {β : Sort v}  
  (f : α → α → α → β) : αᵒᵈ → αᵒᵈ → αᵒᵈ → β :=
λ a b c, f (of_dual c) (of_dual b) (of_dual a)

@[reducible]
def decidable_rel3 {α : Sort u} (r : α → α → α → Prop) :=
Π (a b c : α), decidable (r a b c)

def decidable_rel.mirror2
  {α : Type u} [linear_order α] {r : α → α → Prop} 
  (dec : decidable_rel r) : decidable_rel (mirror2 r) :=
λ a b, dec (of_dual b) (of_dual a)

def decidable_rel3.mirror3
  {α : Type u} [linear_order α] {r : α → α → α → Prop} 
  (dec : decidable_rel3 r) : decidable_rel3 (mirror3 r) :=
λ a b c, dec (of_dual c) (of_dual b) (of_dual a)