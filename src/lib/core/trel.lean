universes u u1 u2 u3

def flip3 {α : Sort u1} {β : Sort u2} {φ : Sort u3} {γ : Sort u} 
  (f : α → β → φ → γ) : φ → β → α → γ :=
λ c b a, f a b c

theorem flip3_flip3 {α : Sort u1} {β : Sort u2} {φ : Sort u3} {γ : Sort u} 
  (f : α → β → φ → γ) : flip3 (flip3 f) = f :=
  funext (λ a, funext (λ b, funext(λ c, rfl)))

@[reducible]
def decidable_trel {α : Sort u} (r : α → α → α → Prop) :=
Π (a b c : α), decidable (r a b c)