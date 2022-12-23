-- Decidability of ternary relation

universe u

@[reducible]
def decidable_trel {α : Sort u} (r : α → α → α → Prop) :=
Π (a b c : α), decidable (r a b c)