import Mathlib.Order.Basic
import Mathlib.Order.Synonym

universe u v

open OrderDual

def mirror2 {α : Type u} [LinearOrder α] {β : Sort v} (f : α → α → β) : αᵒᵈ → αᵒᵈ → β := fun a b =>
  f (ofDual b) (ofDual a)

def mirror3 {α : Type u} [LinearOrder α] {β : Sort v} (f : α → α → α → β) : αᵒᵈ → αᵒᵈ → αᵒᵈ → β :=
  fun a b c => f (ofDual c) (ofDual b) (ofDual a)

@[reducible]
def DecidableRel3 {α : Sort u} (r : α → α → α → Prop) :=
  ∀ a b c : α, Decidable (r a b c)

def DecidableRel.mirror2 {α : Type u} [LinearOrder α] {r : α → α → Prop} (dec : DecidableRel r) :
    DecidableRel (mirror2 r) := fun a b => dec (ofDual b) (ofDual a)

def DecidableRel3.mirror3 {α : Type u} [LinearOrder α] {r : α → α → α → Prop}
    (dec : DecidableRel3 r) : DecidableRel3 (mirror3 r) := fun a b c =>
  dec (ofDual c) (ofDual b) (ofDual a)
