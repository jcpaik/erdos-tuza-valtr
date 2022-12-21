import tactic.basic

import list

structure configuration (α : Type*) [linear_order α] :=
(is_3cup : α → α → α → Prop)
(decidable_3cup : Π (a b c : α), decidable (is_3cup a b c))

namespace configuration

variables {α : Type*} [linear_order α] (C : configuration α)

local attribute [instance] configuration.decidable_3cup

-- Notion of 3-caps

def is_3cap (a b c : α) : Prop := ¬(C.is_3cup a b c)

def decidable_3cap (a b c : α) : decidable (C.is_3cap a b c) :=
  @not.decidable _ (C.decidable_3cup a b c)

local attribute [instance] configuration.decidable_3cap

-- Notion of caps and cups
@[simp]
def is_cap (l : list α) : Prop :=  l.chain' (<) ∧ l.chain3' C.is_3cap
@[simp]
def is_cup (l : list α) : Prop := l.chain' (<) ∧ l.chain3' C.is_3cup

def cap : Type* := {l : list α // C.is_cap l}
def cup : Type* := {l : list α // C.is_cup l}



end configuration