import data.list
import data.finset

import lib.list
import lib.core.decidable

structure config (α : Type*) [linear_order α] :=
(cup3 : α → α → α → Prop)
(decidable_cup3 : decidable_trel cup3)

namespace config

variables {α : Type*} [linear_order α] (C : config α)

attribute [instance] config.decidable_cup3

-- Notion of 3-caps

def cap3 (a b c : α) : Prop := ¬(C.cup3 a b c)

def decidable_cap3 : decidable_trel C.cap3 :=
  λ a b c, @not.decidable _ (C.decidable_cup3 a b c)

attribute [instance] config.decidable_cap3

-- Notion of caps and cups

def cap (l : list α) : Prop := 
  l.chain' (<) ∧ l.chain3' C.cap3
def cup (l : list α) : Prop := 
  l.chain' (<) ∧ l.chain3' C.cup3
def gon (l1 l2 : list α) : Prop :=
  2 ≤ l1.length ∧ C.cap l1 ∧
  2 ≤ l2.length ∧ C.cup l2 ∧
  l1.head' = l2.head' ∧ l1.last' = l2.last'

@[simp] def ncap (n : ℕ) (l : list α) : Prop := 
  C.cap l ∧ l.length = n
@[simp] def ncup (n : ℕ) (l : list α) : Prop := 
  C.cup l ∧ l.length = n
@[simp] def ngon (n : ℕ) (l1 l2 : list α) : Prop :=
  C.gon l1 l2 ∧ l1.length + l2.length = n + 2

def has_ncap (n : ℕ) (S : finset α) : Prop :=
  ∃ (l : list α), C.ncap n l ∧ l.in S
def has_ncup (n : ℕ) (S : finset α) : Prop :=
  ∃ (l : list α), C.ncup n l ∧ l.in S
def has_ngon (n : ℕ) (S : finset α) : Prop :=
  ∃ (l1 l2 : list α), C.ngon n l1 l2 ∧ l1.in S ∧ l2.in S

end config