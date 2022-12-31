import data.list
import data.finset

import lib.list
import lib.core.trel

structure config (α : Type*) [linear_order α] :=
(cup3 : α → α → α → Prop)
(decidable_cup3 : decidable_trel cup3)

namespace config

variables {α : Type*} [ord : linear_order α] (C : config α)

attribute [instance] config.decidable_cup3

-- Notion of 3-caps

def cap3 (a b c : α) : Prop := ¬(C.cup3 a b c)

def decidable_cap3 : decidable_trel C.cap3 :=
  λ a b c, @not.decidable _ (C.decidable_cup3 a b c)

attribute [instance] config.decidable_cap3

-- Notion of caps and cups

def cap (l : list α) : Prop := 
  l.chain' ord.lt ∧ l.chain3' C.cap3
def cup (l : list α) : Prop := 
  l.chain' ord.lt ∧ l.chain3' C.cup3
@[simp] def gon (l1 l2 : list α) : Prop :=
  2 ≤ l1.length ∧ C.cap l1 ∧
  2 ≤ l2.length ∧ C.cup l2 ∧
  l1.head' = l2.head' ∧ l1.last' = l2.last'

instance decidable_cap {l : list α} : decidable (C.cap l) :=
  by rw cap; apply_instance
instance decidable_cup {l : list α} : decidable (C.cup l) :=
  by rw cup; apply_instance
instance decidable_gon {l1 l2 : list α} : decidable (C.gon l1 l2) :=
  by rw gon; apply_instance

def ncap (n : ℕ) (l : list α) : Prop := 
  C.cap l ∧ l.length = n
def ncup (n : ℕ) (l : list α) : Prop := 
  C.cup l ∧ l.length = n
def ngon (n : ℕ) (l1 l2 : list α) : Prop :=
  C.gon l1 l2 ∧ l1.length + l2.length = n + 2

instance decidable_ncap {n : ℕ} {l : list α} : 
  decidable (C.ncap n l) :=
  by rw ncap; apply_instance
instance decidable_ncup {n : ℕ} {l : list α} : 
  decidable (C.ncup n l) :=
  by rw ncup; apply_instance
instance decidable_ngon {n : ℕ} {l1 l2 : list α} : 
  decidable (C.ngon n l1 l2) :=
  by rw ngon; apply_instance

def has_ncap (n : ℕ) (S : finset α) : Prop :=
  ∃ (l : list α) (l_in_S : l.in S), C.ncap n l
def has_ncup (n : ℕ) (S : finset α) : Prop :=
  ∃ (l : list α) (l_in_S : l.in S), C.ncup n l
def has_ngon (n : ℕ) (S : finset α) : Prop :=
  ∃ (l1 : list α) (l1_in_S : l1.in S), 
  ∃ (l2 : list α) (l2_in_S : l2.in S), C.ngon n l1 l2

end config