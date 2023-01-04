import data.nat.choose
import data.finset

import config
import etv

variables {α : Type*} [linear_order α] (C : config α)

/-
def config.main_goal (n : ℕ) (S : finset α) : Prop :=
  nat.choose (n+2) 2 + 2 ≤ S.card →
  ¬C.has_ncap 4 S → ¬C.has_ncup (n+3) S → 
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s

def config.has_join_n3_n2 (n : ℕ) (S : finset α) : Prop :=
  ∃ (p : α) (cl cr : list α), 
    C.ncup (n+2) cl ∧ cl.in S ∧ C.ncup (n+2) cr ∧ cr.in S ∧
    p ∈ cl.last' ∧ p ∈ cr.last'

theorem config.main_goal_reduct {n : ℕ} 
  (h : ∀ S, ¬C.has_join_n3_n2 n S → C.main_goal n S) :
  ∀ S, C.main_goal n S

theorem main_lemma
  (n : ℕ) (hS : nat.choose (n+2) 2 + 2 ≤ S.card)
  (cap_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n+3) S) :
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s := sorry
-/