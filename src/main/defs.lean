import data.nat.choose
import data.finset

import config
import etv

open_locale classical
noncomputable theory

variables {α : Type*} [linear_order α] (C : config α)

def config.main_goal (n : ℕ) : Prop :=
  ∀ (S : finset α),
  nat.choose (n+2) 2 + 2 ≤ S.card →
  ¬C.has_ncap 4 S → ¬C.has_ncup (n+3) S → 
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s

def config.main_goal_wlog (n : ℕ) : Prop :=
  ∀ (S : finset α),
  ¬C.has_join (n+2) (n+1) S →
  nat.choose (n+2) 2 + 2 ≤ S.card →
  ¬C.has_ncap 4 S → ¬C.has_ncup (n+3) S → 
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s