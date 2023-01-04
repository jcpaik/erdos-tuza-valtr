import data.nat.choose
import data.finset

import config
import etv

variables {α : Type*} [linear_order α]
  {C : config α} {S : finset α}

theorem main_induction 
  (n : ℕ) (hS : nat.choose (n+2) 2 + 2 ≤ S.card)
  (cap_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n+2) S) :
  ∃ p q r s, C.has_interweaved_laced (n+1) S p q r s := sorry