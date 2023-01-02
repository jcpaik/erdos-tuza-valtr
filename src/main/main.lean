import data.nat.choose
import data.finset

import config
import etv

variables {α : Type*} [linear_order α]
  {C : config α} {S : finset α} (l : C.label S)
  {n : ℕ} (cup_free : ¬C.has_ncup (n+2) S)

theorem main_induction 
  (n : ℕ) {hn : 2 ≤ n} (hS : nat.choose n 2 ≤ S.card)
  (cap_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n+1) S) :
  ∃ p q r s, C.has_interweaved_laced n S p q r s := sorry