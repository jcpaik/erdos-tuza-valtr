import data.nat.choose
import data.finset

import config
import etv

import main.lemmas

open_locale classical
noncomputable theory

variables {α : Type*} [linear_order α] (C : config α)

def config.main_goal (n : ℕ) : Prop :=
  ∀ (S : finset α),
  nat.choose (n+2) 2 + 2 ≤ S.card →
  ¬C.has_ncap 4 S → ¬C.has_ncup (n+3) S → 
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s

theorem config.mirror_main_goal (n : ℕ) :
  C.main_goal n → C.mirror.main_goal n :=
begin
  sorry
end

def config.main_goal_wlog (n : ℕ) : Prop :=
  ∀ (S : finset α),
  ¬C.has_join (n+2) (n+1) S →
  nat.choose (n+2) 2 + 2 ≤ S.card →
  ¬C.has_ncap 4 S → ¬C.has_ncup (n+3) S → 
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s

theorem config.main_induction_wlog (n : ℕ) :
  C.main_goal n → C.main_goal_wlog (n+1) :=
begin
  intros ih S no_join hS cap4_free cup_free,
  sorry,
end

theorem config.main_induction (n : ℕ) :
  C.main_goal n → C.main_goal (n+1) :=
begin
  intros ih S hS cap4_free cup_free,
  by_cases join_n3_n2 : C.has_join (n+3) (n+2) S, swap,
  { apply C.main_induction_wlog; assumption, },
  by_cases join_n2_n3 : C.has_join (n+2) (n+3) S, swap,
  { rw ←finset.mirror_card at hS,
    rw ←mirror.has_join at join_n2_n3,
    rw ←mirror.has_ncap at cap4_free,
    rw ←mirror.has_ncup at cup_free,
    have mirrored_goal := C.mirror.main_induction_wlog n 
      (C.mirror_main_goal n ih)
      S.mirror join_n2_n3 hS cap4_free cup_free,
    rcases mirrored_goal with ⟨sm, rm, qm, pm, mgoal⟩,
    have eq_p := pm.to_dual_of_dual, set p := pm.of_dual,
    have eq_q := qm.to_dual_of_dual, set q := qm.of_dual,
    have eq_r := rm.to_dual_of_dual, set r := rm.of_dual,
    have eq_s := sm.to_dual_of_dual, set s := sm.of_dual,
    existsi [p, q, r, s],
    rw [←eq_p, ←eq_q, ←eq_r, ←eq_s, mirror.has_interweaved_laced] at mgoal,
    assumption, },
  apply C.join_n2_n3_join_n3_n2; assumption,
end