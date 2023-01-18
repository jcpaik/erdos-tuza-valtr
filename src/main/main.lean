import data.nat.choose
import data.finset

import config
import etv

import main.defs
import main.lemmas
import main.induction_step

open_locale classical
noncomputable theory

variables {α : Type*} [linear_order α] (C : config α)

open order_dual

theorem config.mirror_main_goal (n : ℕ) :
  C.main_goal n → C.mirror.main_goal n :=
begin
  intros h Sm hSm cap4_free cup_free,
  have eq_S : Sm.of_mirror.mirror = Sm := finset.of_mirror_mirror,
  rw ←eq_S at ⊢ hSm cap4_free cup_free,
  set S := Sm.of_mirror,
  rw finset.mirror_card at hSm,
  rw mirror.has_ncap at cap4_free,
  rw mirror.has_ncup at cup_free,
  have goal := h S hSm cap4_free cup_free,
  rcases goal with ⟨p, q, r, s, interweave⟩,
  existsi [to_dual s, to_dual r, to_dual q, to_dual p],
  rw mirror.has_interweaved_laced,
  exact interweave,
end

theorem config.main_lemma (n : ℕ) : C.main_goal n :=
begin
  induction n with n ih,
  { intros S hS cap4_free cup_free, simp at hS,
    set Sl := S.sort (≤) with def_Sl,
    have Sl_card : 3 ≤ Sl.length := by rw def_Sl; simp; exact hS,
    have mem_Sl : ∀ {a : α}, a ∈ Sl ↔ a ∈ S := begin 
      intros a, rw def_Sl, exact finset.mem_sort (≤) end,
    -- Take three elements of S
    rcases list.take_head3 Sl_card with ⟨a, b, c, Sl', eq_Sl⟩,
    have abc_mem : a ∈ S ∧ b ∈ S ∧ c ∈ S := by
      rw [←mem_Sl, ←mem_Sl, ←mem_Sl]; rw eq_Sl; simp,
    have abc_lt : a < b ∧ b < c := begin 
      have sorted := S.sort_sorted_lt, 
      rw [←def_Sl, eq_Sl] at sorted,
      simp at sorted, tauto, end,
    refine ⟨a, b, b, c, _, ⟨_, _⟩⟩,
    exact ⟨abc_lt.left, le_refl b, abc_lt.right⟩,
    use [1, 1, [a], [a, b], [b]], simp, tauto,
    use [1, 1, [b], [b, c], [c]], simp, tauto, },
  { intros S hS cap4_free cup_free,
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
    apply C.join_n2_n3_join_n3_n2; assumption, },
end

theorem main (n : ℕ) (C : config α) 
  (S : finset α) (hS : nat.choose (n+2) 2 + 2 ≤ S.card) :
  C.has_ncap 4 S ∨ C.has_ngon (n+3) S :=
begin
  by_cases has_cap4 : C.has_ncap 4 S, left, exact has_cap4,
  by_cases has_cup : C.has_ncup (n+3) S, 
  { right, apply ncup_is_ngon _ has_cup, dec_trivial, },
  rcases C.main_lemma n S hS has_cap4 has_cup with ⟨p, q, r, s, laced⟩,
  right, exact C.has_interweaved_laced_has_ngon
    has_cap4 laced,
end