import data.nat.choose
import data.finset

import config
import etv

import main.defs
import main.lemmas

open_locale classical
noncomputable theory

variables {α : Type*} [linear_order α] (C : config α)

namespace config

def delta (n : ℕ) (S : finset α) : finset α :=
  S.filter (λ p, C.beta S p < n ∧ 
    ↑p = (S.filter (λ q, C.beta S q = C.beta S p)).min)

lemma delta_card (n : ℕ) (S : finset α) : (C.delta n S).card ≤ n :=
begin
  rw ←finset.card_range n,
  apply finset.card_le_card_of_inj_on (C.beta S),
  { rw delta, intro a, rw finset.mem_filter, 
    intros h, rcases h with ⟨_, h', _⟩, simp at ⊢ h', exact h', },
  { intros x hx y hy hxy, 
    rw delta at hx hy, simp only [finset.mem_filter] at hx hy,
    rcases hx with ⟨x_in_S, bx_lt_n, x_min⟩,
    rcases hy with ⟨y_in_S, by_lt_n, y_min⟩,
    rw [←with_bot.coe_eq_coe, x_min, y_min, hxy], },
end

lemma not_mem_delta {n : ℕ} {S : finset α} {p' : α} 
  (h : p' ∈ S \ (C.delta n S)) : 
  (n ≤ C.beta S p') ∨ (∃ p, 
    p ∈ C.delta n S ∧ C.beta S p = C.beta S p' ∧ p < p') :=
begin
  rw [delta, finset.mem_sdiff, finset.mem_filter, 
    not_and, not_and_distrib] at h,
  cases h with p'_in_S aux, have h := aux p'_in_S, clear aux,
  by_cases bp_n : C.beta S p' < n, swap,
  { left, exact not_lt.mp bp_n },
  cases h, exact absurd bp_n h,
  right, 
  set row := S.filter (λ q, C.beta S q = C.beta S p') with def_row,
  have row_nonempty : row.nonempty := begin 
    use p', rw def_row, rw finset.mem_filter,
    split, assumption, exact rfl, end,
  have row_in_S : row ⊆ S := finset.filter_subset _ _,
  set p := row.min' row_nonempty with def_p,
  have p_in_row : p ∈ row := finset.min'_mem _ row_nonempty,
  have bp_eq_bp' : C.beta S p = C.beta S p' := begin
    rw def_row at p_in_row, rw finset.mem_filter at p_in_row,
    exact p_in_row.right, end,
  have p'_in_row : p' ∈ row := begin 
    rw def_row, rw finset.mem_filter, split, assumption, 
    exact rfl, end,
  existsi p, refine ⟨_, bp_eq_bp', _⟩,
  { rw delta, simp only [finset.mem_filter], 
    rw bp_eq_bp', rw ←def_row,
    refine ⟨row_in_S p_in_row, bp_n, _⟩,
    rw def_p, exact finset.coe_min' _, },
  { rw ←finset.coe_min' row_nonempty at h,
    suffices p_le_p' : p ≤ p',
    { rw le_iff_lt_or_eq at p_le_p',
      cases p_le_p', 
      assumption, exfalso, apply h, rw [←def_p, p_le_p'], },
    rw def_p, exact finset.min'_le _ _ p'_in_row, },
end

lemma laced_extension (n : ℕ) (S D : finset α) (l : C.label S)
  (cup_free : ¬C.has_ncup (n + 4) S) (D_def : D = C.delta (n + 2) S)
  (a : ℕ) (p' : α) (c : list α) 
  (c_cup : C.ncup a c) (c_in : c.in (S \ D)) (c_head : p' ∈ c.head') : 
  (∃ d : list α, C.ncup (n + 3) d ∧ d.in S ∧ p' ∈ d.last') ∨
  (l.alpha p' = 1 ∧
    ∃ p : α, C.ncup (a + 1) (p :: c) ∧ (p :: c).in S ∧
    l.alpha p = 0 ∧ C.beta S p = C.beta S p') :=
begin
  cases (nat.lt_or_ge (n+2) (C.beta S p')) with beta_p' beta_p',
  { rw nat.lt_iff_add_one_le at beta_p', sorry,
    -- TODO: use exists_beta_cup, and take
    },
  { sorry, },
end

/-
I have a function `f : ℕ → option α` and I want to define a finset `S` defined as `{f 0, f 1, ..., f (n-1)} : finset α` with no elements for values of `f i = none`. Any good way of doing that? (say, so that I can utilize mathlib lemmas the best, like the fact that `S.card ≤ n`)

  ∀ (S : finset α),
  ¬C.has_join (n+2) (n+1) S →
  nat.choose (n+2) 2 + 2 ≤ S.card →
  ¬C.has_ncap 4 S → ¬C.has_ncup (n+3) S → 
-/
theorem main_induction_wlog (n : ℕ) :
  C.main_goal n → C.main_goal_wlog (n+1) :=
begin
  intros ih S no_join S_card cap4_free cup_free,
  have l : C.label S := cap4_free_label cap4_free,
  set D := C.delta (n+2) S with def_D,
  have D_card := C.delta_card (n+2) S, rw ←def_D at D_card,
  have SD_card : (n + 2).choose 2 + 2 ≤ (S \ D).card := begin
    apply @nat.le_of_add_le_add_right D.card,
    rw finset.card_sdiff_add_card,
    apply le_trans _ 
      (finset.card_le_of_subset (finset.subset_union_left S D)),
    apply le_trans _ S_card, 
    apply le_trans (nat.add_le_add_left D_card _) _,
    rw nat.add_right_comm, apply le_of_eq, 
    rw nat.add_right_comm n 1 2, simp, apply symm, rw nat.choose, simp,
    rw nat.add_comm,
  end,
  have t := ih (S \ D) SD_card _ _,
  swap, { intro h, rcases h with ⟨c, ⟨_, c_in⟩⟩,
    apply cap4_free, use c, split, assumption,
    apply list.in_superset _ c_in, exact finset.sdiff_subset S D, },
  swap, { intro h, rcases h with ⟨c, ⟨c_cup, c_in⟩⟩,
    rcases c_cup.take_head_last with ⟨p, c', q, eq_c, -⟩,
    have p_in_c : p ∈ c := by rw eq_c; left; exact rfl,
    have p_in_SD : p ∈ S \ D := c_in _ p_in_c,
    rw def_D at p_in_SD,
    have p_in_S : p ∈ S := (finset.sdiff_subset S D) p_in_SD,
    have c_in_S : c.in S := (λ a ha, (finset.sdiff_subset S D) (c_in a ha)),
    rcases (C.not_mem_delta p_in_SD) with 
      le_bp | ⟨o, o_in_delta, bo_eq_bp, o_lt_p⟩,
    { -- n + 2 ≤ C.beta S p and p is the start of n+3 -cup,
      apply no_join, 
      rcases C.beta_cup S p_in_S with ⟨d, d_in_S, d_ncup, d_last⟩,
      sorry, 

    },
    { have o_in_S : o ∈ S := begin 
        rw [delta, finset.mem_filter] at o_in_delta, 
        exact o_in_delta.left end,
      have ao_lt_ap := (l.beta_eq_alpha_inc o_in_S p_in_S bo_eq_bp).mp o_lt_p,
      have has_cup := l.add_alpha p_in_S c_in_S c_cup (by rw eq_c; simp),
      apply cup_free, ring_nf at ⊢ has_cup,
      have ineq : n + 4 ≤ n + (l.alpha p + 3) := by linarith,
      exact has_ncup_le ineq has_cup, }, },
  { rcases t with ⟨p', q', r, s, 
      ⟨⟨p'_lt_q', q'_le_r, r_lt_s⟩, ⟨laced_pr, laced_qs⟩⟩⟩,
    sorry,
     },
end

end config