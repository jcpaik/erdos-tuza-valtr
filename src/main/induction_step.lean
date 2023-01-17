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

lemma laced_extension (n : ℕ) {S D : finset α} {l : C.label S}
  (cup_free : ¬C.has_ncup (n + 4) S) (def_D : D = C.delta (n + 2) S)
  (no_join: ¬C.has_join (n + 1 + 2) (n + 1 + 1) S)
  {p' r : α} (p'r_laced : C.has_laced (n + 2) (S \ D) p' r) : 
  l.alpha p' = 1 ∧ ∃ p : α, C.has_laced (n + 3) S p r :=
begin
  rcases p'r_laced with ⟨a, b, cp', c, cr, cp'_cup, c_cup, cr_cup, 
    ⟨cp'_in_SD, c_in_SD, cr_in_SD⟩, eq_ab, cp'_last, c_head, c_last, cr_head⟩,
  have p'_in_SD := c_in_SD _ (list.mem_of_mem_head' c_head),
  have p'_in_S := (finset.sdiff_subset S D) p'_in_SD,
  have c_in_S := (λ a ha, (finset.sdiff_subset S D) (c_in_SD a ha)),
  rw def_D at p'_in_SD,
  rcases (C.not_mem_delta p'_in_SD) with 
    p'_beta | ⟨p, p_in_delta, eq_p, p_lt_p'⟩,
  { exfalso, apply no_join,
    rcases C.beta_cup S p'_in_S with ⟨d, d_in_S, d_ncup, d_last⟩,
    rcases d_ncup.take_right_with_last (n+3) p'
      (by dec_trivial) (by linarith) d_last with 
      ⟨d', d'_in_d, d'_cup, d'_last⟩,
    use [p', d', c], tauto, },
  { have p_in_S : p ∈ S := begin 
      rw [delta, finset.mem_filter] at p_in_delta, exact p_in_delta.left end,
    split,
    { have ap_lt_ap' := (l.beta_eq_alpha_inc p_in_S p'_in_S eq_p).mp p_lt_p',
      cases nat.lt_or_ge (l.alpha p') 2 with ap' ap', linarith,
      exfalso, apply cup_free,
      have has_cup := l.add_alpha p'_in_S c_in_S c_cup c_head,
      apply has_ncup_le _ has_cup, linarith, },
    { use p, have a1_le_bp' : a + 1 ≤ C.beta S p' := begin
        have cp'_nnil : cp' ≠ [] := begin 
          intro h, subst h, simp at cp'_last, exact cp'_last end,
        rcases list.take_head cp'_nnil with ⟨o, cp'', eq_cp'⟩,
        sorry,
      end, sorry, }, },
end

/- Lemma: if one has a tight cup, 
  its left end is strictly less than the minimum value of the last row -/
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
    { apply no_join, 
      rcases C.beta_cup S p_in_S with ⟨d, d_in_S, d_ncup, d_last⟩,
      rcases d_ncup.take_right_with_last (n+3) p
        (by dec_trivial) (by linarith) d_last with 
        ⟨d', d'_in_d, d'_cup, d'_last⟩,
      use [p, d', p :: c'], split,
      refine ⟨by assumption, _, by assumption⟩,
      intros a ha, exact d_in_S _ (d'_in_d ha),
      refine ⟨_, _, by simp⟩,
      convert c_cup.init using 1, rw eq_c, simp,
      rw eq_c at c_in_S, simp at ⊢ c_in_S, tauto, },
    { have o_in_S : o ∈ S := begin 
        rw [delta, finset.mem_filter] at o_in_delta, 
        exact o_in_delta.left end,
      have ao_lt_ap := (l.beta_eq_alpha_inc o_in_S p_in_S bo_eq_bp).mp o_lt_p,
      have has_cup := l.add_alpha p_in_S c_in_S c_cup (by rw eq_c; simp),
      apply cup_free, ring_nf at ⊢ has_cup,
      apply has_ncup_le _ has_cup, linarith, }, },
  { rcases t with ⟨p', q', r, s, 
      ⟨⟨p'_lt_q', q'_le_r, r_lt_s⟩, ⟨laced_pr, laced_qs⟩⟩⟩,
    sorry,
     },
end

end config