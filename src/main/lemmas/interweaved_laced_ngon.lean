import order

import lib.list

import etv
import main.lemmas.join_ncup_ncup

open order_dual

variables {α : Type*} [linear_order α] (C : config α)

lemma config.has_interweaved_laced_has_ngon_ff
  {n : ℕ} (hn : 3 ≤ n) {S : finset α} 
  (cap4_free : ¬C.has_ncap 4 S) {p q r s : α}
  (label : C.label S) (q_lt_r : q < r) (sqr : ¬label.slope q r) :
  C.has_interweaved_laced n S p q r s → C.has_ngon (n+1) S :=
begin
  intro h, rcases h with ⟨⟨p_lt_q, q_le_r, r_lt_s⟩, ⟨pr_laced, qs_laced⟩⟩,
  rcases pr_laced with 
    ⟨a, b, cp, c1, cr, hcp, hc1, hcr, 
    ⟨⟨cp_in_S, c1_in_S, cr_in_S⟩, eq_ab, 
      cp_last, c1_head, c1_last, cr_head⟩⟩,
  rcases qs_laced with 
    ⟨c, d, cq, c2, cs, hcq, hc2, hcs, 
    ⟨⟨cq_in_S, c2_in_S, cs_in_S⟩, eq_cd, 
      cq_last, c2_head, c2_last, cs_head⟩⟩,

  have p_in_S : p ∈ S := begin
    apply list.mem_in c1_in_S,
    exact list.mem_of_mem_head' c1_head,
  end,
  have q_in_S : q ∈ S := begin
    apply list.mem_in c2_in_S,
    exact list.mem_of_mem_head' c2_head,
  end,
  have r_in_S : r ∈ S := begin
    apply list.mem_in c1_in_S,
    exact list.mem_of_mem_last' c1_last,
  end,
  have s_in_S : s ∈ S := begin
    apply list.mem_in c2_in_S,
    exact list.mem_of_mem_last' c2_last,
  end,
  
  have label := cap4_free_label cap4_free,
  by_cases spq : label.slope p q, swap,
  { apply ncup_is_ngon, linarith,
    use (p :: c2), split,
    apply hc2.extend_left spq; assumption,
    simp, tauto },
  -- (spq : ¬label.slope p q) from now on
  by_cases cpqr : C.cup3 p q r,
  { apply ncup_is_ngon, linarith,
    use (cp ++ q :: cr), split, swap, simp, tauto,
    have cp_nnil : cp ≠ [] := begin
      intro h, subst h, simp at cp_last, exact cp_last,
    end,
    rcases list.take_last cp_nnil with ⟨p, cp', eq_cp⟩,
    rw eq_cp at cp_last, simp at cp_last, subst cp_last,
    -- idea: implement a lemma for taking explicit head
    -- from a statement like this
    have cr_nnil : cr ≠ [] := begin
      intro h, subst h, simp at cr_head, exact cr_head,
    end,
    rcases list.take_head cr_nnil with ⟨r, cr', eq_cr⟩, split,
    rw eq_cr at cr_head, simp at cr_head, subst cr_head,
    rw [eq_cp, eq_cr], simp,
    refine ⟨_, _, _⟩, swap, assumption,
    have eq : cp' ++ [p, q] = cp' ++ [p] ++ [q] := by simp,
    rw eq, rw ←eq_cp, 
    apply hcp.left.extend_right spq; try {assumption},
    rw eq_cp, simp,
    rw ←eq_cr, 
    apply hcr.left.extend_left sqr; try {assumption},
    rw eq_cr, simp,
    simp, rw [hcp.right, hcr.right], rw ←eq_ab, 
    rw nat.add_assoc },
  { use [[p, q, r], c1], split, swap, simp, tauto,
    split, swap, rw hc1.right, simp, linarith,
    rw config.gon, simp,
    cases hc1 with c1_cup c1_length, rw c1_length,
    simp at c1_head c1_last, 
    have h2n : 2 ≤ n := by linarith, tauto, },
end

lemma config.has_interweaved_laced_has_ngon_tt
  {n : ℕ} (hn : 3 ≤ n) {S : finset α} 
  (cap4_free : ¬C.has_ncap 4 S) {p q r s : α}
  (label : C.label S) (q_lt_r : q < r) (sqr : label.slope q r) :
  C.has_interweaved_laced n S p q r s → C.has_ngon (n+1) S :=
begin
  rw [←mirror.has_interweaved_laced, ←mirror.has_ngon],
  have label_m := label.mirror,
  -- idea: implement slope.mirror 
  sorry
end

lemma config.has_interweaved_laced_has_ngon 
  {n : ℕ} (hn : 3 ≤ n) {S : finset α} 
  (cap4_free : ¬C.has_ncap 4 S) {p q r s : α} :
  C.has_interweaved_laced n S p q r s → C.has_ngon (n+1) S :=
begin
  intro h, have q_le_r : q ≤ r := 
    by rw config.has_interweaved_laced at h; tauto,
  rw le_iff_eq_or_lt at q_le_r,
  cases q_le_r,
  { subst q_le_r, rcases h with ⟨-, pr_laced, qs_laced⟩,
    rcases pr_laced with ⟨-, -, -, c1, -, -, hc1, -, 
      ⟨-, c1_in_S, -⟩, -, 
      ⟨-, c1_head, c1_last, -⟩⟩,
    rcases qs_laced with ⟨-, -, -, c2, -, -, hc2, -,
      ⟨-, c2_in_S, -⟩, -,
      ⟨-, c2_head, c2_last, -⟩⟩,
    apply C.join_ncup_ncup S _ cap4_free 
      hc1 c1_in_S hc2 c2_in_S q c1_last c2_head,
    linarith },
  rename q_le_r → q_lt_r,

  have label := cap4_free_label cap4_free,
  by_cases sqr : label.slope q r,
  { revert sqr h, 
    apply C.has_interweaved_laced_has_ngon_tt; assumption, },
  { revert sqr h, 
    apply C.has_interweaved_laced_has_ngon_ff; assumption, },
end