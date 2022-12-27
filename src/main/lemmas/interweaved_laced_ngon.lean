import order

import lib.list

import etv.defs
import etv.label

open order_dual

variables {α : Type*} [linear_order α] (C : config α)

lemma config.has_interweaved_laced_has_ngon 
  {n : ℕ} (hn : 3 ≤ n) {S : finset α} 
  (cap4_free : ¬C.has_ncap 4 S) (p q r s : α) :
  C.has_interweaved_laced n S p q r s → C.has_ngon (n+1) S :=
begin
  intro h, rcases h with ⟨⟨p_lt_q, q_le_r, r_lt_s⟩, ⟨pr_laced, qs_laced⟩⟩,
  rcases pr_laced with ⟨a, b, cp, c1, cr, hcp, hc1, hcr, 
    ⟨eq_ab, cp_last, c1_head, c1_last, cq_head⟩⟩,
  rcases qs_laced with ⟨c, d, cq, c2, cs, hcq, hc2, hcs, 
    ⟨eq_cd, cq_last, c2_head, c2_last, cr_head⟩⟩,
  
  have label := cap4_free_label cap4_free,
  by_cases spq : label.slope p q, swap,
  { apply ncup_is_ngon, linarith,
    have hpc2 : C.ncup (n+1) (p :: c2) := begin
      apply hc2.extend_left spq; try {assumption},
      sorry, sorry,
    end,
    sorry, },
  sorry,
end