import order

import lib.list

import etv

open order_dual

variables {α : Type*} [linear_order α] (C : config α)

lemma config.join_n_n_interweaved (S : finset α) (n : ℕ)
  {c1 : list α} (c1_cup : C.ncup (n+2) c1) (c1_in_S : c1.in S)
  {c2 : list α} (c2_cup : C.ncup (n+2) c2) (c2_in_S : c2.in S)
  (h : c1.last' = c2.head') :
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s :=
begin
  rcases c1_cup.take_head_last with ⟨p, c1', q, eq_c1, c1'_cup⟩,
  rcases c2_cup.take_head_last with ⟨q, c2', r, eq_c2, c2'_cup⟩,
  rw [eq_c1, eq_c2] at h, simp at h, subst h,
  use [p, q, q, r], refine ⟨_, _, _⟩,
  sorry, sorry, sorry,
end

lemma config.join_n_n1_join_n1_n (S : finset α) (n : ℕ)
  (cap4_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n+3) S)
  {cx : list α} (cx_cup : C.ncup (n+1) cx) (cx_in_S : cx.in S)
  {cx1 : list α} (cx1_cup : C.ncup (n+2) cx1) (cx1_in_S : cx1.in S)
  {cy1 : list α} (cy1_cup : C.ncup (n+2) cy1) (cy1_in_S : cy1.in S)
  {cy : list α} (cy_cup : C.ncup (n+1) cy) (cy_in_S : cy.in S)
  (x : α) (cx_last : x ∈ cx.last') (cx1_head : x ∈ cx1.head')
  (y : α) (cy1_last : y ∈ cy1.last') (cy_head : y ∈ cy.head') : 
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s :=
begin
  sorry
end