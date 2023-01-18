import order

import lib.list

import etv
import main.lemmas.join_n2_n3_n2

open order_dual

variables {α : Type*} [linear_order α] (C : config α)

lemma config.join_n2_n2_interweaved {S : finset α} {n : ℕ}
  {c1 : list α} (c1_cup : C.ncup (n+2) c1) (c1_in_S : c1.in S)
  {c2 : list α} (c2_cup : C.ncup (n+2) c2) (c2_in_S : c2.in S)
  (x : α) (c1_last : x ∈ c1.last') (c2_head : x ∈ c2.head') :
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s :=
begin
  rcases c1_cup.take_head_last with ⟨p, c1', q, eq_c1, c1'_cup⟩,
  rcases c2_cup.take_head_last with ⟨q, c2', r, eq_c2, c2'_cup⟩,
  rw eq_c1 at c1_last, rw eq_c2 at c2_head, 
  simp at c1_last c2_head, subst c1_last, subst c2_head,
  use [p, q, q, r], refine ⟨_, _, _⟩,
  { refine ⟨_, _, _⟩, 
    rw eq_c1 at c1_cup, apply c1_cup.head'_lt_last' p q; simp, simp,
    rw eq_c2 at c2_cup, apply c2_cup.head'_lt_last' q r; simp, },
  { existsi [1, n+1, [p], c1, c2.init, _, c1_cup, c2_cup.init], swap, simp,
    rw eq_c1 at ⊢ c1_in_S, rw eq_c2 at ⊢ c2_in_S, 
    simp at ⊢ c1_in_S c2_in_S, ring_nf, tauto, },
  { existsi [n+1, 1, c1.tail, c2, [r], c1_cup.tail, c2_cup, _], swap, simp,
    rw eq_c1 at ⊢ c1_in_S, rw eq_c2 at ⊢ c2_in_S, 
    simp at ⊢ c1_in_S c2_in_S, tauto, },
end

lemma config.join_n2_n3_join_n3_n2_main (S : finset α) (n : ℕ)
  (cap4_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n+4) S)
  {cx : list α} (cx_cup : C.ncup (n+2) cx) (cx_in_S : cx.in S)
  {cx1 : list α} (cx1_cup : C.ncup (n+3) cx1) (cx1_in_S : cx1.in S)
  {cy1 : list α} (cy1_cup : C.ncup (n+3) cy1) (cy1_in_S : cy1.in S)
  {cy : list α} (cy_cup : C.ncup (n+2) cy) (cy_in_S : cy.in S)
  (x : α) (cx_last : x ∈ cx.last') (cx1_head : x ∈ cx1.head')
  (y : α) (cy1_last : y ∈ cy1.last') (cy_head : y ∈ cy.head') : 
  ∃ p q r s, C.has_interweaved_laced (n+3) S p q r s :=
begin
  have l := cap4_free_label cap4_free,
  have x_in_S := cx_in_S _ (list.mem_of_mem_last' cx_last),
  have y_in_S := cy_in_S _ (list.mem_of_mem_head' cy_head),
  rcases lt_or_le y x with hxy | hxy,
  -- Case y < x
  { by_cases lyx : l.slope y x,
    { exfalso, apply cup_free, use cy1 ++ [x], split,
      apply cy1_cup.extend_right lyx; try { assumption },
      simp, split; assumption, },
    { exfalso, apply cup_free, use y :: cx1, split,
      apply cx1_cup.extend_left lyx; try { assumption },
      simp, split; assumption }, },
  -- Case x ≤ y
  rcases cx1_cup.take_head_last with ⟨x, cx1', z, eq_cx1, cx1'_cup⟩,
  rw eq_cx1 at cx1_head, simp at cx1_head, subst cx1_head,
  rcases cy1_cup.take_head_last with ⟨w, cy1', y, eq_cy1, cy1'_cup⟩,
  rw eq_cy1 at cy1_last, simp at cy1_last, subst cy1_last,
  have z_in_S : z ∈ S := by rw eq_cx1 at cx1_in_S; simp at cx1_in_S; tauto,
  have w_in_S : w ∈ S := by rw eq_cy1 at cy1_in_S; simp at cy1_in_S; tauto,
  rcases lt_trichotomy x w with hwx | hwx | hwx, swap,
  { subst hwx, apply C.join_n2_n3_n2 S cap4_free cup_free
      cx_cup cx_in_S cy1_cup cy1_in_S cy_cup cy_in_S 
      x cx_last _ y _ cy_head; rw eq_cy1; simp, },
  { by_cases lxw : l.slope x w,
    { have cxw_cup : C.ncup (n + 3) (cx ++ [w]) := 
        by apply cx_cup.extend_right lxw; try {assumption},
      apply C.join_n2_n2_interweaved cxw_cup _ cy1_cup cy1_in_S w,
      simp, rw eq_cy1, simp, simp, tauto, },
    { exfalso, apply cup_free, use x :: cy1, split,
      apply cy1_cup.extend_left lxw; try {assumption}, rw eq_cy1, simp,
      simp, split; assumption, }, },
  -- w < x
  rcases lt_trichotomy z y with hyz | hyz | hyz, swap,
  { subst hyz, apply C.join_n2_n3_n2 S cap4_free cup_free
      cx_cup cx_in_S cx1_cup cx1_in_S cy_cup cy_in_S 
      x cx_last _ z _ cy_head; rw eq_cx1; simp, },
  { by_cases lzy : l.slope z y,
    { exfalso, apply cup_free, use cx1 ++ [y], split,
      apply cx1_cup.extend_right lzy; try {assumption}, rw eq_cx1, simp,
      simp, split; assumption, },
    { have zcy_cup : C.ncup (n + 3) (z :: cy) := 
        by apply cy_cup.extend_left lzy; try {assumption},
      apply C.join_n2_n2_interweaved cx1_cup _ zcy_cup _ z,
      rw eq_cx1, simp, simp, tauto, simp, tauto, }, },
  -- y < z
  use [w, x, y, z], refine ⟨_, _, _⟩, tauto,
  { existsi [1, n+2, [w], cy1, cy, _, cy1_cup, cy_cup], swap, simp,
    split, simp, tauto, split, ring_nf, rw eq_cy1, simp, assumption, },
  { existsi [n+2, 1, cx, cx1, [z], cx_cup, cx1_cup, _], swap, simp,
    split, simp, tauto, split, ring_nf, rw eq_cx1, simp, assumption, },
end

lemma config.join_n2_n3_join_n3_n2 (S : finset α) (n : ℕ)
  (cap4_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n+4) S)
  (hx : C.has_join (n+2) (n+3) S) (hy : C.has_join (n+3) (n+2) S) : 
  ∃ p q r s, C.has_interweaved_laced (n+3) S p q r s := 
begin
  rcases hx with ⟨x, cx, cx1, 
    ⟨cx_cup, cx_in_S, cx_last⟩, ⟨cx1_cup, cx1_in_S, cx1_head⟩⟩,
  rcases hy with ⟨y, cy1, cy, 
    ⟨cy1_cup, cy1_in_S, cy1_last⟩, ⟨cy_cup, cy_in_S, cy_head⟩⟩,
  apply C.join_n2_n3_join_n3_n2_main S n 
    cap4_free cup_free cx_cup cx_in_S cx1_cup cx1_in_S 
    cy1_cup cy1_in_S cy_cup cy_in_S x cx_last cx1_head
    y cy1_last cy_head,
end