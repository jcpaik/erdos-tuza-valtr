import order

import lib.list

import etv.defs
import etv.label

open order_dual

variables {α : Type*} [linear_order α] (C : config α)

lemma config.join_ncup_n1cup_ncup (S : finset α)
  {n : ℕ} (hn : 2 ≤ n)
  (cap4_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n+2) S)
  {cx : list α} (hcx : C.ncup n cx) (cx_in_S : cx.in S)
  {c : list α} (hc : C.ncup (n+1) c) (c_in_S : c.in S)
  {cy : list α} (hcy : C.ncup n cx) (cy_in_S : cy.in S)
  (x : α) (hxcx : x ∈ cx.last') (hxc : x ∈ c.head')
  (y : α) (hyc : y ∈ c.last') (hycy : y ∈ cy.head') : 
  ∃ p q r s, C.has_interweaved_laced (n+1) S p q r s := sorry