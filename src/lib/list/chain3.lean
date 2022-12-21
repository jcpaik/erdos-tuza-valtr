import tactic.basic

import lib.list.defs

variables {α : Type*} {R : α → α → α → Prop}

namespace list

theorem chain3_split {a b c d : α} {l1 l2 : list α} : 
  chain3 R a b (l1 ++ c :: d :: l2) ↔
  chain3 R a b (l1 ++ [c, d]) ∧ chain3 R c d l2 := 
by induction l1 with x l1 IH generalizing a b;
  simp only [*, nil_append, cons_append, chain3.nil, chain3_cons, and_true, and_assoc]

@[simp] theorem chain3'_nil : chain3' R [] := trivial

@[simp] theorem chain3'_singleton (a : α) : chain3' R [a] := trivial

@[simp] theorem chain3'_pair (a b : α) : chain3' R [a, b] := chain3.nil

@[simp] theorem chain3'_cons {x y z l} : 
  chain3' R (x :: y :: z :: l) ↔ R x y z ∧ chain3' R (y :: z :: l) := 
chain3_cons 

theorem chain3'_split {a b : α}: ∀ {l1 l2 : list α},
  chain3' R (l1 ++ a :: b :: l2) ↔
  chain3' R (l1 ++ [a, b]) ∧ chain3' R (a :: b :: l2)
| [] l2 := (and_iff_right (chain3'_pair a b)).symm
| [c] l2 := by simp -- todo
| (c :: d :: l1) l2 := chain3_split 

end list