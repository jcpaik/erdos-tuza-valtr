import lib.list

import etv.defs
import etv.label

variables {α : Type*} [linear_order α] (C : config α)

lemma config.join_ncup_ncup (S : finset α)
  {n : ℕ} (hn : 2 ≤ n)
  (cap4_free : ¬C.has_ncap 4 S)
  (cup_sn_free : ¬C.has_ncup (n+1) S)
  {c1 : list α} (hc1 : C.ncup n c1)
  {c2 : list α} (hc2 : C.ncup n c2)
  (x : α) (hx1 : x ∈ c1.last') (hx2 : x ∈ c2.head') : C.has_ngon n S :=
begin
  cases hc1 with c1_cup c1_length,
  cases hc2 with c2_cup c2_length,
  have c1_size2 : 2 ≤ c1.length := by convert hn,
  rcases list.take_last2 c1_size2 with ⟨a, x, c1', eq_c1⟩,
  rw eq_c1 at hx1, simp at hx1, subst hx1,
  have c2_size2 : 2 ≤ c2.length := by convert hn,
  rcases list.take_head2 c2_size2 with ⟨x, b, c2', eq_c2⟩,
  rw eq_c2 at hx2, simp at hx2, subst hx2,
  
end