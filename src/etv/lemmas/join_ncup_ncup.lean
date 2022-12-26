import lib.list

import etv.defs
import etv.label

variables {α : Type*} [linear_order α] (C : config α)

lemma config.join_ncup_ncap_case_ff
  (S : finset α) (n : ℕ) (a x b : α) (c1 c2 : list α) (lab : C.label S)
  (a_in_S : a ∈ S) (x_in_S : x ∈ S) (b_in_S : b ∈ S)
  (hc1 : C.ncup (n+2) (c1 ++ [a, x])) (c1_in_S : c1.in S)
  (hc2 : C.ncup (n+2) (x :: b :: c2)) (c2_in_S : c2.in S)
  (sab : ¬lab.slope a b) : 
  C.has_ngon (n+3) S :=
begin
  have hax : a < x := by simp [config.cup, config.ncup] at hc1; tauto,
  have hxb : x < b := by simp [config.cup, config.ncup] at hc2; tauto,
  have hab : a < b := has_lt.lt.trans hax hxb,
  have h_b_c2 : b :: c2 ≠ [] := by simp,
  rcases list.take_last h_b_c2 with ⟨c, c3, eq_c2⟩,
  rw eq_c2 at hc2,
  have hxc : x < c := by
    apply hc2.head'_lt_last' x c; simp; dec_trivial,
  have c_in_S : c ∈ S := begin
    have h_in : (b :: c2).in S := by simp; tauto,
    rw eq_c2 at h_in, simp at h_in, tauto,
  end,
  by_cases haxc : C.cup3 a x c,
  { apply ncup_is_ngon, dec_trivial,
    use c1 ++ [a, x, c], split, split,
    simp, rw config.ncup at hc1, tauto,
    simp, simp [config.ncup] at hc1, tauto,
    simp, tauto },
  { use [[a, x, c], a :: (c3 ++ [c])],
    refine ⟨⟨_, _⟩, _, _⟩; try {simp}; try {tauto},
    split, tauto, split, dec_trivial,
    rw ←eq_c2, rw ←eq_c2 at hc2,
    have hbc2 := hc2.tail.left, simp at hbc2,
    apply hbc2.extend_left sab; try {tauto},
    simp, tauto, simp [config.ncup] at hc2, 
    ring_nf, ring_nf at hc2, simp, simp at hc2, 
    exact hc2.right, split, assumption,
    have hh : (b :: c2).in S := by simp; tauto,
    rw eq_c2 at hh, simp at hh, exact hh },
end

lemma config.join_ncup_ncap_case_tt
  (S : finset α) (n : ℕ) (a x b : α) (c1 c2 : list α) (lab : C.label S)
  (a_in_S : a ∈ S) (x_in_S : x ∈ S) (b_in_S : b ∈ S)
  (hc1 : C.ncup (n+2) (c1 ++ [a, x])) (c1_in_S : c1.in S)
  (hc2 : C.ncup (n+2) (x :: b :: c2)) (c2_in_S : c2.in S)
  (hab : lab.slope a b) : 
  C.has_ngon (n+3) S :=
begin
  sorry,
end

lemma config.join_ncup_ncup (S : finset α)
  {n : ℕ} (hn : 2 ≤ n)
  (cap4_free : ¬C.has_ncap 4 S)
  {c1 : list α} (hc1 : C.ncup n c1) (c1_in_S : c1.in S)
  {c2 : list α} (hc2 : C.ncup n c2) (c2_in_S : c2.in S)
  (x : α) (hx1 : x ∈ c1.last') (hx2 : x ∈ c2.head') : C.has_ngon (n+1) S :=
begin
  -- Introduce variables
  rw le_iff_exists_add' at hn, 
  cases hn with n en, subst en, ring_nf,
  have c1_size2 : 2 ≤ c1.length := by cases hc1; linarith,
  rcases list.take_last2 c1_size2 with ⟨a, x, c1', eq_c1⟩, 
  subst eq_c1, simp at hx1, subst hx1,
  have c2_size2 : 2 ≤ c2.length := by cases hc2; linarith,
  rcases list.take_head2 c2_size2 with ⟨x, b, c2', eq_c2⟩,
  subst eq_c2, simp at hx2, subst hx2,

  have lab := cap4_free_label cap4_free,
  by_cases hl : lab.slope a b,
  { apply C.join_ncup_ncap_case_tt S n a x b c1' c2' lab;
    simp at c1_in_S c2_in_S; tauto },
  { apply C.join_ncup_ncap_case_ff S n a x b c1' c2' lab;
    simp at c1_in_S c2_in_S; tauto }, 
end 