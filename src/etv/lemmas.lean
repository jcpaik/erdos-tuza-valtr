import lib.list

import etv.defs
import etv.label

variables {α : Type*} [linear_order α] (C : config α)

lemma config.join_ncup_ncup (S : finset α)
  {n : ℕ} (hn : 2 ≤ n)
  (cap4_free : ¬C.has_ncap 4 S)
  {c1 : list α} (hc1 : C.ncup n c1) (c1_in_S : c1.in S)
  {c2 : list α} (hc2 : C.ncup n c2) (c2_in_S : c2.in S)
  (x : α) (hx1 : x ∈ c1.last') (hx2 : x ∈ c2.head') : C.has_ngon (n+1) S :=
begin
  -- Introduce variables
  cases hc1 with c1_cup c1_length,
  cases hc2 with c2_cup c2_length,
  have c1_size2 : 2 ≤ c1.length := by linarith,
  rcases list.take_last2 c1_size2 with ⟨a, x, c1', eq_c1⟩, 
  subst eq_c1, simp at hx1, subst hx1,
  have c2_size2 : 2 ≤ c2.length := by linarith,
  rcases list.take_head2 c2_size2 with ⟨x, b, c2', eq_c2⟩,
  subst eq_c2, simp at hx2, subst hx2,

  have hax_hxb : a < x ∧ x < b := 
    by simp [config.cup] at c1_cup c2_cup; tauto,
  have hab : a < b := has_lt.lt.trans hax_hxb.left hax_hxb.right,
  have haxbS : a ∈ S ∧ x ∈ S ∧ b ∈ S := 
    by simp at c1_in_S c2_in_S; tauto,
  
  have lab := C.cap4_free_label cap4_free,
  have c1'_cup := C.cup_init c1_cup, simp at c1'_cup,
  have c2'_cup := C.cup_tail c2_cup, simp at c2'_cup,
  
  by_cases hl : lab.slope a b,
  { 
    have ab_cup : C.cup (c1' ++ [a] ++ [b]) :=
      by apply lab.extend_right_cup hl c1'_cup;
        simp at c1_in_S; simp at c2_in_S;
        try {simp}; 
        try {tauto},
    have hc1'_a : c1' ++ [a] ≠ [] := by simp,
    set c1'_a := c1' ++ [a] with eq_c1'_a,
    rcases ⟨list.take_head hc1'_a⟩ with ⟨d, c1_, eq_d⟩,
    have eq : c1' ++ [a, x] = c1' ++ [a] ++ [x] := by simp, 
    rw ←eq_c1'_a at eq, rw eq_d at eq, rw eq at *,
    have d_in_S : d ∈ S := begin
      simp at c1_in_S, tauto,
    end,
    have hdx : d < x := begin
      apply C.cup_head'_lt_last' d x c1_cup; simp,
      exact le_add_self,
    end,
    by_cases dxb : C.cup3 d x b,
    { apply C.ncup_is_ngon, exact le_add_right hn,
      use (d :: x :: b :: c2'), simp, 
      simp at c2_length c2_in_S, tauto },
    { rw eq_d at *, 
      use [[d, x, b], d :: c1_ ++ [b]],
      refine ⟨⟨⟨_, _, _⟩, _⟩, _, _⟩,
      simp, simp, tauto, simp, simp at ab_cup,
      refine ⟨_, _⟩, linarith, assumption,
      simp, simp at c1_length, linarith, simp, tauto,
      simp, simp at c1_in_S, tauto,
     } },
    
end 