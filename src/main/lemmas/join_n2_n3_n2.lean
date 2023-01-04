import order

import lib.list

import etv

open order_dual

variables {α : Type*} [linear_order α] (C : config α)

lemma config.join_n2_n3_n2_ff 
  (S : finset α) (cap4_free : ¬C.has_ncap 4 S)
  {n : ℕ} (x y : α)
  {P : list α} (hPx : C.ncup (n+2) (P ++ [x])) (Px_in_S : (P ++ [x]).in S)
  {Q : list α} (hxQy : C.ncup (n+3) (x :: Q ++ [y])) 
  (xQy_in_S : (x :: Q ++ [y]).in S)
  {R : list α} (hyR : C.ncup (n+2) (y :: R)) (yR_in_S : (y :: R).in S)
  (label : C.label S) (sxy : ¬label.slope x y) :
  ∃ p q r s, C.has_interweaved_laced (n+3) S p q r s :=
begin
  have x_in_S : x ∈ S := by simp at xQy_in_S; tauto,
  have y_in_S : y ∈ S := by simp at xQy_in_S; tauto,
  have x_lt_y : x < y := by apply hxQy.head'_lt_last' x y; simp,
  
  have hP := hPx.init, simp at hP,
  have hQy := hxQy.tail, simp at hQy,
  rcases hP.init_append_last with ⟨P', a, eq_P, hP'⟩, subst eq_P,
  rcases hQy.cons_head_tail with ⟨b, Q', eq_Q, hQ'⟩,
  have eq_xQy : x :: Q ++ [y] = x :: (Q ++ [y]) := by simp,
  rw [eq_xQy, eq_Q] at *, clear eq_xQy,
  have a_in_S : a ∈ S := by simp at Px_in_S; tauto,
  have b_in_S : b ∈ S := by simp at xQy_in_S; tauto,

  have hR := hyR.tail, simp at hR,
  rcases hR.init_append_last with ⟨R', z, eq_R, hR'⟩,
  have xy_laced : C.has_laced (n+3) S x y := begin
    have hy : C.ncup 1 [y] := by simp,
    existsi [_, _, _, _, _, hPx, hxQy, hy], 
    refine ⟨_, _, _⟩, 
    split, assumption, split, assumption,
    simp, simp at xQy_in_S, tauto,
    simp, simp, rw ←eq_Q, simp,
  end,
  have xz_laced : C.has_laced (n+3) S x z := begin
    have hxyR : C.ncup (n+3) (x :: y :: R) := begin
      apply hyR.extend_left sxy; try {assumption}, simp,
    end,
    rw eq_R at hxyR,
    have hz : C.ncup 1 [z] := by simp,
    existsi [_, _, _, _, _, hPx, hxyR, hz],
    refine ⟨_, _, _⟩,
    split, assumption, rw eq_R at yR_in_S,
    simp, simp at yR_in_S, tauto,
    simp, simp,
  end,

  have a_lt_x : a < x := 
    by rw [config.ncup, config.cup] at hPx; simp at hPx; tauto,
  have x_lt_b : x < b :=
    by rw [config.ncup, config.cup] at hxQy; simp at hxQy; tauto,
  have y_lt_z : y < z := begin
    rw eq_R at hyR, apply hyR.head'_lt_last' y z,
    simp, simp,
  end,
  have a_lt_b : a < b := has_lt.lt.trans a_lt_x x_lt_b,
  by_cases sab : label.slope a b, swap,
  -- case ¬label.slope a b
  { have hQy := hxQy.tail, simp at hQy, rw ←eq_Q at hQy,
    have haQy : C.ncup (n+3) (a :: Q ++ [y]) := begin
      apply hQy.extend_left sab; try {assumption},
      simp, rw ←eq_Q at xQy_in_S, simp at xQy_in_S, tauto, simp,
      rw eq_Q, simp,
    end,
    have ha : C.ncup 1 [a] := by simp,
    have ay_laced : C.has_laced (n+3) S a y := begin
      existsi [_, _, _, _, _, ha, haQy, hyR],
      refine ⟨_, _, _⟩, 
      simp, rw ←eq_Q at xQy_in_S, simp at xQy_in_S yR_in_S, tauto,
      rw nat.add_comm, simp,
    end,
    use [a, x, y, z], split,
    { split, assumption, split, 
      exact le_of_lt x_lt_y, assumption },
    { tauto }, },
  -- case label.slope a b
  have b_lt_y : b < y := begin
    have hQy := hxQy.tail, simp at hQy,
    apply hQy.head'_lt_last' b y; simp,
    rw ←eq_Q, simp,
  end,
  have hP := hPx.init, simp at hP,
  have hPb : C.ncup (n+2) (P' ++ [a] ++ [b]) := begin
    apply hP.extend_right sab; try { assumption },
    simp; simp at Px_in_S; tauto,
    simp,
  end,
  by_cases sby : label.slope b y, swap,
  { have bz_laced : C.has_laced (n+3) S b z := begin
      have hbyR : C.ncup (n+3) (b :: y :: R) := begin
        apply hyR.extend_left sby; try {assumption}, simp,
      end,
      have hz : C.ncup 1 [z] := by simp,
      existsi [_, _, _, _, _, hPb, hbyR, hz], rw eq_R,
      refine ⟨_, _, _⟩, 
      rw eq_R at yR_in_S, simp at Px_in_S yR_in_S, simp, tauto,
      simp, simp,
    end,
    use [x, b, y, z], split, 
    split, assumption, split, apply le_of_lt, assumption, assumption,
    tauto, },
  { have hPby : C.ncup (n+3) (P' ++ [a] ++ [b] ++ [y]) := begin
      apply hPb.extend_right sby; try { assumption },
      simp; simp at Px_in_S; tauto, simp,
    end,
    have P_nnil : P' ++ [a] ≠ [] := by simp,
    rcases list.take_head P_nnil with ⟨w, P_, eq_P_⟩,
    rw eq_P_ at hPby,
    have wy_laced : C.has_laced (n+3) S w y := begin
      have hw : C.ncup 1 [w] := by simp,
      existsi [_, _, _, _, _, hw, hPby, hyR], 
      refine ⟨_, _, _⟩,
      rw eq_P_ at Px_in_S, simp at yR_in_S Px_in_S, simp, tauto,
      rw nat.add_comm, simp,
    end,
    use [w, x, y, z], split, split,
    rw eq_P_ at hPx, apply hPx.head'_lt_last' w x; simp,
    split, exact le_of_lt x_lt_y, assumption, tauto, },
end

lemma config.join_n2_n3_n2_tt
  (S : finset α) (cap4_free : ¬C.has_ncap 4 S)
  {n : ℕ} (x y : α)
  {P : list α} (hPx : C.ncup (n+2) (P ++ [x])) (Px_in_S : (P ++ [x]).in S)
  {Q : list α} (hxQy : C.ncup (n+3) (x :: Q ++ [y])) 
  (xQy_in_S : (x :: Q ++ [y]).in S)
  {R : list α} (hyR : C.ncup (n+2) (y :: R)) (yR_in_S : (y :: R).in S)
  (label : C.label S) (sxy : label.slope x y) :
  ∃ p q r s, C.has_interweaved_laced (n+3) S p q r s :=
begin
  have mirrored_goal : ∃ s r q p, 
    C.mirror.has_interweaved_laced (n+3) S.mirror s r q p :=
  begin
    rw ←mirror.ncup at hPx hxQy hyR, simp at hPx hxQy hyR,
    rw ←mirror.has_ncap at cap4_free,
    rw ←list.mirror_in at Px_in_S xQy_in_S yR_in_S,
    simp [-list.cons_in, -list.append_in] at Px_in_S xQy_in_S yR_in_S,
    have syx := sxy, rw ←mirror_slope at syx,
    apply C.mirror.join_n2_n3_n2_ff 
      _ _ (to_dual y) (to_dual x)
      hyR _ hxQy _ hPx _ label.mirror _; assumption,
  end,
  simp at mirrored_goal,
  rcases mirrored_goal with ⟨s, r, q, p, h⟩,
  rw mirror.has_interweaved_laced at h,
  use [p, q, r, s], exact h,
end

lemma config.join_n2_n3_n2 (S : finset α) {n : ℕ}
  (cap4_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n+4) S)
  {cx : list α} (cx_ncup : C.ncup (n+2) cx) (cx_in_S : cx.in S)
  {c : list α} (c_ncup : C.ncup (n+3) c) (c_in_S : c.in S)
  {cy : list α} (cy_ncup : C.ncup (n+2) cy) (cy_in_S : cy.in S)
  (x : α) (hxcx : x ∈ cx.last') (hxc : x ∈ c.head')
  (y : α) (hyc : y ∈ c.last') (hycy : y ∈ cy.head') : 
  ∃ p q r s, C.has_interweaved_laced (n+3) S p q r s :=
begin
  rcases c_ncup.take_head_last with ⟨x, Q, y, eq_Q, Q_ncup⟩,
  subst eq_Q, simp at hxc hyc, subst hxc, subst hyc,
  rcases cx_ncup.init_append_last with ⟨P, x, eq_P, P_ncup⟩, 
  subst eq_P, simp at hxcx, subst hxcx,
  rcases cy_ncup.cons_head_tail with ⟨y, R, eq_R, R_ncup⟩,
  subst eq_R, simp at hycy, subst hycy,

  have label := cap4_free_label cap4_free,
  by_cases sxy : label.slope x y,
  { apply C.join_n2_n3_n2_tt S; try {assumption}, },
  { apply C.join_n2_n3_n2_ff S; try {assumption}, },
end