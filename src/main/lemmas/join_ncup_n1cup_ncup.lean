import order

import lib.list

import etv

open order_dual

variables {α : Type*} [linear_order α] (C : config α)

lemma config.join_ncup_n1cup_ncup_ff 
  (S : finset α) (cap4_free : ¬C.has_ncap 4 S)
  {n : ℕ} (hn : 1 ≤ n) (x y : α)
  {P : list α} (hPx : C.ncup (n+1) (P ++ [x])) (Px_in_S : (P ++ [x]).in S)
  {Q : list α} (hxQy : C.ncup (n+2) (x :: Q ++ [y])) 
  (xQy_in_S : (x :: Q ++ [y]).in S)
  {R : list α} (hyR : C.ncup (n+1) (y :: R)) (yR_in_S : (y :: R).in S)
  (label : C.label S) (sxy : ¬label.slope x y) :
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s :=
begin
  have x_in_S : x ∈ S := by simp at xQy_in_S; tauto,
  have y_in_S : y ∈ S := by simp at xQy_in_S; tauto,
  have x_lt_y : x < y := begin 
    apply hxQy.head'_lt_last' x y, 
    simp, dec_trivial, simp, simp,
  end,

  have P_nnil : P ≠ [] := begin
    intro h, subst h, cases hPx with _ eq, simp at eq,
    rw eq at hn, exact nat.lt_asymm hn hn,
  end,
  have Q_nnil : Q ≠ [] := begin
    intro h, subst h, cases hxQy with _ eq, simp at eq,
    rw eq at hn, exact nat.lt_asymm hn hn,
  end,
  rcases list.take_last P_nnil with ⟨a, P', eq_P⟩, subst eq_P,
  rcases list.take_head Q_nnil with ⟨b, Q', eq_Q⟩, subst eq_Q,
  clear P_nnil Q_nnil,
  have a_in_S : a ∈ S := by simp at Px_in_S; tauto,
  have b_in_S : b ∈ S := by simp at xQy_in_S; tauto,

  have R_nnil : R ≠ [] := begin
    intro h, subst h, cases hyR with _ eq, simp at eq,
    rw eq at hn, exact nat.lt_asymm hn hn,
  end,
  rcases list.take_last R_nnil with ⟨z, R', eq_R⟩,
  have xy_laced : C.has_laced (n+2) S x y := begin
    have hy : C.ncup 1 [y] := by simp,
    existsi [_, _, _, _, _, hPx, hxQy, hy], 
    refine ⟨_, _, _⟩,
    split, assumption, split, assumption, 
    simp, simp at xQy_in_S, tauto,
    simp, simp,
  end,
  have xz_laced : C.has_laced (n+2) S x z := begin
    have hxyR : C.ncup (n+2) (x :: y :: R) := begin
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
    simp, dec_trivial, simp, simp,
  end,
  have a_lt_b : a < b := has_lt.lt.trans a_lt_x x_lt_b,
  by_cases sab : label.slope a b, swap,
  -- case ¬label.slope a b
  { have hQy := hxQy.tail, simp at hQy,
    have haQy : C.ncup (n+2) (a :: b :: Q' ++ [y]) := begin
      apply hQy.extend_left sab; try {assumption},
      simp, simp at xQy_in_S, tauto, simp,
    end,
    have ha : C.ncup 1 [a] := by simp,
    have ay_laced : C.has_laced (n+2) S a y := begin
      existsi [_, _, _, _, _, ha, haQy, hyR],
      refine ⟨_, _, _⟩, 
      simp, simp at xQy_in_S yR_in_S, tauto,
      rw nat.add_comm, simp,
    end,
    use [a, x, y, z], split,
    { split, assumption, split, 
      exact le_of_lt x_lt_y, assumption },
    { tauto }, },
  -- case label.slope a b
  have b_lt_y : b < y := begin
    have hQy := hxQy.tail, simp at hQy,
    apply hQy.head'_lt_last' b y; simp, dec_trivial,
  end,
  have hP := hPx.init, simp at hP,
  have hPb : C.ncup (n+1) (P' ++ [a] ++ [b]) := begin
    apply hP.extend_right sab; try { assumption },
    simp; simp at Px_in_S; tauto,
    simp,
  end,
  by_cases sby : label.slope b y, swap,
  { have bz_laced : C.has_laced (n+2) S b z := begin
      have hbyR : C.ncup (n+2) (b :: y :: R) := begin
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
  { have hPby : C.ncup (n+2) (P' ++ [a] ++ [b] ++ [y]) := begin
      apply hPb.extend_right sby; try { assumption },
      simp; simp at Px_in_S; tauto, simp,
    end,
    have P_nnil : P' ++ [a] ≠ [] := by simp,
    rcases list.take_head P_nnil with ⟨w, P_, eq_P_⟩,
    rw eq_P_ at hPby,
    have wy_laced : C.has_laced (n+2) S w y := begin
      have hw : C.ncup 1 [w] := by simp,
      existsi [_, _, _, _, _, hw, hPby, hyR], 
      refine ⟨_, _, _⟩,
      rw eq_P_ at Px_in_S, simp at yR_in_S Px_in_S, simp, tauto,
      rw nat.add_comm, simp,
    end,
    use [w, x, y, z], split, split,
    rw eq_P_ at hPx, apply hPx.head'_lt_last' w x; simp, dec_trivial,
    split, exact le_of_lt x_lt_y, assumption, tauto },
end

lemma config.join_ncup_n1cup_ncup_tt
  (S : finset α) (cap4_free : ¬C.has_ncap 4 S)
  {n : ℕ} (hn : 1 ≤ n) (x y : α)
  {P : list α} (hPx : C.ncup (n+1) (P ++ [x])) (Px_in_S : (P ++ [x]).in S)
  {Q : list α} (hxQy : C.ncup (n+2) (x :: Q ++ [y])) 
  (xQy_in_S : (x :: Q ++ [y]).in S)
  {R : list α} (hyR : C.ncup (n+1) (y :: R)) (yR_in_S : (y :: R).in S)
  (label : C.label S) (sxy : label.slope x y) :
  ∃ p q r s, C.has_interweaved_laced (n+2) S p q r s :=
begin
  have mirrored_goal : ∃ s r q p, 
    C.mirror.has_interweaved_laced (n+2) S.mirror s r q p :=
  begin
    rw ←mirror.ncup at hPx hxQy hyR, simp at hPx hxQy hyR,
    rw ←mirror.has_ncap at cap4_free,
    rw ←list.mirror_in at Px_in_S xQy_in_S yR_in_S,
    simp [-list.cons_in, -list.append_in] at Px_in_S xQy_in_S yR_in_S,
    have syx := sxy, rw ←mirror_slope at syx,
    apply C.mirror.join_ncup_n1cup_ncup_ff 
      _ _ _ (to_dual y) (to_dual x)
      hyR _ hxQy _ hPx _ label.mirror _; assumption,
  end,
  simp at mirrored_goal,
  rcases mirrored_goal with ⟨s, r, q, p, h⟩,
  rw mirror.has_interweaved_laced at h,
  use [p, q, r, s], exact h,
end

lemma config.join_ncup_n1cup_ncup (S : finset α)
  {n : ℕ} (hn : 2 ≤ n)
  (cap4_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n+2) S)
  {cx : list α} (hcx : C.ncup n cx) (cx_in_S : cx.in S)
  {c : list α} (hc : C.ncup (n+1) c) (c_in_S : c.in S)
  {cy : list α} (hcy : C.ncup n cy) (cy_in_S : cy.in S)
  (x : α) (hxcx : x ∈ cx.last') (hxc : x ∈ c.head')
  (y : α) (hyc : y ∈ c.last') (hycy : y ∈ cy.head') : 
  ∃ p q r s, C.has_interweaved_laced (n+1) S p q r s :=
begin
  have cx_nnil : cx ≠ [] := begin
    intro h, subst h, simp at hxcx, assumption,
  end,
  rcases list.take_last cx_nnil with ⟨x, P, eq_P⟩, subst eq_P,
  have c_nnil : c ≠ [] := begin
    intro h, subst h, simp at hxc, assumption,
  end,
  rcases list.take_head c_nnil with ⟨x, Q', eq_Q'⟩, subst eq_Q',
  simp at hxc, subst hxc, simp at hxcx, subst hxcx,
  clear cx_nnil c_nnil,

  have Q'_nnil : Q' ≠ [] := begin
    intro h, subst h, cases hc with _ l, simp at l,
    subst l, exact nat.not_succ_le_zero 1 hn,
  end,
  rcases list.take_last Q'_nnil with ⟨y, Q, eq_Q⟩, subst eq_Q,
  have cy_nnil : cy ≠ [] := begin
    intro h, subst h, simp at hycy, assumption,
  end,
  rcases list.take_head cy_nnil with ⟨y, R, eq_R⟩, subst eq_R, 
  simp at hyc, subst hyc, simp at hycy, subst hycy,
  clear Q'_nnil cy_nnil,

  cases n, simp at hn, tauto,
  have label := cap4_free_label cap4_free,
  by_cases sxy : label.slope x y,
  { apply C.join_ncup_n1cup_ncup_tt S; try {assumption},
    cases hn with _ hn, simp, exact le_of_lt hn, },
  { apply C.join_ncup_n1cup_ncup_ff S; try {assumption},
    cases hn with _ hn, simp, exact le_of_lt hn, },
end