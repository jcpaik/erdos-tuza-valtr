-- main erdos-szekeres theorem file
-- uses sublist to give order to cap/cup

import tactic.basic
import tactic.ring
import tactic.linarith
import logic.nontrivial
import .list

open_locale classical
noncomputable theory

variables {α : Type*}

theorem cap_cup_extension
  {s : list α} (s_nodup : s.nodup)
  {c : α → α → α → Prop}
  {cap : list α} (cap_sublist : cap <+ s) 
  (cap_chain: cap.chain3' c) (cap_size2: 2 ≤ cap.length)
  {cup : list α} (cup_sublist : cup <+ s) 
  (cup_chain: cup.chain3' cᶜ) (cup_size2: 2 ≤ cup.length)
  (h : cup.last (list.size2_not_nil cup_size2) = 
       cap.first (list.size2_not_nil cap_size2) ) :
  
  (∃ ext_cap : list α, 
    ext_cap <+ s ∧ 
    ext_cap.chain3' c ∧ 
    ext_cap.length = cap.length + 1) ∨
  (∃ ext_cup : list α, 
    ext_cup <+ s ∧ 
    ext_cup.chain3' cᶜ ∧ 
    ext_cup.length = cup.length + 1) :=
begin
  rcases cap.take_first2 cap_size2 
    with ⟨q', r, cap', ⟨cap_eq, cap_first⟩⟩,
  rcases cup.take_last2 cup_size2 
    with ⟨p, q, cup', ⟨cup_eq, cup_last⟩⟩,
  rw [cap_first, cup_last] at h, subst h,

  -- rudimentary facts
  have pq_in_cup : [p, q] <+ cup, rw cup_eq, simp,
  have pq_in_s : [p, q] <+ s, 
  from list.sublist.trans pq_in_cup cup_sublist,
  have qr_in_cap : [q, r] <+ cap, rw cap_eq, 
  from [q, r].sublist_append_left cap',
  have qr_in_s : [q, r] <+ s,
  from list.sublist.trans qr_in_cap cap_sublist,

  by_cases cpqr : c p q r,
  { left, existsi (p :: cap), 
    simp, split, rw cap_eq,
    have eq : p :: q :: r :: cap' = [p] ++ [q] ++ (r :: cap'), simp,
    rw eq, apply s.nodup_sublist_overlap; try { tauto },
    simp, rw ←cap_eq, tauto,
    rw cap_eq, simp, rw ←cap_eq, tauto },
  { right, existsi (cup ++ [r]), 
    simp, split, rw cup_eq, simp,
    have eq : cup' ++ [p, q, r] = (cup' ++ [p]) ++ [q] ++ [r], simp,
    rw eq, apply s.nodup_sublist_overlap; try { tauto },
    simp, rw ←cup_eq, tauto,
    rw cup_eq, simp, apply list.chain3'_append,
    rw ←cup_eq, tauto, tauto },
end

lemma diagonal_induction {P : ℕ → ℕ → Prop} 
  (hPa : ∀ b, 2 ≤ b → P 2 b) (hPb : ∀ a, 2 ≤ a → P a 2)
  (ih : ∀ a b, 2 ≤ a → 2 ≤ b → P a (b+1) → P (a+1) b → P (a+1) (b+1)) :
  ∀ a b, 2 ≤ a → 2 ≤ b → P a b :=
begin
  assume a b ha hb,
  revert hb,
  apply nat.le_induction,
  { from hPb a ha },
  { induction ha with c hc, 
    { assume p q r, 
      have h : 2 ≤ p+1 := le_add_right q, 
      from (hPa (p+1) h) },
    { have hn: ∀ (n : ℕ), 2 ≤ n → P c n,
      { assume n hn, induction hn with p hp,
        { from (hPb c) hc },
        { from ha_ih p hp hn_ih } },
      assume n hn2 hp, 
      have hq : P c (n+1) := hn (n+1) (le_add_right hn2), 
      from ih _ _ hc hn2 hq hp } }
end

lemma binom_eq' (a' b' : ℕ) :
  (a' + b' + 1).choose a' + 
  (a' + b' + 1).choose (a' + 1) = 
  (a' + b' + 2).choose (a' + 1) :=
rfl

lemma binom_eq {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : 
  (a + (b + 1) - 4).choose (a - 2) + 
  (a + 1 + b - 4).choose (a + 1 - 2) = 
  (a + 1 + (b + 1) - 4).choose (a + 1 - 2) :=
begin
  rw le_iff_exists_add at ha hb,
  rcases ha with ⟨a', rfl⟩,
  rcases hb with ⟨b', rfl⟩,
  convert binom_eq' a' b';
  ring_nf,
end

lemma find_size2_chain3' {r : α → α → α → Prop} {l: list α} (h: 2 ≤ l.length) : 
  ∃ (c : list α), c <+ l ∧ c.chain3' r ∧ 2 ≤ c.length :=
begin
  rcases (l.take_first2 h) with ⟨p, q, l', l_eq, l_first⟩,
  use [[p, q]], rw l_eq,
  refine ⟨_, _, _⟩; try { simp },
  from [p, q].sublist_append_left l',
end

theorem cap_cup
  {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) 
  (s : list α) (s_nodup : s.nodup) 
  (hs : nat.choose (a + b - 4) (a - 2) + 1 ≤ s.length) 
  (c : α → α → α → Prop) : 

  (∃ cap : list α, cap <+ s ∧ cap.chain3' c ∧ a ≤ cap.length) ∨
  (∃ cup : list α, cup <+ s ∧ cup.chain3' cᶜ ∧ b ≤ cup.length) := 
begin
  revert s,
  revert a b,
  refine diagonal_induction _ _ _,
  -- a = 2
  { intros b hb, simp, intros s hnd ht, 
    left, from find_size2_chain3' ht },
  -- b = 2
  { intros b hb, simp, intros s hnd ht,
    right, from find_size2_chain3' ht },
  -- main induction 
  { intros a b ha hb,
    have hsum := binom_eq ha hb,
    -- put back all the long numbers into symbols
    set n_a_sb: ℕ := (a + (b + 1) - 4).choose (a - 2),
    set n_sa_b: ℕ := (a + 1 + b - 4).choose (a + 1 - 2),
    set n_sa_sb: ℕ := (a + 1 + (b + 1) - 4).choose (a + 1 - 2),

    assume ih_a_sb ih_sa_b s s_nodup s_size,
    -- criterion for dividing the set `s` into two
    -- I want to make this decidable
    set start_of_cap: α → Prop := λ (p: α), 
      (∃ (cap: list α) (cap_not_nil: cap ≠ []), 
         cap <+ s ∧ a ≤ cap.length ∧ 
         cap.chain3' c ∧ 
         p = cap.first cap_not_nil) 
      with eq_start_of_cap,

    -- dividing `s` into sets `sa` and `sb` using `start_of_cap`
    have sa_sb_length := s.length_filter_filter start_of_cap,
    set sa := s.filter start_of_cap with eq_sa, 
    set sb := s.filter start_of_capᶜ with eq_sb,
    rw [←eq_sa, ←eq_sb] at sa_sb_length,
    have size_cases: n_sa_b + 1 ≤ sa.length ∨ 
      n_a_sb + 1 ≤ sb.length := by by_contra'; linarith,

    -- before dividing into cases, some utility lemmas
    have sa_nodup: sa.nodup, 
    rw eq_sa, from list.nodup.filter _ s_nodup,
    have sb_nodup: sb.nodup,
    rw eq_sb, from list.nodup.filter _ s_nodup,
    have sa_in_s: sa <+ s := list.filter_sublist s,
    have sb_in_s: sb <+ s := list.filter_sublist s,
    have lift_in_sa: ∀ {l : list α}, l <+ sa → l <+ s :=
      λ l h, list.sublist.trans h sa_in_s,
    have lift_in_sb: ∀ {l : list α}, l <+ sb → l <+ s :=
      λ l h, list.sublist.trans h sb_in_s,

    cases size_cases.symm with sb_large sa_large,
    -- case where sb is large is easier
    -- either find a-cap (contradicts def) or (b+1)-cup
    { have h_sb_cap_cup := ih_a_sb sb sb_nodup sb_large,
      rcases h_sb_cap_cup with 
        ⟨cap', ⟨cap'_in_sb, cap'_chain, cap'_len⟩⟩ | 
        ⟨cup', ⟨cup'_in_sb, cup'_chain, cup'_len⟩⟩,
      -- a-cap in sb
      { have cap'_not_nil : cap' ≠ [],
        from list.size2_not_nil (nat.le_trans ha cap'_len),
        have cap'_in_s := lift_in_sb cap'_in_sb,

        set p := cap'.first cap'_not_nil with eq_p,
        have hp : start_of_cap p, rw eq_start_of_cap,
        use [cap', cap'_not_nil]; repeat { split }; try { tauto },
        have p_in_cap' : p ∈ cap' := list.first_mem cap'_not_nil,
        have p_in_sb : p ∈ sb := list.sublist.subset cap'_in_sb p_in_cap',
        rw [eq_sb, list.mem_filter] at p_in_sb,
        cases p_in_sb, contradiction },
      -- (b+1)-cup in sb
      { right, use cup', 
        have h := lift_in_sb cup'_in_sb, tauto } },

    -- case when sa is large
    -- find (a+1)-cap or b-cup
    have h_sa_cap_cup := ih_sa_b sa sa_nodup sa_large,
    rcases h_sa_cap_cup with 
      ⟨cap', ⟨cap'_in_sa, cap'_chain, cap'_len⟩⟩ | 
      ⟨cup, ⟨cup_in_sa, cup_chain, cup_len⟩⟩,
    -- (a+1)-cap in sa is easy
    { left, use cap', 
      have h := lift_in_sa cap'_in_sa, tauto },
    -- main case b-cup in sa
    clear ih_a_sb ih_sa_b,
    -- rudimentary facts
    have cup_not_nil : cup ≠ [] :=
      list.size2_not_nil (nat.le_trans hb cup_len),
    have cup_in_s : cup <+ s := lift_in_sa cup_in_sa,
    have p_in_cup := list.last_mem cup_not_nil,
    -- take the last point `p` of `cup`
    set p := cup.last cup_not_nil with eq_p_cap_last,
    -- ...and as it is in `sa` it is the start of another `cap`
    have p_in_sa := list.sublist.subset cup_in_sa p_in_cup,
    rw [eq_sa, list.mem_filter] at p_in_sa,
    cases p_in_sa with _ hp,
    rw eq_start_of_cap at hp,
    rcases hp with ⟨cap, cap_not_nil, 
      ⟨cap_in_s, cap_len, cap_chain, eq_p⟩⟩,
    rw eq_p_cap_last at eq_p,
    -- invoke the main lemma that enlarges a cap or a cup sharing the endpoints
    have cap_cup_ext :=
      cap_cup_extension 
        s_nodup cap_in_s cap_chain (nat.le_trans ha cap_len)
          cup_in_s cup_chain (nat.le_trans hb cup_len)
          eq_p,
    -- clean up and match the goal
    cases cap_cup_ext with cap_ext cup_ext,
    { rcases cap_ext with ⟨cape, ⟨cape_in_s, cape_chain, cape_len⟩⟩,
      left, use cape, refine ⟨_, _, _⟩; try { tauto }, linarith },
    { rcases cup_ext with ⟨cupe, ⟨cupe_in_s, cupe_chain, cupe_len⟩⟩,
      right, use cupe, refine ⟨_, _, _⟩; try { tauto }, linarith },
  }
end