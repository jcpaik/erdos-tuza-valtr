-- a self-contained practice sketch of the erdos-szekeres theorem
-- uses `linear_order` to give ordering to cap/cup

import tactic.basic
import data.fintype.basic
import data.finset
import data.finset.basic
import data.finset.sort
import data.list
import logic.nontrivial
import tactic.omega

-- I don't know how to distinguish Prop and bool
open_locale classical
noncomputable theory

variables {α : Type*} [linear_order α]
class configuration (α : Type*) :=
  (color : α → α → α → bool)
variables [configuration α]

def is_chain' (r : α → α → α → Prop) : ∀ (l : list α), Prop
| [] := true
| [x] := true
| [x, y] := true
| (x :: y :: z :: xs) := r x y z ∧ is_chain' (y :: z :: xs)

example {a b c d e : α} (r : α → α → α → Prop) :
  is_chain' r [a, b, c, d, e] ↔ r a b c ∧ r b c d ∧ r c d e :=
by simp [is_chain']

def is_chain (r : α → α → α → Prop) (s : list α) := is_chain' r s ∧ s.sorted (<)

lemma diagonal_induction {P : ℕ → ℕ → Prop} (hPa : ∀ b, 2 ≤ b → P 2 b) (hPb : ∀ a, 2 ≤ a → P a 2)
  (ih : ∀ a b, 2 ≤ a → 2 ≤ b → P a (b+1) → P (a+1) b → P (a+1) (b+1)) :
  ∀ a b, 2 ≤ a → 2 ≤ b → P a b :=
begin
  intros a b ha hb,
  revert hb,
  apply nat.le_induction,
  { exact hPb a ha },
  { induction ha with c hc, 
    { intros p q r, have h : 2 ≤ p+1 := le_add_right q, exact (hPa (p+1) h), },
    { have hn: ∀ (n : ℕ), 2 ≤ n → P c n,
      { intros n hn, induction hn with p hp,
        { apply (hPb c), exact hc },
        { apply ha_ih, exact hp, exact hn_ih } },
      intros n hn2 hp, 
      have hq : P c (n+1) := hn (n+1) (le_add_right hn2), 
      exact ih _ _ hc hn2 hq hp } }
end

theorem first_two {r : α → α → α → Prop} (l: list α) (h: 2 ≤ l.length) (hnd: l.nodup) : 
  ∃ (c : list α), c ⊆ l ∧ c.length = 2 ∧ is_chain r c :=
begin
  cases l, 
  case nil { simp at h, tauto },
  case cons : a l {
    cases l, 
    case nil { simp at h, 
    have nh: ¬(2 ≤ 1), exact (1: ℕ).not_succ_le_self,
    contradiction },
    case cons : b l {
      have hab: a ≠ b, intro heab, rw heab at hnd, simp at hnd, tauto,
      cases lt_or_gt_of_ne hab with halb hbla,
      { use ([a, b]: list α), 
        refine ⟨_, _, _⟩,
        simp, simp, simp [is_chain, is_chain', halb] },
      { use ([b, a]: list α), 
        refine ⟨_, _, _⟩,
        simp, simp, simp [is_chain, is_chain'], exact hbla }
    }
  }
end

theorem first_two' {r : α → α → α → Prop} (l: list α) (h: 2 ≤ l.length) (hnd: l.nodup) : 
  ∃ (c : list α), c ⊆ l ∧ 2 ≤ c.length ∧ is_chain r c :=
begin
  rcases (first_two l h hnd) with ⟨c, ⟨hc0, hc1, hc2⟩⟩,
  use c, refine ⟨_, _, _⟩,
  tauto, exact eq.ge hc1, tauto
end

theorem off2 (a: ℕ) (ha: 2 ≤ a): ∃b, a = b + 2 := 
begin
  use (a - 2),
  omega
end

theorem some_eq (a b: ℕ) (ha: 2 ≤ a) (hb: 2 ≤ b): 
  (a + (b + 1) - 4).choose (a - 2) + 
  (a + 1 + b - 4).choose (a + 1 - 2) = 
  (a + 1 + (b + 1) - 4).choose (a + 1 - 2) :=
begin
  cases (off2 a ha) with a' ea, rw ea,
  cases (off2 b hb) with b' eb, rw eb,
  repeat {rw ←add_assoc}, simp,
  have eq1: a' + 2 + 1 + b' - 2 = a' + b' + 1 := by omega, rw eq1, 
  have eq2: a' + 1 + b' = a' + b' + 1 := by omega, rw eq2,
  have eq3: a' + 2 + b' = a' + b' + 2 := by omega, rw eq3,
  tauto
end

theorem partition_length {α: Type*} (l: list α) (p: α → Prop) :
  (list.filter p l).length + (list.filter (not ∘ p) l).length = l.length :=
begin
  induction l,
  case nil { simp, },
  case cons : h l ih {
    by_cases x : (p h); simp [list.filter, x],
    omega, omega
  }
end

@[simp] def list.first {α: Type*} : ∀ (l: list α), l ≠ [] → α
| [] := λ h, absurd rfl h
| (a :: l) := λ _, a

lemma list.first_in_list (l: list α) (h: l ≠ []) : (l.first h ∈ l) :=
begin
  cases l with a l,
  exact h rfl, simp,
end

@[simp] def list.first2 {α: Type*} : ∀ (l: list α), 2 ≤ l.length → α × α
| [] := λ h, absurd h (1: ℕ).not_lt_zero
| [p] := λ h,absurd h (1 : ℕ).not_succ_le_self 
| (p :: q :: l') := λ _, (p, q)

@[simp] def list.last2 {α: Type*} : ∀ (l: list α), 2 ≤ l.length → α × α
| [] := λ h, absurd h (1: ℕ).not_lt_zero
| [p] := λ h,absurd h (1 : ℕ).not_succ_le_self 
| [p, q] := λ _, (p, q)
| (p :: q :: r :: l') := λ _, 
    let h: 2 ≤ (q :: r :: l').length := begin simp, omega end in 
    (q :: r :: l').last2 h

theorem list.size2_nonempty {α: Type*} : ∀ (l : list α), 2 ≤ l.length → l ≠ []
| [] := λ h, begin simp at h, exfalso, tauto end
| (a :: l) := λ _ h, begin simp at h, tauto end

theorem list.take_first2 {α: Type*} : 
  ∀ (l: list α) (hl: 2 ≤ l.length),
  ∃ (p q: α) (l': list α), 
    l.first2 hl = (p, q) ∧ 
    l = p :: q :: l' ∧ 
    p = (l.first (l.size2_nonempty hl))
| [] := λ h, absurd h (1: ℕ).not_lt_zero
| [p] := λ h, absurd h (1 : ℕ).not_succ_le_self
| (p :: q :: l') := λ _, by {existsi [p, q, l'], simp}

theorem list.take_last2 {α: Type*} :
  ∀ (l: list α) (hl: 2 ≤ l.length),
  ∃ (p q: α) (l': list α), 
    l.last2 hl = (p, q) ∧
    l = l' ++ [p, q] ∧ 
    q = (l.last (l.size2_nonempty hl))
| [] := λ h, absurd h (1: ℕ).not_lt_zero
| [p] := λ h, absurd h (1 : ℕ).not_succ_le_self
| [p, q] := λ _, ⟨p, q, [], by simp⟩
| (p :: q :: r :: rest') := λ _, 
  begin 
    set rest := q :: r :: rest' with def_rest,
    have h_rest : 2 ≤ rest.length := by {simp, exact le_add_self},
    rcases rest.take_last2 h_rest with ⟨l2, l1, l', ⟨eq_ih, x, y⟩⟩,
    existsi [l2, l1, p :: l'],
    simp, split; tauto,
  end

lemma chain_first2 
  {a b: α} {l : list α} {hl: 2 ≤ l.length} {c: α → α → α → Prop}
  (h_first2: l.first2 hl = (a, b)) (h_chain: is_chain c l) : 
  a < b :=
begin
  cases l with a' l' hl,
  simp at hl, tauto,
  cases l' with b' l'' hl',
  simp at hl, exfalso, exact (1 : ℕ).not_succ_le_self hl,
  simp at h_first2, cases h_first2 with ha hb, subst ha, subst hb,
  have h := h_chain.right, simp at h, tauto,
end

lemma chain_last2 
  {a b: α} {l : list α} {hl: 2 ≤ l.length} {c: α → α → α → Prop}
  (h_last2: l.last2 hl = (a, b)) (h_chain: is_chain c l) : 
  a < b :=
begin
  rcases l.take_last2 hl with ⟨a', b', l', ab_eq, l_eq, _⟩,
  rw h_last2 at ab_eq, cases ab_eq, 
  have h_inc := h_chain.right,
  have h: [a, b] <+ l := by {rw l_eq, simp},
  have q := list.pairwise.sublist h h_inc, simp at q, tauto,
end

lemma first_is_max (l : list α) (l_nonempty : l ≠ []) (h: list.sorted (<) l) 
  (b : α) (b_in_l: b ∈ l) :
  l.first l_nonempty ≤ b := 
begin
  induction l,
  simp at b_in_l, tauto,
  simp, simp at h, 
  have h' := h.left b,
  simp at b_in_l, cases b_in_l,
  { rw b_in_l, },
  { exact le_of_lt (h' b_in_l) },
end

lemma incseq_extend_first 
  (a : α) (l : list α) (l_nonempty : l ≠ [])
  (h: a < l.first l_nonempty) (hlist : l.sorted (<)) : 
  (a :: l).sorted (<) :=
begin
  simp, split,
  intros b b_in_l,
  have h' := first_is_max l l_nonempty hlist b b_in_l,
  exact gt_of_ge_of_gt h' h,
  tauto,
end

lemma chain_extend_first
  {c: α → α → α → Prop}
  {p q r : α} {cap : list α}
  (h_pair : p < q) (h_triple : c p q r)
  (h_chain : is_chain c (q :: r :: cap)) : 
  is_chain c (p :: q :: r :: cap) := 
begin
  split,
  rw is_chain', cases h_chain, tauto,
  cases h_chain with _ h_chain,
  refine (incseq_extend_first p (q :: r :: cap) _ h_pair h_chain),
  simp,
end

lemma chain'_extend_last
  {c: α → α → α → Prop}
  {p q r : α} {cap : list α}
  (h_pair : q < r) (h_triple : c p q r)
  (h_chain : is_chain' c (cap ++ [p, q])) : 
  is_chain' c (cap ++ [p, q, r]) := 
begin
  induction cap with t cap ih,
  split; tauto,
  cases cap with u cap,
  simp [is_chain'] at *; tauto,
  cases cap with v cap,
  simp [is_chain'] at *; tauto,
  simp [is_chain'] at *, split; tauto,
end

lemma chain_extend_last
  {c: α → α → α → Prop}
  {p q r : α} {cap : list α}
  (h_pair : q < r) (h_triple : c p q r)
  (h_chain : is_chain c (cap ++ [p, q])) : 
  is_chain c (cap ++ [p, q, r]) := 
begin
  split, 
  have h_chain' := h_chain.left,
  apply chain'_extend_last; tauto,
  have h_sorted := h_chain.right,
  have h_pairwise: (cap ++ [p, q] ++ [r]).pairwise (<),
  rw ←list.chain'_iff_pairwise,
  apply list.chain'.append_overlap; try {tauto},
  rw list.chain'_iff_pairwise, tauto,
  simp; try { tauto },
  have h: [p, q] <+ cap ++ [p, q] := by simp,
  have h2 := list.pairwise.sublist h h_sorted, simp at h2, tauto,
  simp at h_pairwise, tauto,
end

theorem cap_cup_extension
  {s: list α} {c: α → α → α → Prop}
  {cap : list α} (hcap_subset : cap ⊆ s) (hcap_chain: is_chain c cap) {hcap_size2: 2 ≤ cap.length}
  {cup : list α} (hcup_subset : cup ⊆ s) (hcup_chain: is_chain cᶜ cup) {hcup_size2: 2 ≤ cup.length}
  (h : cup.last (cup.size2_nonempty hcup_size2) = 
       cap.first (cap.size2_nonempty hcap_size2) ) :
  
  (∃ cape : list α, cape ⊆ s ∧ is_chain c cape ∧ cape.length = cap.length + 1) ∨
  (∃ cupe : list α, cupe ⊆ s ∧ is_chain cᶜ cupe ∧ cupe.length = cup.length + 1) :=
begin
  rcases cap.take_first2 hcap_size2 with ⟨q', r, cap', ⟨cap_f2, cap_eq, hq'_first⟩⟩,
  rcases cup.take_last2 hcup_size2 with ⟨p, q, cup', ⟨cup_f2, cup_eq, hq_last⟩⟩,
  rw [←hq_last, ←hq'_first] at h, subst h,
  have p_in_s : p ∈ s := begin
    have p_in_cup : p ∈ cup, rw cup_eq, simp,
    exact hcup_subset p_in_cup,
  end,
  have q_in_s : q ∈ s := begin
    have q_in_cup : q ∈ cup, rw cup_eq, simp,
    exact hcup_subset q_in_cup,
  end,
  have r_in_s : r ∈ s := begin
    have r_in_cap : r ∈ cap, rw cap_eq, simp,
    exact hcap_subset r_in_cap,
  end,
  by_cases triple : c p q r,
  { left, existsi (p :: cap), simp, split, tauto, 
    rw cap_eq, apply chain_extend_first; try { tauto },
    exact chain_last2 cup_f2 hcup_chain, rw ←cap_eq, tauto },
  { right, existsi (cup ++ [r]), simp, split, tauto,
    rw cup_eq, simp, apply chain_extend_last; try { tauto },
    exact chain_first2 cap_f2 hcap_chain, rw ←cup_eq, tauto },
end

theorem cap_cup
  {a b : ℕ} (ha: 2 ≤ a) (hb: 2 ≤ b) 
  (s: list α) (hnd: s.nodup) (hs : nat.choose (a + b - 4) (a - 2) + 1 ≤ s.length) 
  (c: α → α → α → Prop) : 

  (∃ cap : list α, cap ⊆ s ∧ a ≤ cap.length ∧ is_chain c cap) ∨
  (∃ cup : list α, cup ⊆ s ∧ b ≤ cup.length ∧ is_chain cᶜ cup) := 
begin
  revert s,
  revert a b,
  refine diagonal_induction _ _ _,
  { intros b hb, simp, intros s hnd ht, 
    left, exact (first_two' s ht hnd) },
  { intros b hb, simp, intros s hnd ht,
    right, exact (first_two' s ht hnd) },
  { intros a b ha hb,
    set nab1: ℕ := (a + (b + 1) - 4).choose (a - 2) with hnab1,
    set na1b: ℕ := (a + 1 + b - 4).choose (a + 1 - 2) with hna1b,
    set na1b1: ℕ := (a + 1 + (b + 1) - 4).choose (a + 1 - 2) with hna1b1,
    have hsum: nab1 + na1b = na1b1,
    rw hnab1, rw hna1b, rw hna1b1, apply (some_eq a b ha hb),
    rw ←hsum,
    intros hab1 ha1b s s_nd hsz,
    -- Is this decidable? That's why we use the sin
    set start_of_cap: α → Prop := λ (p: α), 
      (∃ (scap: list α) (scap_nonzero: scap ≠ []), 
         scap ⊆ s ∧ a ≤ scap.length ∧ 
         is_chain c scap ∧ 
         p = scap.first scap_nonzero) 
      with h_start_of_cap,
    set spart := list.partition start_of_cap s with h_spart,
    simp at h_spart,
    set sa := spart.fst with h_sa, rw h_spart at h_sa, simp at h_sa,
    set sb := spart.snd with h_sb, rw h_spart at h_sb, simp at h_sb,
    have hssum: sa.length + sb.length = s.length,
    rw [h_sa, h_sb],
    exact partition_length _ _,
    have hineq: na1b + 1 ≤ sa.length ∨ nab1 + 1 ≤ sb.length := by omega,
    have sa_nd: sa.nodup := 
      by {rw h_sa, exact list.nodup.filter start_of_cap s_nd},
    have sb_nd: sb.nodup := 
      by {rw h_sb, exact list.nodup.filter (not ∘ start_of_cap) s_nd},
    have la: ∀ l : list α, l ⊆ sa → l ⊆ s := 
      by {rw h_sa, intros l h0, 
        have h1 := list.filter_subset s,
        exact list.subset.trans h0 h1 },
    have lb: ∀ l : list α, l ⊆ sb → l ⊆ s :=
      by {rw h_sb, intros l h0, 
        have h1 := list.filter_subset s,
        exact list.subset.trans h0 h1 },
    cases hineq,
    {
      have hmain := ha1b sa sa_nd hineq,
      cases hmain,
      { -- could be refactored? yes.
        cases hmain with scap hmain,
        left, use scap, exact and.imp_left (la scap) hmain,
      },
      {
        rcases hmain with ⟨scup, ⟨scup_in_sa, ⟨scup_len, scup_chain⟩⟩⟩,
        have scup_not_nil : scup ≠ [] := 
          begin 
            intro scup_empty, 
            simp [scup_empty] at scup_len, 
            simp [scup_len] at hb, tauto
          end,
        set p: α := scup.last scup_not_nil with hp,
        have hmainp: start_of_cap p := begin
          have p_in_scup := list.last_mem scup_not_nil,
          rw ←hp at p_in_scup,
          have p_in_sa := scup_in_sa p_in_scup,
          simp [h_sa] at p_in_sa,
          exact p_in_sa.right
        end,
        rw h_start_of_cap at hmainp,
        rcases hmainp with ⟨scap, _, ⟨scap_in_s, scap_len, scap_chain, hp_other⟩⟩,
        have hext := cap_cup_extension scap_in_s scap_chain (la scup scup_in_sa) scup_chain _,
        cases hext,
        { rcases hext with ⟨cap, ⟨cap_in_s, cap_is_chain, cap_len⟩⟩,
          left, existsi cap, refine ⟨_, _, _⟩; try { tauto }, omega },
        { rcases hext with ⟨cup, ⟨cup_in_s, cup_is_chain, cup_len⟩⟩,
          right, existsi cup, refine ⟨_, _, _⟩; try { tauto }, omega },
        omega, omega, rw hp at hp_other,
        exact hp_other,
      },
    },
    {
      have hmain := hab1 sb sb_nd hineq,
      cases hmain,
      {
        rcases hmain with ⟨scap, ⟨scap_in_sb, scap_len, scap_is_chain⟩⟩,
        have scap_nonempty: scap ≠ [],
        intro cont, subst cont, simp at scap_len, subst scap_len, 
        exact (1: ℕ).not_lt_zero ha,
        have p_in_scap := scap.first_in_list scap_nonempty,
        set p := scap.first scap_nonempty with p_is_first,
        have p_in_sb := scap_in_sb p_in_scap,
        rw h_sb at p_in_sb, rw list.mem_filter at p_in_sb,
        have hnmainp: ¬ (start_of_cap p) := p_in_sb.right,
        have hmainp: start_of_cap p, rw h_start_of_cap,
        existsi [scap, scap_nonempty],
        refine ⟨_, _, _, _⟩; try {tauto},
        exfalso, exact hnmainp hmainp,
      },
      {
        cases hmain with scup hmain,
        right, use scup, exact and.imp_left (lb scup) hmain,
      }
    },
  }
end