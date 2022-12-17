-- lemmas about 3-chain of lists, taking first/last two elements, etc.

import data.list

variables {α : Type*}

@[simp] def list.chain3' (R : α → α → α → Prop) : list α → Prop 
| [] := true
| [x] := true
| [x, y] := true
| (x :: y :: z :: xs) := R x y z ∧ (y :: z :: xs).chain3'

example {a b c d e : α} (r : α → α → α → Prop) :
  [a, b, c, d, e].chain3' r ↔ r a b c ∧ r b c d ∧ r c d e :=
by simp

@[simp] def list.first : ∀ (l: list α), l ≠ [] → α
| [] := λ h, absurd rfl h
| (a :: l) := λ _, a

theorem list.first_mem : ∀ {l : list α} (h : l ≠ []), (l.first h ∈ l)
| [] h := absurd rfl h
| (a :: l) h := by simp

/-
@[simp] def list.first2 : ∀ (l: list α) (h : 2 ≤ l.length), α × α
| [] h := absurd h (of_to_bool_ff rfl)
| [p] h := absurd h (nat.lt_asymm h)
| (p :: q :: l') _ := (p, q)

@[simp] def list.last2 : ∀ (l: list α) (h : 2 ≤ l.length), α × α
| [] h := absurd h (of_to_bool_ff rfl)
| [p] h := absurd h (nat.lt_asymm h)
| [p, q] _ := (p, q)
| (p :: q :: r :: l') _ :=
    let h: 2 ≤ (q :: r :: l').length := le_add_self in
    (q :: r :: l').last2 h
-/

theorem list.size2_not_nil : ∀ {l : list α} (h : 2 ≤ l.length), l ≠ []
| [] h := absurd h (of_to_bool_ff rfl)
| (a :: l) _ := by simp

theorem list.take_first2 : 
  ∀ (l: list α) (hl: 2 ≤ l.length),
  ∃ (p q: α) (l': list α), 
    l = p :: q :: l' ∧ 
    (l.first (list.size2_not_nil hl)) = p
| [] := λ h, absurd h (of_to_bool_ff rfl)
| [p] := λ h, absurd h (nat.lt_asymm h)
| (p :: q :: l') := λ _, by {existsi [p, q, l'], simp}

theorem list.take_last2 :
  ∀ (l: list α) (hl: 2 ≤ l.length),
  ∃ (p q: α) (l': list α), 
    l = l' ++ [p, q] ∧ 
    (l.last (list.size2_not_nil hl)) = q
| [] := λ h, absurd h (of_to_bool_ff rfl)
| [p] := λ h, absurd h (nat.lt_asymm h)
| [p, q] := λ _, ⟨p, q, [], by simp⟩
| (p :: q :: r :: rest') := λ _, 
  begin 
    set rest := q :: r :: rest',
    have rest_size2 : 2 ≤ rest.length := by {simp, exact le_add_self},
    rcases rest.take_last2 rest_size2 with ⟨p', q', l', ih_eq, ih_last⟩,
    existsi [p', q', p :: l'],
    simp, split; tauto,
  end

lemma list.chain3'_append
  {l : list α} {R: α → α → α → Prop} {p q r : α} 
  (h_chain3 : (l ++ [p, q]).chain3' R) (h : R p q r) : 
  (l ++ [p, q, r]).chain3' R := 
begin
  induction l with t l ih,
  { simp, tauto, },
  { cases l with u l, simp at *, tauto,
    cases l with v l, simp at *, tauto,
    simp at *, tauto, },
end

theorem list.length_filter_filter 
  (l : list α) (p : α → Prop) [decidable_pred p] :
  (l.filter p).length + (l.filter pᶜ).length = l.length :=
begin
  induction l with a l ih, simp,
  by_cases h : (p a); simp [list.filter, h]; rw ←ih,
  from nat.succ_add _ _,
  from rfl,
end

theorem list.nodup_sublist_overlap
  (l l1 l2 l3 : list α)
  (hl : l.nodup) (l2_not_nil : l2 ≠ [])
  (h12 : l1 ++ l2 <+ l) (h23 : l2 ++ l3 <+ l) : 
  l1 ++ l2 ++ l3 <+ l :=
begin
  revert l1 l2 l3,

  induction l with a l ih_aux,
  { simp at *, tauto },
  simp at hl,
  cases hl with a_not_in_l l_nodup,
  have ih := @ih_aux l_nodup,
  clear ih_aux l_nodup,
  intros l1 l2 l3 l2_not_nil h12 h23,
    
  cases l1 with b l1, 
  { simp at *, from h23 },

  cases l2 with c l2,
  { simp at *, contradiction },

  cases h23 with _ _ _ hc23 _ _ _ h23,
  case cons2 {
    suffices a_in_l : a ∈ l, contradiction,
    cases h12 with _ _ _ hb12 _ _ _ h12',
    have h : a ∈ b :: (l1 ++ a :: l2), simp,
    from list.sublist.subset hb12 h,
    have h : a ∈ l1 ++ a :: l2, simp,
    from list.sublist.subset h12' h,
  },
  cases h12 with _ _ _ hb12 _ _ _ h12',
  apply list.sublist.cons,
  apply ih; try { tauto },
  apply list.sublist.cons2,
  apply ih; try { tauto },
end