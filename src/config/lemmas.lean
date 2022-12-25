import tactic.linarith

import config.defs

namespace config

variables {α : Type*} [linear_order α] (C : config α)

@[simp] theorem cap_nil : C.cap [] := 
  by rw config.cap; tauto

@[simp] theorem cap_singleton (a : α) : C.cap [a] := 
  by rw config.cap; simp

@[simp] theorem cap_pair {a b : α} : C.cap [a, b] ↔ a < b := 
  by rw config.cap; simp; tauto

@[simp] theorem cap_cons3 {a b c : α} {l : list α} : 
  C.cap (a :: b :: c :: l) ↔ 
  a < b ∧ C.cap3 a b c ∧ C.cap (b :: c :: l) := 
by repeat {rw config.cap}; simp; tauto

@[simp] theorem cap_append_cons3 {a b c : α} {l1 l2 : list α} :
  C.cap (l1 ++ a :: b :: c :: l2) ↔ 
    C.cap (l1 ++ [a, b]) ∧ C.cap3 a b c ∧ C.cap (b :: c :: l2) :=
begin
  induction l1 with d l1,
  {simp [config.cap]; tauto},
  cases l1 with e l1, 
  {simp [config.cap]; tauto},
  cases l1 with f l1,
  {simp [config.cap]; tauto},
  simp, simp at l1_ih, rw l1_ih, tauto,
end

theorem cap_init {l : list α} (h : C.cap l) : C.cap l.init :=
begin
  induction l with a l,
  {simp [config.cap]; tauto},
  cases l with b l, 
  {simp [config.cap]; tauto},
  cases l with c l,
  {simp [config.cap, list.init] at *},
  cases l with d l,
  {simp [config.cap, list.init] at *, tauto},
  simp [list.init] at *, tauto,
end

theorem cap_tail {l : list α} (h : C.cap l) : C.cap l.tail :=
begin
  induction l with a l,
  {simp [config.cap]; tauto},
  cases l with b l, 
  {simp [config.cap]; tauto},
  cases l with c l,
  {simp [config.cap] at *},
  cases l with d l,
  {simp [config.cap] at *, tauto},
  simp [list.init] at *, tauto,
end

def cap_take_head2 : ∀ {l : list α}, 2 ≤ l.length →
  Σ' (h1 h2 : α) (t : list α), l = h1 :: h2 :: t
| [] h := absurd h (of_to_bool_ff rfl)
| [a] h := absurd h (of_to_bool_ff rfl)
| (a :: b :: t) _ := ⟨a, b, t, rfl⟩

def cap_take_head3 : ∀ {l : list α}, 3 ≤ l.length →
  Σ' (h1 h2 h3 : α) (t : list α), l = h1 :: h2 :: h3 :: t
| [] h := absurd h (of_to_bool_ff rfl) 
| [a] h := absurd h (of_to_bool_ff rfl)
| [a, b] h := absurd h (of_to_bool_ff rfl)
| (a :: b :: c :: t) _ := ⟨a, b, c, t, rfl⟩

@[simp] theorem cup_nil : C.cup [] := 
  by rw config.cup; tauto

@[simp] theorem cup_singleton (a : α) : C.cup [a] := 
  by rw config.cup; simp

@[simp] theorem cup_pair {a b : α} : C.cup [a, b] ↔ a < b := 
  by rw config.cup; simp; tauto

@[simp] theorem cup_cons3 {a b c : α} {l : list α} : 
  C.cup (a :: b :: c :: l) ↔ 
  a < b ∧ C.cup3 a b c ∧ C.cup (b :: c :: l) := 
by repeat {rw config.cup}; simp; tauto

@[simp] theorem cup_append_cons3 {a b c : α} {l1 l2 : list α} :
  C.cup (l1 ++ a :: b :: c :: l2) ↔ 
    C.cup (l1 ++ [a, b]) ∧ C.cup3 a b c ∧ C.cup (b :: c :: l2) :=
begin
  induction l1 with d l1,
  {simp [config.cup]; tauto},
  cases l1 with e l1, 
  {simp [config.cup]; tauto},
  cases l1 with f l1,
  {simp [config.cup]; tauto},
  simp, simp at l1_ih, rw l1_ih, tauto,
end 

theorem cup_init {l : list α} (h : C.cup l) : C.cup l.init :=
begin
  induction l with a l,
  {simp [config.cup]; tauto},
  cases l with b l, 
  {simp [config.cup]; tauto},
  cases l with c l,
  {simp [config.cup, list.init] at *},
  cases l with d l,
  {simp [config.cup, list.init] at *, tauto},
  simp [list.init] at *, tauto,
end

theorem cup_tail {l : list α} (h : C.cup l) : C.cup l.tail :=
begin
  cases l with a l,
  {simp [config.cup]; tauto},
  cases l with b l, 
  {simp [config.cup]; tauto},
  cases l with c l,
  {simp [config.cup] at *},
  cases l with d l,
  {simp [config.cup] at *, tauto},
  simp [list.init] at *, tauto,
end

theorem cup_head'_lt_last' (p q : α) {l : list α} (l_cup : C.cup l) 
  (hl : 2 ≤ l.length) (hp : p ∈ l.head') (hq : q ∈ l.last') : p < q :=
begin
  cases l with p l,
  {simp at hp, exfalso, tauto},
  simp at hp, subst hp,
  have l_nnil : l ≠ [] := by 
    intro h; subst h; simp at hl; exact nat.lt_asymm hl hl,
  rcases list.take_last l_nnil with ⟨q, l', eq_l⟩,
  rw eq_l at hq, simp at hq, subst hq,
  rw [config.cup, eq_l] at l_cup,
  cases l_cup with l_sorted _,
  rw list.chain'_iff_pairwise at l_sorted, simp at l_sorted,
  have h' := l_sorted.left q, tauto,
end

theorem ncup_is_ngon {n : ℕ} {S : finset α} 
  (hn : 2 ≤ n) (h : C.has_ncup n S) : C.has_ngon n S :=
begin
  rcases h with ⟨c, ⟨⟨c_cup, c_length⟩, c_in_S⟩⟩,
  have hc : c ≠ [] := 
    by cases c; subst c_length; simp at hn; tauto,
  rcases list.take_last hc with ⟨y, c, eq_c⟩, subst eq_c,
  have hc : c ≠ [] :=
    by intro h; subst c_length; subst h; simp at hn; exact nat.lt_asymm hn hn,
  rcases list.take_head hc with ⟨x, c, eq_c⟩, subst eq_c,
  clear hc hc,

  use [[x, y], x :: c ++ [y]],
  refine ⟨_, _, _⟩; try {simp; simp at c_in_S; tauto},
  rw [config.ngon, config.gon], simp,
  have hxy : x < y := begin
    apply C.cup_head'_lt_last' x y c_cup,
    simp, exact inf_eq_left.mp rfl, simp, simp,
  end,
  simp at c_length, rw c_length, split, tauto, linarith,
end

end config