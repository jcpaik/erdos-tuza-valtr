import tactic.linarith

import config.defs

variables {α : Type*} [linear_order α] {C : config α}

namespace config

namespace cap

@[simp] protected theorem nil : C.cap [] := 
  by rw config.cap; tauto

@[simp] protected theorem singleton (a : α) : C.cap [a] := 
  by rw config.cap; simp

@[simp] protected theorem pair {a b : α} : C.cap [a, b] ↔ a < b := 
  by rw config.cap; simp; tauto

@[simp] protected theorem cons3 {a b c : α} {l : list α} : 
  C.cap (a :: b :: c :: l) ↔ 
  a < b ∧ C.cap3 a b c ∧ C.cap (b :: c :: l) := 
by repeat {rw config.cap}; simp; tauto

@[simp] protected theorem append_cons3 {a b c : α} {l1 l2 : list α} :
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

protected theorem init {l : list α} (h : C.cap l) : C.cap l.init :=
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

protected theorem tail {l : list α} (h : C.cap l) : C.cap l.tail :=
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

end cap

namespace ncap

protected theorem init {n : ℕ} {l : list α} (h : C.ncap (n+1) l) : C.ncap n l.init :=
begin
  cases l with a l,
  { simp [config.ncap, config.cap] at h, cases h },
  simp [config.ncap] at *, cases h with hc hl,
  split, exact hc.init, assumption,
end

protected theorem tail {n : ℕ} {l : list α} (h : C.ncap (n+1) l) : C.ncap n l.tail :=
begin
  cases l with a l,
  { simp [config.ncap, config.cap] at h, cases h },
  simp [config.ncap] at *, cases h with hc hl,
  split, exact hc.tail, assumption,
end

end ncap

namespace cup

@[simp] protected theorem nil : C.cup [] := 
  by rw config.cup; tauto

@[simp] protected theorem singleton (a : α) : C.cup [a] := 
  by rw config.cup; simp

@[simp] protected theorem pair {a b : α} : C.cup [a, b] ↔ a < b := 
  by rw config.cup; simp; tauto

@[simp] protected theorem cons3 {a b c : α} {l : list α} : 
  C.cup (a :: b :: c :: l) ↔ 
  a < b ∧ C.cup3 a b c ∧ C.cup (b :: c :: l) := 
by repeat {rw config.cup}; simp; tauto

@[simp] protected theorem append_cons3 {a b c : α} {l1 l2 : list α} :
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

protected theorem init {l : list α} (h : C.cup l) : C.cup l.init :=
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

protected theorem tail {l : list α} (h : C.cup l) : C.cup l.tail :=
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

theorem head'_lt_last' 
  {l : list α} (l_cup : C.cup l) (p q : α) 
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

end cup

namespace ncup

@[simp] protected theorem nil : C.ncup 0 [] := 
  by rw [config.ncup, config.cup]; tauto

@[simp] protected theorem singleton (a : α) : C.ncup 1 [a] := 
  by rw [config.ncup, config.cup]; simp

@[simp] protected theorem pair {a b : α} : C.ncup 2 [a, b] ↔ a < b := 
  by rw [config.ncup, config.cup]; simp; tauto

@[simp] protected theorem cons3 {n : ℕ} {a b c : α} {l : list α} : 
  C.ncup (n + 1) (a :: b :: c :: l) ↔ 
  a < b ∧ C.cup3 a b c ∧ C.ncup n (b :: c :: l) := 
by repeat {rw [config.ncup, config.cup]}; simp; tauto

protected theorem init {n : ℕ} {l : list α}
  (h : C.ncup (n+1) l) : C.ncup n l.init :=
begin
  cases l with a l,
  { simp [config.ncup, config.cup] at h, cases h },
  simp [config.ncup] at *, cases h with hc hl,
  split, exact hc.init, assumption,
end

protected theorem tail {n : ℕ} {l : list α}
  (h : C.ncup (n+1) l) : C.ncup n l.tail :=
begin
  cases l with a l,
  { simp [config.ncup, config.cup] at h, cases h },
  simp at *, cases h with hc hl,
  split, exact hc.tail, simp at hl, assumption,
end

theorem head'_lt_last' (p q : α) {n : ℕ} {l : list α} 
  (l_ncup : C.ncup n l) 
  (hl : 2 ≤ l.length) (hp : p ∈ l.head') (hq : q ∈ l.last') : p < q :=
begin
  cases l_ncup with l_cup _,
  apply l_cup.head'_lt_last' p q; assumption,
end

end ncup

end config

theorem ncup_is_ngon {n : ℕ} {S : finset α} 
  (hn : 2 ≤ n) (h : C.has_ncup n S) : C.has_ngon n S :=
begin
  rcases h with ⟨c, c_in_S, ⟨c_cup, c_length⟩⟩,
  have hc : c ≠ [] := 
    by cases c; subst c_length; simp at hn; tauto,
  rcases list.take_last hc with ⟨y, c, eq_c⟩, subst eq_c,
  have hc : c ≠ [] :=
    by intro h; subst c_length; subst h; simp at hn; exact nat.lt_asymm hn hn,
  rcases list.take_head hc with ⟨x, c, eq_c⟩, subst eq_c,
  clear hc hc,

  existsi [[x, y], _, x :: c ++ [y], _],
  rw [config.ngon, config.gon], simp,
  have hxy : x < y :=
    by apply c_cup.head'_lt_last' x y; simp; dec_trivial,
  simp at c_length, rw c_length, split, tauto, linarith,

  assumption, simp, simp at c_in_S, tauto,
end