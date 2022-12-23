import tactic.linarith

import config.defs

variables {α : Type*} [linear_order α] (C : config α)

@[simp] theorem ncap_nil : C.ncap 0 [] := 
  by rw [config.ncap, config.cap]; tauto

@[simp] theorem cap_singleton (a : α) : C.cap 1 [a] := by rw config.cap; simp

@[simp] theorem cap_pair {a b : α} : C.cap 2 [a, b] ↔ a < b := by rw config.cap; simp; tauto

@[simp] theorem cap_cons {n : ℕ} {a b c : α} {l : list α} : 
  C.cap (n+1) (a :: b :: c :: l) ↔ a < b ∧ C.cap3 a b c ∧ C.cap n (b :: c :: l) := 
by rw config.cap; rw config.cap; simp; tauto

@[simp] theorem cap_append_cons3 {n : ℕ} {a b c : α} {l1 l2 : list α} :
  C.cap (n + l2.length + 1) (l1 ++ a :: b :: c :: l2) ↔ 
    C.cap n (l1 ++ [a, b]) ∧ 
    C.cap3 a b c ∧
    C.cap (l2.length + 2) (b :: c :: l2) :=
begin
  induction l1 with d l1,
  { simp [config.cap]; tauto, },
end