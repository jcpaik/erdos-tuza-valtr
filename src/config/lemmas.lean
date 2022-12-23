import config.defs

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