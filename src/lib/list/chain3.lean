import lib.list.defs

variables {α : Type*} {R : α → α → α → Prop}

namespace list

theorem chain3_split {a b c d : α} {l1 l2 : list α} : 
  chain3 R a b (l1 ++ c :: d :: l2) ↔
  chain3 R a b (l1 ++ [c, d]) ∧ chain3 R c d l2 := 
by induction l1 with x l1 IH generalizing a b;
  simp only [*, nil_append, cons_append, chain3.nil, chain3_cons, and_true, and_assoc]

@[simp] theorem chain3_append_cons3 {a b c d e : α} {l1 l2 : list α} :
  chain3 R a b (l1 ++ c :: d :: e :: l2) ↔ 
  chain3 R a b (l1 ++ [c, d]) ∧ R c d e ∧ 
  chain3 R d e l2 := 
by rw [chain3_split, chain3_cons]

@[simp] theorem chain3'_nil : chain3' R [] := trivial

@[simp] theorem chain3'_singleton (a : α) : chain3' R [a] := trivial

@[simp] theorem chain3'_pair (a b : α) : chain3' R [a, b] := chain3.nil

@[simp] theorem chain3'_cons {x y z l} : 
  chain3' R (x :: y :: z :: l) ↔ R x y z ∧ chain3' R (y :: z :: l) := 
chain3_cons 

theorem chain3'_split {a b : α}: ∀ {l1 l2 : list α},
  chain3' R (l1 ++ a :: b :: l2) ↔
  chain3' R (l1 ++ [a, b]) ∧ chain3' R (a :: b :: l2)
| [] l2 := (and_iff_right (chain3'_pair a b)).symm
| [c] l2 := by simp -- todo
| (c :: d :: l1) l2 := chain3_split 

@[simp] theorem chain3'_append_cons3 {a b c : α} {l1 l2 : list α} :
  chain3' R (l1 ++ a :: b :: c :: l2) ↔
  chain3' R (l1 ++ [a, b]) ∧ R a b c ∧
  chain3' R (b :: c :: l2) :=
by rw [chain3'_split, chain3'_cons]

theorem chain3'.left_of_append {l1 l2 : list α}
  (h : chain3' R (l1 ++ l2)) : chain3' R l1 :=
begin
  induction l1 with a l1 ih, simp,
  cases l1 with b l1, simp,
  cases l1 with c l1, simp,
  simp at ⊢ h, tauto,
end

theorem chain3'.right_of_append {l1 l2 : list α}
  (h : chain3' R (l1 ++ l2)) : chain3' R l2 :=
begin
  revert l2,
  induction l1 with a l1 ih, intros l2 h', exact h',
  intros l2 h', 
  cases l1 with b l1,
  { cases l2 with c l2, simp,
    cases l2 with d l2, simp,
    simp at h', exact h'.right, },
  cases l1 with c l1,
  { cases l2 with d l2, simp,
    cases l2 with e l2, simp,
    simp at h', exact h'.right.right, },
  apply ih, simp at ⊢ h', exact h'.right,
end

theorem chain3'.infix {l₁ l : list α } 
  (h : chain3' R l) (h' : l₁ <:+: l) : chain3' R l₁ :=
by { rcases h' with ⟨l₂, l₃, rfl⟩, exact h.left_of_append.right_of_append }

theorem chain3'.suffix 
  {l₁ l : list α} (h : chain3' R l) (h' : l₁ <:+ l) : chain3' R l₁ := 
  h.infix h'.is_infix

theorem chain3'.prefix 
  {l₁ l : list α} (h : chain3' R l) (h' : l₁ <+: l) : chain3' R l₁ := 
  h.infix h'.is_infix

theorem chain3'.drop 
  {l : list α} (h : chain3' R l) (n : ℕ) : chain3' R (drop n l) := 
  h.suffix (drop_suffix _ _)

theorem chain3'.init 
  {l : list α} (h : chain3' R l) : chain3' R l.init := 
  h.prefix l.init_prefix

theorem chain3'.take 
  {l : list α} (h : chain3' R l) (n : ℕ) : chain3' R (take n l) := 
  h.prefix (take_prefix _ _)

theorem chain3'.tail 
  {l : list α} (h : chain3' R l) : chain3' R l.tail :=
begin
  cases l with a l, simp, 
  cases l with b l, simp,
  cases l with c l, simp,
  simp at ⊢ h, exact h.right,
end 

theorem chain3'_mirror [linear_order α] {l : list α} : 
  chain3' (mirror3 R) l.mirror ↔ chain3' R l :=
begin
  induction l with a l ih, simp,
  cases l with b l, simp,
  cases l with c l, 
  rw list.mirror, simp, 
  rw list.mirror, simp, 
  simp [list.mirror] at ih, rw ←ih,
  rw mirror3, simp, exact and.comm
end

end list