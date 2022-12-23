import config

variables {α : Type*} [linear_order α] (C : config α)

namespace config

def interweaved {n : ℕ} {c1 c2 : list α} 
  (h1 : C.ncup n c1) (h2 : C.ncup n c2) : Prop :=
  ∃ (p q r s : α), 
    p ∈ c1.head' ∧ r ∈ c1.last' ∧ q ∈ c2.head' ∧ s ∈ c2.last' ∧ 
    p < q ∧ q ≤ r ∧ r < s

def laced {n : ℕ} {c : list α} (h : C.ncup n c) : Prop :=
  ∃ (p q : α) (cp cq : list α), 
    p ∈ c.head' ∧ q ∈ c.last' ∧ 
    p ∈ cp.last' ∧ q ∈ cq.head' ∧ 
    cp.length + cq.length = n

def interweaved_laced {n : ℕ} {c1 c2 : list α} 
  (h1 : C.ncup n c1) (h2 : C.ncup n c2) : Prop :=
  C.interweaved h1 h2 ∧ C.laced h1 ∧ C.laced h2

end config