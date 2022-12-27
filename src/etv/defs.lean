import config

variables {α : Type*} [linear_order α] (C : config α)

namespace config

def has_laced (n : ℕ) (S : finset α) (p q : α) : Prop :=
  ∃ {a b : ℕ} {cp c cq : list α} 
    (hcp : C.ncup a cp) (hc : C.ncup n c) (hcQ : C.ncup b cq),
    (cp.in S ∧ c.in S ∧ cq.in S) ∧ a + b = n ∧ 
    (p ∈ cp.last' ∧ p ∈ c.head' ∧ q ∈ c.last' ∧ q ∈ cq.head')

def has_interweaved_laced
  (n : ℕ) (S : finset α) (p q r s : α) : Prop :=
  (p < q ∧ q ≤ r ∧ r < s) ∧
  (C.has_laced n S p r ∧ C.has_laced n S q s)

end config