import config

variables {α : Type*} [linear_order α] (C : config α)

namespace config

def has_laced (n : ℕ) (S : finset α) (p q : α) : Prop :=
  ∃ (cp c cq : list α), 
    (C.cup cp ∧ C.cup c ∧ C.cup cq) ∧
    (p ∈ cp.last' ∧ p ∈ c.head' ∧ q ∈ c.last' ∧ q ∈ cq.head') ∧
    (cp.length + cq.length = n ∧ c.length = n)

def has_interweaved_laced
  (n : ℕ) (S : finset α) (p q r s : α) : Prop :=
  (p < q ∧ q ≤ r ∧ r < s) ∧
  (C.has_laced n S p r ∧ C.has_laced n S q s)

end config