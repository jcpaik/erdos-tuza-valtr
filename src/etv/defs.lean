import config

variables {α : Type*} [linear_order α] (C : config α)

namespace config

def has_laced (n : ℕ) (S : finset α) (p q : α) : Prop :=
  ∃ {a b : ℕ} {cp c cq : list α} 
    (hcp : C.ncup a cp) (hc : C.ncup n c) (hcQ : C.ncup b cq),
    (cp.in S ∧ c.in S ∧ cq.in S) ∧ a + b = n ∧ 
    (p ∈ cp.last' ∧ p ∈ c.head' ∧ q ∈ c.last' ∧ q ∈ cq.head')

theorem has_laced.mem_ends {C : config α} {n : ℕ} {S : finset α} {p q : α}
  (h : C.has_laced n S p q) : p ∈ S ∧ q ∈ S :=
begin
  rcases h with ⟨-, -, -, c, -, -, -, -, 
    ⟨-, c_in_S, -⟩, -, ⟨-, c_head, c_last, -⟩⟩,
  exact ⟨c_in_S _ (list.mem_of_mem_head' c_head), 
    c_in_S _ (list.mem_of_mem_last' c_last)⟩,
end

def has_interweaved_laced
  (n : ℕ) (S : finset α) (p q r s : α) : Prop :=
  (p < q ∧ q ≤ r ∧ r < s) ∧
  (C.has_laced n S p r ∧ C.has_laced n S q s)

def has_join (a b : ℕ) (S : finset α) : Prop :=
  ∃ (p : α) (cl cr : list α),
    (C.ncup a cl ∧ cl.in S ∧ p ∈ cl.last') ∧ 
    (C.ncup b cr ∧ cr.in S ∧ p ∈ cr.head')

end config