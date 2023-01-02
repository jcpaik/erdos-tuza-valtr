import etv.defs
import etv.label

variables 
  {α : Type*} [linear_order α] {C : config α} 
  {S : finset α} (l : C.label S)

namespace config.label

private lemma mem_imply_nnil (a : α) {l : list α} (ha : a ∈ l) : l ≠ [] := 
  by intro eq; subst eq; simp at ha; tauto

def is_alpha_cup {a : α} (ha : a ∈ S) (c : list α) : Prop :=
  C.cup c ∧ c.last' = some a ∧ c.chain' l.slopeᶜ

instance decidable_is_alpha_cup {a : α} (ha : a ∈ S) (c : list α) :
  decidable (l.is_alpha_cup ha c) := by rw is_alpha_cup; apply_instance

def alpha_cups {a : α} (ha : a ∈ S) : 
  Σ' (lists : list (list α)), lists ≠ [] :=
⟨((S.sort (≤)).sublists.filter (l.is_alpha_cup ha)), 
  by apply mem_imply_nnil [a]; simp [is_alpha_cup]; tauto⟩

def alpha_cup {a : α} (ha : a ∈ S) : list α :=
  let ⟨lists, lists_nnil⟩ := l.alpha_cups ha in
  (lists.argmax list.length).get_or_else []

-- one off from actual definition
def alpha (a : α) : ℕ := 
  if ha : a ∈ S then (l.alpha_cup ha).length - 1 else 0

def is_beta_cup (l : C.label S) {a : α} (ha : a ∈ S) (c : list α) : Prop :=
  C.cup c ∧ c.last' = some a

instance decidable_is_beta_cup {a : α} (ha : a ∈ S) (c : list α) :
  decidable (l.is_beta_cup ha c) := by rw is_beta_cup; apply_instance

def beta_cups {a : α} (ha : a ∈ S) : 
  Σ' (lists : list (list α)), lists ≠ [] :=
⟨((S.sort (≤)).sublists.filter (l.is_beta_cup ha)), 
  by apply mem_imply_nnil [a]; simp [is_beta_cup]; tauto⟩

def beta_cup {a : α} (ha : a ∈ S) : list α :=
  let ⟨lists, lists_nnil⟩ := l.beta_cups ha in
  (lists.argmax list.length).get_or_else []

def beta (a : α) : ℕ :=
  if ha : a ∈ S then (l.beta_cup ha).length else 0

variables {a : α} (ha : a ∈ S)

theorem alpha_le_beta : l.alpha a ≤ l.beta a := sorry

theorem alpha_append_cup
  {n : ℕ} {c : list α} (hc : C.ncup n c) 
  (c_in_S : c.in S) (c_head : a ∈ c.head') :
  C.has_ncup (n + l.alpha a) S := sorry

theorem ff_inc_alpha {a b : α} (sab : ¬l.slope a b)
  (ha : a ∈ S) (hb : b ∈ S) (a_le_b : a < b) : 
  l.alpha a < l.alpha b := sorry

theorem tt_inc_alpha {a b : α} (sab : l.slope a b)
  (ha : a ∈ S) (hb : b ∈ S) (a_le_b : a < b) : 
  l.beta a < l.beta b := sorry

theorem has_beta_cup {a : α} (ha : a ∈ S) : 
  C.has_ncup (l.beta a) S := sorry

end config.label