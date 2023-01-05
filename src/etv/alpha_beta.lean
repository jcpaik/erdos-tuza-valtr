import etv.defs
import etv.label

open_locale classical
noncomputable theory

variables 
  {α : Type*} [linear_order α] {C : config α} 
  {S : finset α} (l : C.label S)

private lemma mem_imply_nnil (a : α) {l : list α} (ha : a ∈ l) : l ≠ [] := 
  by intro eq; subst eq; simp at ha; tauto

namespace config.label

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

end config.label

namespace config

variable (C)

def is_beta_cup {a : α} (ha : a ∈ S) (c : list α) : Prop :=
  C.cup c ∧ c.last' = some a

instance decidable_is_beta_cup {a : α} (ha : a ∈ S) (c : list α) :
  decidable (C.is_beta_cup ha c) := by rw is_beta_cup; apply_instance

def beta_cups {a : α} (ha : a ∈ S) : 
  Σ' (lists : list (list α)), lists ≠ [] :=
⟨((S.sort (≤)).sublists.filter (C.is_beta_cup ha)), 
  by apply mem_imply_nnil [a]; simp [is_beta_cup]; tauto⟩

def beta_cup {a : α} (ha : a ∈ S) : list α :=
  let ⟨lists, lists_nnil⟩ := C.beta_cups ha in
  (lists.argmax list.length).get_or_else []

variable (S)

def beta (a : α) : ℕ :=
  if ha : a ∈ S then (C.beta_cup ha).length else 0

variables {a : α} (ha : a ∈ S)

def row (S : finset α) (i : ℕ) : finset α :=
  S.filter (λ p, C.beta S p = i)

def delta (S : finset α) : finset α :=
  S.filter (λ p, ∃ i : ℕ, ↑p = (C.row S i).min)

/-
Define a map from delta to some set
Show that it is injective...

theorem alpha_le_beta : l.alpha a ≤ C.beta S a := sorry

theorem alpha_append_cup
  {n : ℕ} {c : list α} (hc : C.ncup n c) 
  (c_in_S : c.in S) (c_head : a ∈ c.head') :
  C.has_ncup (n + l.alpha a) S := sorry

theorem ff_inc_alpha {a b : α} (sab : ¬l.slope a b)
  (ha : a ∈ S) (hb : b ∈ S) (a_le_b : a < b) : 
  l.alpha a < l.alpha b := sorry

theorem tt_inc_alpha {a b : α} (sab : l.slope a b)
  (ha : a ∈ S) (hb : b ∈ S) (a_le_b : a < b) : 
  C.beta S a < C.beta S b := sorry

theorem has_beta_cup {a : α} (ha : a ∈ S) : 
  C.has_ncup (C.beta S a) S := sorry
-/

end config