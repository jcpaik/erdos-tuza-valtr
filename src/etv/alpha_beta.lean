import etv.defs
import etv.label

open_locale classical
noncomputable theory

variables 
  {α : Type*} [linear_order α] {C : config α} 
  {S : finset α} (l : C.label S)

private lemma mem_imply_nnil 
  {α : Type*} (a : α) {l : list α} (ha : a ∈ l) : l ≠ [] := 
  by intro eq; subst eq; simp at ha; tauto

namespace config.label

def is_alpha_cup (a : α) (c : list α) : Prop :=
  (c ++ [a]).in S ∧ (c ++ [a]).sorted (<) ∧ (c ++ [a]).chain' l.slopeᶜ

instance decidable_is_alpha_cup (a : α) (c : list α) :
  decidable (l.is_alpha_cup a c) := by rw is_alpha_cup; apply_instance

theorem alpha_cup_is_cup {c : list α} 
  (c_in_S : c.in S) (c_sorted : c.sorted (<))
  (c_chain : c.chain' l.slopeᶜ) : C.cup c :=
begin
  induction c with h0 c ih, simp,
  cases c with h1 c, simp,
  cases c with h2 c,
  { simp, simp at c_sorted, assumption, },
  simp, refine ⟨_, _, _⟩,
  simp at c_sorted; tauto,
  simp at c_in_S c_chain c_sorted; apply l.extend_left; tauto,
  apply ih; simp at ⊢ c_in_S c_chain c_sorted; tauto,
end

def alpha_cups' (a : α) : list (list α) :=
  (S.sort (≤)).sublists.filter (l.is_alpha_cup a)

def alpha_cup' (a : α) : option (list α) :=
  (l.alpha_cups' a).argmax list.length

def alpha_cup'_is_some {a : α} (ha : a ∈ S) : 
  option.is_some (l.alpha_cup' a) :=
begin
  rw [←option.ne_none_iff_is_some, config.label.alpha_cup'], simp,
  apply mem_imply_nnil [], simp [is_alpha_cup, alpha_cups'], exact ha,
end

-- one off from actual definition
def alpha (a : α) : ℕ := 
  if ha : a ∈ S then (option.get (l.alpha_cup'_is_some ha)).length else 0

-- APIs for alpha: First, existence of a cup with length alpha + 1
def alpha_cup {a : α} (ha : a ∈ S) : 
  Σ' c : list α, c.length = l.alpha a + 1 ∧ 
    c.in S ∧ c.sorted (<) ∧ c.chain' l.slopeᶜ ∧ a ∈ c.last' :=
begin
  have some := l.alpha_cup'_is_some ha,
  set c := option.get some with def_c, 
  rw alpha, rw dif_pos ha, rw ←def_c,
  have h_argmax := option.get_mem some, 
  rw [←def_c, alpha_cup'] at h_argmax,
  have c_alpha_cup := list.argmax_mem h_argmax,
  simp [alpha_cups', is_alpha_cup] at c_alpha_cup,
  use (c ++ [a]), simp, tauto,
end

-- Next, maximality of the cup with length alpha + 1
def cup_length_le_alpha {a : α} {c : list α}
  (c_in_S : c.in S) 
  (c_sorted : c.sorted (<))
  (c_chain : c.chain' l.slopeᶜ)
  (c_last : a ∈ c.last') : c.length ≤ l.alpha a + 1 :=
begin
  have ha : a ∈ S := c_in_S _ (list.mem_of_mem_last' c_last),
  have some := l.alpha_cup'_is_some ha,
  set d := option.get some with def_d, 
  rw alpha, rw dif_pos ha, rw ←def_d,
  have h_argmax := option.get_mem some, 
  rw [←def_d, alpha_cup'] at h_argmax,
  rcases list.take_last' c_last with ⟨c', eq_c⟩,
  subst eq_c, simp,
  have c'_alpha_cup : c' ∈ l.alpha_cups' a := begin
    rw alpha_cups', simp, split,
    { apply list.sublist_of_subperm_of_sorted _ _ 
        (finset.sort_sorted_lt S),
      apply list.nodup.subperm,
      apply @list.nodup.sublist _ _ (c' ++ [a]), 
      simp, exact (list.sorted.nodup c_sorted),
      intros a ha, simp, simp at c_in_S, exact (c_in_S.left) _ ha,
      apply list.pairwise.sublist _ c_sorted, simp, },
    { refine ⟨_, _, _⟩; assumption },
  end,
  exact list.le_of_mem_argmax c'_alpha_cup h_argmax,
end

theorem add_alpha {a : α} (ha : a ∈ S)
  {n : ℕ} {c : list α} (c_in_S : c.in S)
  (c_cup : C.ncup n c) (c_head : a ∈ c.head') : 
  C.has_ncup (n + l.alpha a) S :=
begin
  rcases (l.alpha_cup ha) with 
    ⟨d, d_length, d_in_S, d_sorted, d_chain, d_last⟩,
  have d_cup : C.cup d := l.alpha_cup_is_cup d_in_S d_sorted d_chain,
  rcases list.take_last' d_last with ⟨d', eq_d⟩,
  rcases list.take_head' c_head with ⟨c', eq_c⟩,
  use d' ++ a :: c', 
  by_cases hd' : d' = [],
  { subst hd', simp at eq_d, subst eq_d, simp at d_length, rw d_length,
    rw ←eq_c, split; simp; assumption, },
  rcases list.take_last hd' with ⟨p, d'', eq_d'⟩,
  cases c' with q c'',
  { subst eq_c, cases c_cup with _ c_len, simp at c_len,
    subst c_len, rw ←eq_d, refine ⟨⟨_, _⟩, _⟩,
    assumption, rw d_length, exact add_comm _ _, assumption, },
  rw eq_d', split, 
  { rw [config.ncup], split, simp, refine ⟨_, _, _⟩,
    convert d_cup, rw [eq_d, eq_d'], simp,
    rw eq_d' at eq_d, simp at eq_d, 
    rw eq_d at d_chain d_sorted d_in_S,
    rw eq_c at c_in_S c_cup,
    rw list.sorted at d_sorted,
    rw [config.ncup, config.cup] at c_cup,
    apply l.extend_left,
    simp at d_in_S; tauto, simp at d_in_S; tauto,
    have t := @list.pairwise.sublist 
      _ _ [p, a] (d'' ++ [p, a]) _ d_sorted,
    simp at t, exact t, simp,
    simp at d_chain; tauto,
    simp at c_in_S; tauto,
    simp at c_cup; tauto,
    rw ←eq_c, exact c_cup.left,
    rw eq_d at d_length, simp at d_length,
    rw ←eq_c, rw ←eq_d', simp, rw d_length,
    rw c_cup.right, exact add_comm _ _, },
  { rw ←eq_c, rw ←eq_d', simp, rw eq_d at d_in_S,
    simp at d_in_S, tauto, },
end

end config.label

namespace config

variable (C)

def is_beta_cup {a : α} (ha : a ∈ S) (c : list α) : Prop :=
  C.cup c ∧ c.last' = some a

instance decidable_is_beta_cup {a : α} (ha : a ∈ S) (c : list α) :
  decidable (C.is_beta_cup ha c) := by rw is_beta_cup; apply_instance

def beta_cups {a : α} (ha : a ∈ S) : list (list α) :=
  (S.sort (≤)).sublists.filter (C.is_beta_cup ha)

def beta_cups_nnil {a : α} (ha : a ∈ S) : C.beta_cups ha ≠ [] :=
  by apply mem_imply_nnil [a]; simp [beta_cups, is_beta_cup]; tauto

def beta_cup' {a : α} (ha : a ∈ S) : option (list α) :=
  (C.beta_cups ha).argmax list.length

def beta_cup'_is_some {a : α} (ha : a ∈ S) : option.is_some (C.beta_cup' ha) :=
begin
  rw ←option.ne_none_iff_is_some, rw config.beta_cup', simp,
  exact C.beta_cups_nnil ha,
end

def beta_cup {a : α} (ha : a ∈ S) : list α :=
  option.get (C.beta_cup'_is_some ha)

variable (S)

def beta (a : α) : ℕ :=
  if ha : a ∈ S then (C.beta_cup ha).length else 0

lemma exists_beta_cup {a : α} (ha : a ∈ S) {n : ℕ} (hn : n ≤ C.beta S a): 
  ∃ c : list α, C.ncup n c ∧ c.in S ∧ a ∈ c.last' :=
begin
  sorry
end

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