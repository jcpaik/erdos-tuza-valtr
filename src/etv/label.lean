-- develops the language of slope labeling

import tactic.basic
import tactic.ring
import tactic.linarith
import logic.nontrivial

import list
import etv.defs

-- proof uses classical logic for shortcut
open_locale classical
noncomputable theory

variable {α : Type*}
-- true when the triple forms a cup

structure label (s : list α) (R : α → α → α → Prop) :=
-- abuse classical logic and extend label to any pairs of α's
-- to not have to check containment every single time
( slope : α → α → Prop ) 
( ext_left : ∀ {a b : α}, ¬slope a b → ∀ {c : α}, [c, a, b] <+ s → R c a b )
( ext_right : ∀ {a b : α}, slope a b → ∀ {c : α}, [a, b, c] <+ s → R a b c )

-- existence of label
noncomputable def find_slope 
  {s : list α} {R : α → α → α → Prop} (h : s.cap_free R 4) (a b : α): Prop :=
  if hab : [a, b] <+ s then
    if hc : ∀ c, [c, a, b] <+ s → R c a b then false
    else true
  else false

noncomputable def find_label 
  {s : list α} {R : α → α → α → Prop} 
  (s_nodup : s.nodup) (h : s.cap_free R 4) : label s R := 
begin
  use (find_slope h),
  -- ext_left
  { assume a b hnab c cab_in_s,
    have ab_in_s : [a, b] <+ s := list.sublist_of_cons_sublist cab_in_s,
    rw find_slope at hnab, simp at hnab, tauto },
  -- ext_right
  { assume a b hab c cab_in_s,
    have ab_in_s : [a, b] <+ s := by { 
      have h := [a, b].sublist_append_left [c], simp at h,
      from list.sublist.trans h cab_in_s,
    },
    rw find_slope at hab, simp at hab,
    rcases hab with ⟨_, ⟨x, xab_in_s, cap_xab⟩⟩,
    by_contra cap_abc, apply h,
    use [[x, a, b, c]], split,
    { have eq : [x, a, b, c] = [x] ++ [a, b] ++ [c] := by simp, rw eq,
      apply list.nodup_sublist_overlap; tauto },
    { rw list.is_cap, simp; tauto, },
  },
end

-- basic extension lemmas of slope label


-- building the notion of alpha and beta
@[simp]
private def list.exists_sublist_with_last 
  (s : list α) (P : list α → Prop) (x : α) (n : ℕ) :=
  ∃ (c : list α) (c_nnil : c ≠ []), 
    c <+ s ∧ P c ∧ c.first c_nnil = x ∧ c.length = n

@[simp]
private def list.longest_sublist_with_last
  (s : list α) (P : list α → Prop) (x : α) (alpha : ℕ) :=
  ∀ (c : list α) (c_nnil : c ≠ []),
    c <+ s → P c → c.first c_nnil = x → c.length ≤ alpha

private noncomputable def list.sublist_with_last_x
  (s : list α) (P : list α → Prop) (singleton_P : ∀ a : α, P [a]) 
  (x : α) (hx : x ∈ s) : 
  {n // s.exists_sublist_with_last P x n ∧ s.longest_sublist_with_last P x n} :=
begin
  set p := list.exists_sublist_with_last s P x with eq_p,
  suffices h : ∃ (m : ℕ), p m ∧ ∀ (x : ℕ), p x → x ≤ m,
  { apply classical.indefinite_description, 
    rcases h with ⟨m, ⟨pm, m_largest⟩⟩, 
    use m, split, tauto, 
    rw eq_p at m_largest, 
    assume c c_nnil _ _ _,
    have h' := m_largest c.length, apply h',
    use [c, c_nnil], tauto },
  apply nat.find_max_x,
  { rewrite eq_p, 
    have hx : [x] ≠ [] := by simp,
    use [1, [x], hx]; simp, tauto, },
  { use s.length, 
    intros m pm, rw eq_p at pm,
    rcases pm with ⟨c, _nnil, c_in_s, _, _, c_len⟩,
    rw ←c_len, exact list.sublist.length_le c_in_s, }
end

namespace label

variables {s : list α} {R : α → α → α → Prop}

@[simp]
def has_alpha_chain (l : label s R) (c : list α) : Prop :=
  c.chain' l.slopeᶜ

def alpha_x (l : label s R) {x : α} (hx : x ∈ s) : 
  {n // s.exists_sublist_with_last (has_alpha_chain l) x n ∧ 
        s.longest_sublist_with_last (has_alpha_chain l) x n} := 
  (s.sublist_with_last_x (has_alpha_chain l) (λ a, by simp) x hx)

def alpha (l : label s R) {x : α} (hx : x ∈ s) : ℕ := 
  (alpha_x l hx).1

theorem alpha_has
  {s : list α} {l : label s R}
  {x : α} {hx : x ∈ s} {a : ℕ}
  (ha : a = l.alpha hx) : 
  ∃ (c : list α) (c_nnil : c ≠ []), 
    c <+ s ∧ c.chain' l.slopeᶜ ∧ c.first c_nnil = x ∧ c.length = a :=
begin
  have ha' : a = (alpha_x l hx).1 := by {rw ha, simp [alpha]}, 
  cases alpha_x l hx with n hn, simp at ha', subst ha', exact hn.left,
end 

def alpha_max
  {s : list α} {l : label s R}
  {x : α} {hx : x ∈ s} {a : ℕ}
  (ha : a = l.alpha hx) : 
  ∀ (c : list α) (c_nnil : c ≠ []),
    c <+ s → c.chain' l.slopeᶜ → c.first c_nnil = x → c.length ≤ a
  :=
begin
  have ha' : a = (alpha_x l hx).1 := by {rw ha, simp [alpha]}, 
  cases alpha_x l hx with n hn, simp at ha', subst ha', exact hn.right,
end

@[simp]
def has_beta_chain (l : label s R) (c : list α) : Prop :=
  c.chain3' R

def beta_x (l : label s R) {x : α} (hx : x ∈ s) : 
  {n // s.exists_sublist_with_last (has_beta_chain l) x n ∧ 
        s.longest_sublist_with_last (has_beta_chain l) x n} := 
  (s.sublist_with_last_x (has_beta_chain l) (λ a, by simp) x hx)

def beta (l : label s R) {x : α} (hx : x ∈ s) : ℕ := 
  (beta_x l hx).1

theorem beta_has
  {s : list α} {l : label s R}
  {x : α} {hx : x ∈ s} {a : ℕ}
  (ha : a = l.beta hx) : 
  ∃ (c : list α) (c_nnil : c ≠ []), 
    c <+ s ∧ c.chain3' R ∧ c.first c_nnil = x ∧ c.length = a :=
begin
  have ha' : a = (beta_x l hx).1 := by {rw ha, simp [beta]}, 
  cases beta_x l hx with n hn, simp at ha', subst ha', exact hn.left,
end 

def beta_max
  {s : list α} {l : label s R}
  {x : α} {hx : x ∈ s} {a : ℕ}
  (ha : a = l.beta hx) : 
  ∀ (c : list α) (c_nnil : c ≠ []),
    c <+ s → c.chain3' R → c.first c_nnil = x → c.length ≤ a
  :=
begin
  have ha' : a = (beta_x l hx).1 := by {rw ha, simp [beta]}, 
  cases beta_x l hx with n hn, simp at ha', subst ha', exact hn.right,
end

end label