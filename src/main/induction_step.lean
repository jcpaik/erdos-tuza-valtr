import data.nat.choose
import data.finset

import config
import etv

import main.defs
import main.lemmas

open_locale classical
noncomputable theory

variables {α : Type*} [linear_order α] (C : config α)

namespace config

def row (i : ℕ) (S : finset α) : finset α :=
  S.filter (λ p, C.beta S p = i)

def delta (n : ℕ) (S : finset α) : finset α :=
  S.filter (λ p, ∃ i : ℕ, i ≤ n ∧ ↑p = (C.row i S).min)

lemma delta_card (n : ℕ) (S : finset α) : (C.delta n S).card ≤ n :=
begin
  sorry

end   

lemma cup_extension (n : ℕ) (S D : finset α) (l : C.label S)
  (S_card : (n + 3).choose 2 + 2 ≤ S.card)
  (cap4_free : ¬C.has_ncap 4 S) (cup_free : ¬C.has_ncup (n + 4) S)
  (D_def : D = C.delta (n + 2) S)
  (a : ℕ) (p' : α) (c : list α) 
  (c_cup : C.ncup a c) (c_in : c.in (S \ D)) (c_head : p' ∈ c.head') : 
  (∃ d : list α, C.ncup (n + 3) d ∧ d.in S ∧ p' ∈ d.last') ∨
  (l.alpha p' = 1 ∧
    ∃ p : α, C.ncup (a + 1) (p :: c) ∧ (p :: c).in S ∧
    l.alpha p = 0 ∧ C.beta S p = C.beta S p') :=
begin
  cases (nat.lt_or_ge (n+2) (C.beta S p')) with beta_p' beta_p',
  { rw nat.lt_iff_add_one_le at beta_p', sorry,
    -- TODO: use exists_beta_cup, and take
    },
  { sorry },
end

/-
I have a function `f : ℕ → option α` and I want to define a finset `S` defined as `{f 0, f 1, ..., f (n-1)} : finset α` with no elements for values of `f i = none`. Any good way of doing that? (say, so that I can utilize mathlib lemmas the best, like the fact that `S.card ≤ n`)

  ∀ (S : finset α),
  ¬C.has_join (n+2) (n+1) S →
  nat.choose (n+2) 2 + 2 ≤ S.card →
  ¬C.has_ncap 4 S → ¬C.has_ncup (n+3) S → 
-/
theorem main_induction_wlog (n : ℕ) :
  C.main_goal n → C.main_goal_wlog (n+1) :=
begin
  intros ih S no_join S_card cap4_free cup_free,
  set D := C.delta (n+2) S with def_D,
  have D_card := C.delta_card (n+2) S, rw ←def_D at D_card,
  have SD_card : (n + 2).choose 2 + 2 ≤ (S \ D).card := begin
    apply @nat.le_of_add_le_add_right D.card,
    rw finset.card_sdiff_add_card,
    apply le_trans _ (finset.card_le_of_subset (finset.subset_union_left S D)),
    apply le_trans _ S_card, 
    apply le_trans (nat.add_le_add_left D_card _) _,
    rw nat.add_right_comm, apply le_of_eq, 
    rw nat.add_right_comm n 1 2, simp, apply symm, rw nat.choose, simp,
    rw nat.add_comm,
  end,
  have t := ih (S \ D) SD_card _ _,
  swap, { intro h, rcases h with ⟨c, ⟨_, c_in⟩⟩,
    apply cap4_free, use c, split, assumption,
    apply list.in_superset _ c_in, exact finset.sdiff_subset S D, },
  swap, { intro h, rcases h with ⟨c, ⟨c_cup, c_in⟩⟩,
    sorry },
  sorry,
end

end config