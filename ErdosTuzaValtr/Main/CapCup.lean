import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Project.Config.Default
import Mathlib.Project.Etv.Default

#align_import ErdosTuzaValtr.Main.cap_cup

open scoped Classical

noncomputable section

namespace Config

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem has_cap2_cup2 {S : Finset α} (hS : 1 < S.card) : C.HasNCap 2 S ∧ C.HasNCup 2 S :=
  by
  set l := S.sort (· ≤ ·) with eq_l
  have hl : 2 ≤ l.length := by rw [eq_l] <;> simp <;> exact hS
  rcases List.takeHead2 hl with ⟨a, b, t, eq_ab⟩
  have sorted := Finset.sort_sorted_lt S; rw [← eq_l] at sorted
  have a_lt_b : a < b := by rw [eq_ab] at sorted <;> simp at sorted <;> tauto
  have a_in_S : a ∈ l := by rw [eq_ab] <;> simp
  rw [eq_l] at a_in_S; simp at a_in_S
  have b_in_S : b ∈ l := by rw [eq_ab] <;> simp
  rw [eq_l] at b_in_S; simp at b_in_S
  constructor
  · use[a, b]; simp [Config.NCap]; tauto
  · use[a, b]; simp [Config.NCap]; tauto

theorem binom_eq (a b : ℕ) :
    (a + b + 2).choose (a + 1) = (a + b + 1).choose a + (a + b + 1).choose (a + 1) :=
  rfl

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cap_cup (a b : ℕ) (S : Finset α) (hS : Nat.choose (a + b) a < S.card) :
    C.HasNCap (a + 2) S ∨ C.HasNCup (b + 2) S :=
  by
  revert a b S hS; refine' Nat.pincerRecursion _ _ _
  -- case b = 0
  · simp; intro a S hS; right; exact (C.has_cap2_cup2 hS).right
  -- case a = 0
  · simp; intro a S hS; left; exact (C.has_cap2_cup2 hS).left
  -- diagonal induction
  · intro a b
    repeat' rw [a.succ_eq_add_one]; repeat' rw [b.succ_eq_add_one]
    set sz_ab1 := (a + (b + 1)).choose a with eq_sz_ab1
    set sz_a1b := (a + 1 + b).choose (a + 1) with eq_sz_a1b
    set sz_a1b1 := (a + 1 + (b + 1)).choose (a + 1) with eq_sz_a1b1
    have eq_sz : sz_a1b1 = sz_ab1 + sz_a1b := by rw [eq_sz_ab1, eq_sz_a1b, eq_sz_a1b1] <;> ring_nf
    -- numerical details now not relevant
    clear eq_sz_ab1 eq_sz_a1b eq_sz_a1b1
    ring_nf; intro hab1 ha1b S hS
    set is_start_of_cap : α → Prop := fun p =>
      ∃ c, C.cap c ∧ c.In S ∧ c.length = a + 2 ∧ p ∈ c.head? with def_is_start_of_cap
    set T := Finset.filter is_start_of_cap S with def_T
    have eq_card : (S \ T).card + T.card = S.card :=
      by
      apply Finset.card_sdiff_add_card_eq_card
      rw [def_T]; exact S.filter_subset is_start_of_cap
    have sz_cases : sz_ab1 < (S \ T).card ∨ sz_a1b < T.card := by by_contra! <;> linarith
    cases sz_cases
    -- case sz_ab1 < (S \ T).card
    · cases' hab1 (S \ T) sz_cases with hcap hcup
      rcases hcap with ⟨c, ⟨c_cap, c_length⟩, c_in⟩
      · have c_nnil : c ≠ [] := by intro eq_c <;> subst eq_c <;> cases c_length
        rcases List.takeHead c_nnil with ⟨ch, ct, eq_c⟩
        have h : ch ∈ S \ T := by apply c_in <;> rw [eq_c] <;> simp
        rw [def_T] at h; simp at h; cases' h with c_in_S h
        have f := h c_in_S c c_cap _ c_length; rw [eq_c] at f; simp at f
        exfalso; exact f
        refine' List.in_superset _ c_in; simp
      · right
        exact hasNCup_supset (Finset.sdiff_subset S T) hcup
    -- case sz_a1b < T.card
    cases' ha1b T sz_cases with hcap hcup
    · left; refine' hasNCap_supset _ hcap
      rw [def_T]; simp
    · rcases hcup with ⟨cl, ⟨cl_cup, cl_length⟩, cl_in_T⟩
      have cl_sz2 : 2 ≤ cl.length := by rw [cl_length] <;> simp
      rcases List.takeLast2 cl_sz2 with ⟨p, q, cl', eq_cl⟩; clear cl_sz2
      have q_in_T : q ∈ T := by refine' cl_in_T q _ <;> rw [eq_cl] <;> simp
      rw [def_T] at q_in_T <;> simp at q_in_T
      cases' q_in_T with q_in_S q_st; simp [def_is_start_of_cap] at q_st
      rcases q_st with ⟨cr, cr_cap, cr_in_S, cr_length, cr_head⟩
      have cr_sz2 : 2 ≤ cr.length := by rw [cr_length] <;> simp
      rcases List.takeHead2 cr_sz2 with ⟨q, r, cr', eq_cr⟩; clear cr_sz2
      rw [eq_cr] at cr_head; simp at cr_head; subst cr_head
      by_cases hpqr : C.cup3 p q r
      · right; use cl ++ [r]; refine' ⟨⟨_, _⟩, _⟩
        · rw [eq_cl]; simp; rw [← eq_cl]
          rw [eq_cr] at cr_cap; simp [Config.Cap] at cr_cap; tauto
        · simp; rw [cl_length]
        · simp; constructor
          refine' List.in_superset _ cl_in_T; rw [def_T]; simp
          rw [eq_cr] at cr_in_S; simp at cr_in_S; tauto
      · left; use p::cr; refine' ⟨⟨_, _⟩, _⟩
        · rw [eq_cr]; simp; rw [← eq_cr]
          rw [eq_cl] at cl_cup; simp [Config.Cup] at cl_cup; tauto
        · simp; rw [cr_length]
        · simp; rw [eq_cl] at cl_in_T; simp at cl_in_T; tauto

end Config
