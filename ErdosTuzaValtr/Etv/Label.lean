import Mathlib.Data.Finset.Basic
import ErdosTuzaValtr.Lib.Core.Rel3
import Mathlib.Config.Default

variable {α : Type _} [LinearOrder α] (C : Config α)

structure Config.Label (S : Finset α) where
  Slope : α → α → Prop
  decidableSlope : DecidableRel slope
  -- The direction looks odd, but it is written in perspective of
  -- _where_ the edge ab is placed
  extend_left :
    ∀ {a b : α}, a ∈ S → b ∈ S → a < b → ¬slope a b → ∀ {c : α}, c ∈ S → b < c → C.Cup3 a b c
  extend_right :
    ∀ {a b : α}, a ∈ S → b ∈ S → a < b → slope a b → ∀ {c : α}, c ∈ S → c < a → C.Cup3 c a b

attribute [instance] Config.Label.decidableSlope

def Cap4FreeSlope {S : Finset α} (h : ¬C.HasNCap 4 S) (a b : α) : Prop :=
  ∀ c : S, ↑c < a → C.Cup3 c a b

instance decidableCap4FreeSlope {S : Finset α} (h : ¬C.HasNCap 4 S) :
    DecidableRel (Cap4FreeSlope C h) := fun a b => by rw [Cap4FreeSlope] <;> simp <;> infer_instance

variable {C}

def cap4FreeLabel {S : Finset α} (h : ¬C.HasNCap 4 S) : C.Label S :=
  by
  use Cap4FreeSlope C h
  infer_instance
  · intro a b ha hb hab hn c hc hbc
    by_contra h'; apply hn; intro d hd
    by_contra h''; apply h; use[d, a, b, c]; simp [Config.NCap]; tauto
  · intro a b ha hb hab hy c hc hca
    exact hy ⟨c, hc⟩ hca

variable {C} {S : Finset α} {label : C.Label S}

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
protected theorem Config.Cup.extend_left {l : List α} (l_cup : C.Cup l) {a b : α}
    (s_ab : ¬label.Slope a b) (ha : a ∈ S) (hab : a < b) (l_in_S : l.In S)
    (b_head_l : b ∈ l.head?) : C.Cup (a::l) :=
  by
  cases' l with b l
  · simp at b_head_l; tauto
  simp at b_head_l; subst b_head_l
  cases' l with c l
  · simp; exact hab
  simp at l_in_S; simp
  refine' ⟨_, _, _⟩ <;> try tauto
  simp [Config.Cup] at l_cup
  apply label.extend_left <;> tauto

protected theorem Config.Cup.extend_right {l : List α} (l_cup : C.Cup l) {a b : α}
    (s_ab : label.Slope a b) (hab : a < b) (hb : b ∈ S) (l_in_S : l.In S)
    (a_last_l : a ∈ l.getLast?) : C.Cup (l ++ [b]) :=
  by
  by_cases hl : 2 ≤ l.length
  · rcases List.takeLast2 hl with ⟨c, a, l', eq_l⟩
    rw [eq_l] at a_last_l; simp at a_last_l; subst a_last_l
    rw [eq_l]; simp; rw [← eq_l]
    refine' ⟨_, _, _⟩ <;> try tauto
    simp [Config.Cup] at l_cup
    rw [eq_l] at l_in_S; simp at l_in_S
    rw [eq_l] at l_cup; simp at l_cup
    apply label.extend_right <;> tauto
  cases' l with p l; simp
  cases' l with q l; simp at *; subst a_last_l <;> tauto
  exfalso; apply hl; exact le_add_self

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
protected theorem Config.NCup.extend_left {n : ℕ} {l : List α} (l_ncup : C.NCup n l) {a b : α}
    (s_ab : ¬label.Slope a b) (ha : a ∈ S) (hab : a < b) (l_in_S : l.In S)
    (b_head_l : b ∈ l.head?) : C.NCup (n + 1) (a::l) :=
  by
  cases' l_ncup with l_cup l_len; constructor
  apply l_cup.extend_left s_ab <;> try assumption
  simp; assumption

protected theorem Config.NCup.extend_right {n : ℕ} {l : List α} (l_ncup : C.NCup n l) {a b : α}
    (s_ab : label.Slope a b) (hab : a < b) (hb : b ∈ S) (l_in_S : l.In S)
    (a_last_l : a ∈ l.getLast?) : C.NCup (n + 1) (l ++ [b]) :=
  by
  cases' l_ncup with l_cup l_len; constructor
  apply l_cup.extend_right s_ab <;> try assumption
  simp; assumption

variable (label)

open OrderDual

protected def Config.Label.mirror : C.mirror.Label S.mirror :=
  ⟨fun a b => ¬Mirror2 label.Slope a b, fun a b =>
    @Not.decidable _ (label.decidableSlope.Mirror2 a b),
    by
    intro a b a_in_S b_in_S hab hslope c c_in_S hbc
    simp [Mirror2] at hslope
    simp [Config.mirror, Mirror3]
    simp [Finset.mirror] at a_in_S b_in_S c_in_S
    rcases a_in_S with ⟨oa, ⟨oa_in_S, oa_eq⟩⟩
    rcases b_in_S with ⟨ob, ⟨ob_in_S, ob_eq⟩⟩
    rcases c_in_S with ⟨oc, ⟨oc_in_S, oc_eq⟩⟩
    rw [← oa_eq] at hab
    rw [← ob_eq] at hab hbc
    rw [← oc_eq] at hbc
    simp at hab hbc
    rw [← oa_eq, ← ob_eq, ← oc_eq]; simp
    rw [← oa_eq, ← ob_eq] at hslope; simp at hslope
    apply label.extend_right <;> tauto,
    by
    intro a b a_in_S b_in_S hab hslope c c_in_S hca
    simp [Mirror2] at hslope
    simp [Config.mirror, Mirror3]
    simp [Finset.mirror] at a_in_S b_in_S c_in_S
    rcases a_in_S with ⟨oa, ⟨oa_in_S, oa_eq⟩⟩
    rcases b_in_S with ⟨ob, ⟨ob_in_S, ob_eq⟩⟩
    rcases c_in_S with ⟨oc, ⟨oc_in_S, oc_eq⟩⟩
    rw [← oa_eq] at hab hca
    rw [← ob_eq] at hab
    rw [← oc_eq] at hca
    simp at hab hca
    rw [← oa_eq, ← ob_eq, ← oc_eq]; simp
    rw [← oa_eq, ← ob_eq] at hslope; simp at hslope
    apply label.extend_left <;> tauto⟩

variable {label}

def mirror_slope {a b : α} : ¬label.mirror.Slope (toDual b) (toDual a) ↔ label.Slope a b :=
  by
  rw [Config.Label.mirror]; simp
  rw [Mirror2]; simp
