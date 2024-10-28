import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Project.Config.Default
import Mathlib.Project.Etv.Default

#align_import ErdosTuzaValtr.Main.defs

open scoped Classical

noncomputable section

variable {α : Type _} [LinearOrder α] (C : Config α)

def Config.MainGoal (n : ℕ) : Prop :=
  ∀ S : Finset α,
    Nat.choose (n + 2) 2 + 2 ≤ S.card →
      ¬C.HasNcap 4 S → ¬C.HasNcup (n + 3) S → ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s

def Config.MainGoalWlog (n : ℕ) : Prop :=
  ∀ S : Finset α,
    ¬C.HasJoin (n + 2) (n + 1) S →
      Nat.choose (n + 2) 2 + 2 ≤ S.card →
        ¬C.HasNcap 4 S → ¬C.HasNcup (n + 3) S → ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s