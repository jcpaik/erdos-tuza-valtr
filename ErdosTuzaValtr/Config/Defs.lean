import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import ErdosTuzaValtr.Lib.List.Default
import ErdosTuzaValtr.Lib.Core.Rel3

structure Config (α : Type _) [LinearOrder α] where
  Cup3 : α → α → α → Prop
  decidableCup3 : DecidableRel3 Cup3

namespace Config

variable {α : Type _} [ord : LinearOrder α] (C : Config α)

attribute [instance] Config.decidableCup3

-- Notion of 3-caps
def Cap3 (a b c : α) : Prop :=
  ¬C.Cup3 a b c

def decidableCap3 : DecidableRel3 C.Cap3 := fun a b c => @instDecidableNot _ (C.decidableCup3 a b c)

attribute [instance] Config.decidableCap3

-- Notion of caps and cups
def Cap (l : List α) : Prop :=
  l.Chain' (· < ·) ∧ l.Chain3' C.Cap3

def Cup (l : List α) : Prop :=
  l.Chain' (· < ·) ∧ l.Chain3' C.Cup3

@[simp]
def Gon (l1 l2 : List α) : Prop :=
  2 ≤ l1.length ∧
    C.Cap l1 ∧ 2 ≤ l2.length ∧ C.Cup l2 ∧ l1.head? = l2.head? ∧ l1.getLast? = l2.getLast?

instance decidableCup {l : List α} : Decidable (C.Cup l) := by rw [Cup] <;> infer_instance

def Ncap (n : ℕ) (l : List α) : Prop :=
  C.Cap l ∧ l.length = n

def Ncup (n : ℕ) (l : List α) : Prop :=
  C.Cup l ∧ l.length = n

def Ngon (n : ℕ) (l1 l2 : List α) : Prop :=
  C.Gon l1 l2 ∧ l1.length + l2.length = n + 2

def HasNcap (n : ℕ) (S : Finset α) : Prop :=
  ∃ l : List α, C.Ncap n l ∧ l.In S

def HasNcup (n : ℕ) (S : Finset α) : Prop :=
  ∃ l : List α, C.Ncup n l ∧ l.In S

def HasNgon (n : ℕ) (S : Finset α) : Prop :=
  ∃ l1 l2 : List α, C.Ngon n l1 l2 ∧ l1.In S ∧ l2.In S

end Config
