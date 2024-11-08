import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import ErdosTuzaValtr.Lib.Core.Rel3

variable {α : Type _}

-- Local notion for a list contained in a finset
protected def List.In (l : List α) (S : Finset α) : Prop :=
  ∀ a : α, a ∈ l → a ∈ S

protected def Finset.Mirror [LinearOrder α] (S : Finset α) : Finset αᵒᵈ :=
  Finset.image OrderDual.toDual S

protected def Finset.ofMirror [LinearOrder α] (S : Finset αᵒᵈ) : Finset α :=
  Finset.image OrderDual.ofDual S

namespace List

-- Local notion for flipping a list of elements, together with its order
protected def Mirror [LinearOrder α] (l : List α) : List αᵒᵈ :=
  (List.map OrderDual.toDual l).reverse

protected def ofMirror [LinearOrder α] (l : List αᵒᵈ) : List α :=
  (List.map OrderDual.ofDual l).reverse

variable (R : α → α → α → Prop)

inductive Chain3 : α → α → List α → Prop
  | nil {a b : α} : Chain3 a b []
  | cons : ∀ {a b c : α} {l : List α}, R a b c → Chain3 b c l → Chain3 a b (c :: l)

def Chain3' : List α → Prop
  | nil => True
  | [_] => True
  | a :: b :: l => Chain3 R a b l

variable {R}

@[simp]
theorem chain3_cons {a b c : α} {l : List α} : Chain3 R a b (c :: l) ↔ R a b c ∧ Chain3 R b c l :=
  ⟨fun p => by cases' p with _ a b c l _ n p <;> exact ⟨n, p⟩, fun ⟨n, p⟩ => p.cons n⟩

@[simp]
theorem chain3_nil {a b : α} : Chain3 R a b [] := Chain3.nil

instance decidableChain3 [DecidableRel3 R] (a b : α) (l : List α) : Decidable (Chain3 R a b l) := by
  induction l generalizing a b <;> simp only [Chain3.nil, chain3_cons] <;> infer_instance

instance decidableChain3' [DecidableRel3 R] (l : List α) : Decidable (Chain3' R l) := by
  cases' l with _ l <;> try cases' l with _ l <;> dsimp only [Chain3'] <;> infer_instance
  rw [Chain3']
  infer_instance

end List
