import tactic.basic
import logic.basic
import lib.core.decidable

variable {α : Type*}

namespace list

variable (R : α → α → α → Prop)

inductive chain3 : α → α → list α → Prop
| nil {a b : α} : chain3 a b [] 
| cons : ∀ {a b c : α} {l : list α}, 
    R a b c → chain3 b c l → chain3 a b (c :: l)

def chain3' : list α → Prop
| [] := true
| [_] := true
| (a :: b :: l) := chain3 R a b l

variable {R}
@[simp]
theorem chain3_cons {a b c : α} {l : list α} : 
  chain3 R a b (c :: l) ↔ R a b c ∧ chain3 R b c l :=
⟨ λ p, by cases p with _ a b c l _ n p; exact ⟨n, p⟩, 
  λ ⟨n, p⟩, p.cons n ⟩

attribute [simp] chain3.nil

instance decidable_chain3 [decidable_trel R] 
  (a b : α) (l : list α) : decidable (chain3 R a b l) :=
by induction l generalizing a b; simp only [chain3.nil, chain3_cons]; resetI; apply_instance

instance decidable_chain3' [decidable_trel R] (l : list α) : decidable (chain3' R l) :=
by cases l with _ l; try {cases l with _ l}; dunfold chain3'; apply_instance

end list