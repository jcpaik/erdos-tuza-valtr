import list

variable {α : Type*}
-- true when the triple forms a cup
variable (R : α → α → α → Prop)

def list.is_cap (a : ℕ) : list α → Prop := 
  λ cap : list α, cap.chain3' Rᶜ ∧ cap.length = a

def list.is_cup (a : ℕ) : list α → Prop := 
  λ cup : list α, cup.chain3' R ∧ cup.length = a

def is_gon (n : ℕ) (cap cup : list α) : Prop := 
  ∃ (a b : ℕ) (cap_not_nil : cap ≠ []) (cup_not_nil : cup ≠ []),
    n = a + b + 2 ∧
    cap.is_cap R (a + 2) ∧ cup.is_cup R (b + 2) ∧ 
    cap.first cap_not_nil = cup.first cup_not_nil ∧ 
    cap.last cap_not_nil = cup.last cup_not_nil

def erdos_tuza_valtr (n a b m : ℕ) : Prop :=
  ∀ (s : list α) (s_nodup : s.nodup) (s_size : s.length = m),
    (∃ cap : list α, cap <+ s ∧ cap.is_cap R a) ∨
    (∃ cup : list α, cup <+ s ∧ cup.is_cup R b) ∨
    (∃ (cap cup : list α), cap <+ s ∧ cup <+ s ∧ is_gon R n cap cup)

def list.has_cap (a : ℕ) (s : list α) : Prop :=
  (∃ cap : list α, cap <+ s ∧ cap.is_cap R a)

def list.has_cup (b : ℕ) (s : list α) : Prop :=
  (∃ cup : list α, cup <+ s ∧ cup.is_cup R b)

def list.has_gon (n : ℕ) (s : list α) : Prop :=
  (∃ cap cup : list α, cap <+ s ∧ cup <+ s ∧ is_gon R n cap cup)

def list.cap_free (a : ℕ) (s : list α) : Prop := ¬(s.has_cap R a)

def list.cup_free (b : ℕ) (s : list α) : Prop := ¬(s.has_cup R b)

def list.gon_free (n : ℕ) (s : list α) : Prop := ¬(s.has_gon R n)