-- Erdos-Tuza-Valtr conjecture on a set-theoretic model of convexity

import tactic.basic
import tactic.ring
import tactic.linarith
import logic.nontrivial

import list
import etv.defs
import etv.label

-- proof uses classical logic for shortcut
open_locale classical
noncomputable theory

variable {α : Type*}
-- true when the triple forms a cup
variable (R : α → α → α → Prop)

theorem main (n : ℕ) (hn : 3 ≤ n) : 
  erdos_tuza_valtr R n 4 n ((n-1)*(n-2) / 2 + 2) := sorry