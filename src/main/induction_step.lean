import data.nat.choose
import data.finset

import config
import etv

import main.defs
import main.lemmas

open_locale classical
noncomputable theory

variables {α : Type*} [linear_order α] (C : config α)

theorem config.main_induction_wlog (n : ℕ) :
  C.main_goal n → C.main_goal_wlog (n+1) := sorry