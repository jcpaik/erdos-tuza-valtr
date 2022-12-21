import etv.defs
import etv.label
import tactic.linarith

open_locale classical
noncomputable theory

variables (α : Type*) (R : α → α → α → Prop) 

-- this is used a lot in followings
open list.sublist

-- Lemma 5.1
theorem joint_max_cups 
  (n : ℕ) (hn : n ≥ 2) (s : list α) (s_nodup : s.nodup)
  (hs4 : s.cap_free R 4) (hsn : s.cup_free R (n+1))
  (c1 c2 : list α)
  (c1_nnil : c1 ≠ []) (c1_in_s : c1 <+ s) (hc1 : c1.is_cup R n)
  (c2_nnil : c2 ≠ []) (c2_in_s : c2 <+ s) (hc2 : c2.is_cup R n)
  (h : c1.last c1_nnil = c2.first c2_nnil) :
  s.has_gon R (n + 1) :=
begin
  set x := c1.last c1_nnil with eq_x_c1_last,
  rename h → eq_x_c2_first,
  have c1_size2 : 2 ≤ c1.length := by {rw list.is_cup at hc1, linarith},
  have c2_size2 : 2 ≤ c2.length := by {rw list.is_cup at hc2, linarith},
  -- destructing two elements of c1 and c2...
  rcases (c1.take_last2 c1_size2) with ⟨a, x', ⟨c1', eq_c1, eq_x'⟩⟩,
  rw eq_x' at eq_x_c1_last, subst eq_x_c1_last, 
  rcases (c2.take_first2 c2_size2) with ⟨x', b, ⟨c2', eq_c2, eq_x'⟩⟩,
  rw eq_x' at eq_x_c2_first, subst eq_x_c2_first,
  clear eq_x' eq_x' c1_size2 c2_size2,

  have ab_in_s : [a, b] <+ s,
  { have ax_in_c1 : [a, x] <+ c1 := by {rw eq_c1, simp},
    have ax_in_s : [a, x] <+ s := trans ax_in_c1 c1_in_s,
    have xb_in_c2 : [x, b] <+ c2 := by {rw eq_c2, 
      apply cons2, apply cons2, simp },
    have xb_in_s : [x, b] <+ s := trans xb_in_c2 c2_in_s,
    have axb_in_s : [a] ++ [x] ++ [b] <+ s,
    apply list.nodup_sublist_overlap; tauto, 
    revert axb_in_s, apply list.sublist.trans,
    apply cons2, apply cons, simp, },
  have l := find_label s_nodup hs4,
  set s := l.slope ab_in_s with eq_s,
end