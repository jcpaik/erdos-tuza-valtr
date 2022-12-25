import config

variables {α : Type*} [linear_order α] (C : config α)

namespace config

structure label (S : finset α) :=
(slope : α → α → Prop)
(decidable_slope : decidable_rel slope)
-- The direction looks odd, but it is written in perspective of
-- _where_ the edge ab is placed
(extend_left : ∀ {a b : α}, a ∈ S → b ∈ S → a < b → ¬slope a b → 
  ∀ {c : α}, c ∈ S → b < c → C.cup3 a b c)
(extend_right : ∀ {a b : α}, a ∈ S → b ∈ S → a < b → slope a b →
  ∀ {c : α}, c ∈ S → c < a → C.cup3 c a b)

def cap4_free_slope {S : finset α} (h : ¬C.has_ncap 4 S) (a b : α) : Prop :=
  ∀ c : S, ↑c < a → C.cup3 c a b

instance decidable_cap4_free_slope {S : finset α} (h : ¬C.has_ncap 4 S) :
  decidable_rel (C.cap4_free_slope h) := 
λ a b, by rw cap4_free_slope; simp; apply_instance

def cap4_free_label {S : finset α} (h : ¬C.has_ncap 4 S) : C.label S :=
begin
  use C.cap4_free_slope h,
  apply_instance,
  { intros a b ha hb hab hn c hc hbc, 
    by_contra h', apply hn, intros d hd, 
    by_contra h'', apply h, use [[d, a, b, c]], simp, tauto },
  { intros a b ha hb hab hy c hc hca,
    exact hy ⟨c, hc⟩ hca },
end

namespace label

variables {C} {S : finset α} (label : C.label S)

section extend_cup

-- Best used as : apply l.extend_left_cup a b
-- Explicitly mention two points
theorem extend_left_cup 
  {a b : α} (s_ab : ¬label.slope a b) {l : list α} (l_cup : C.cup l)
  (ha : a ∈ S) (hab : a < b) (l_in_S : l.in S)
  (b_head_l : b ∈ l.head') : C.cup (a :: l) :=
begin
  cases l with b l,
  { simp at b_head_l, tauto },
  simp at b_head_l, subst b_head_l,
  cases l with c l,
  { simp, exact hab },
  simp at l_in_S, simp,
  refine ⟨_, _, _⟩; try {tauto},
  simp [config.cup] at l_cup,
  apply label.extend_left; tauto,
end 

theorem extend_right_cup 
  {a b : α} (s_ab : label.slope a b) {l : list α} (l_cup : C.cup l)
  (hab : a < b) (hb : b ∈ S) (l_in_S : l.in S)
  (a_last_l : a ∈ l.last') : C.cup (l ++ [b]) :=
begin
  by_cases hl : 2 ≤ l.length,
  { rcases list.take_last2 hl with ⟨c, a, l', eq_l⟩,
    rw eq_l at a_last_l, simp at a_last_l, subst a_last_l,
    rw eq_l, simp, rw ←eq_l,
    refine ⟨_, _, _⟩; try {tauto},
    simp [config.cup] at l_cup,
    rw eq_l at l_in_S, simp at l_in_S,
    rw eq_l at l_cup, simp at l_cup,
    apply label.extend_right; tauto },
  cases l with p l, simp,
  cases l with q l, simp at *, subst a_last_l; tauto,
  exfalso, apply hl, exact le_add_self,
end

end extend_cup

end label

end config