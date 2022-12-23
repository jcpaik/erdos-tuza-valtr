import config

variables {α : Type*} [linear_order α] (C : config α)

namespace config

structure label (S : finset α) :=
(slope : S → S → Prop)
(decidable_slope : decidable_rel slope)
-- The direction looks odd, but it is written in perspective of
-- _where_ the edge ab is placed
(extend_left : ∀ {a b : S} {h : a < b}, 
  ¬slope a b → ∀ c : S, b < c → C.cup3 a b c)
(extend_right : ∀ {a b : S} {h : a < b}, 
  slope a b → ∀ c : S, c < a → C.cup3 c a b)

def cap4_free_slope {S : finset α} (h : ¬C.has_ncap 4 S) (a b : S) : Prop :=
  ∀ c : S, b < c → C.cup3 a b c

instance decidable_cap4_free_slope {S : finset α} (h : ¬C.has_ncap 4 S) :
  decidable_rel (C.cap4_free_slope h) := 
λ a b, by rw cap4_free_slope; simp; apply_instance

def cap4_free_label {S : finset α} (h : ¬C.has_ncap 4 S) : C.label S :=
begin
  use C.cap4_free_slope h,
  apply_instance,
  { intros a b hab hn c hca, 
    by_contra h', apply hn, intros d hd, 
    by_contra h'', apply h, use [[c, a, b, d]], split, {simp; tauto}, simp, },
  { intros a b hab hy c hbc,
    exact hy c hbc },
end

end config

namespace label

variables {C} {S : finset α} (label : C.label S)

theorem extend_left_cup 
  {a b : S} {h : a < b} (s_ab : ¬label.slope a b) 
  {l : list α} (l_cup : C.cup l) (l_in_S : l.in S)
  (b_in_l : ↑b ∈ l.head') : C.cup (a :: l) :=
begin
  cases l with b l,
  { simp at b_in_l, tauto },
  simp at b_in_l, subst b_in_l,
  cases l with c l,
  { simp, tauto },
  simp at l_in_S, have c_in_S : c ∈ S := by tauto,
  simp, have h' := label.extend_left s_ab ⟨c, c_in_S⟩,
end 

theorem extend_right_cup 
  {a b : S} {h : a < b} 
  (s_ab : l.slope a b) (l : list α) : 
  ↑a ∈ l.last' → C.cup (l ++ [b]) := sorry 

end label