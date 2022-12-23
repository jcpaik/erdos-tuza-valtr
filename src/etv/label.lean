import config

variables {α : Type*} [linear_order α] (C : config α)

namespace config

structure label (S : finset α) :=
(slope : S → S → Prop)
(decidable_slope : decidable_rel slope)
(extend_left : ∀ {a b}, a < b → ¬slope a b → ∀ c : S, c < a → C.cup3 c a b)
(extend_right : ∀ {a b}, a < b → slope a b → ∀ c : S, b < c → C.cup3 a b c)

def cap4_free_slope {S : finset α} (h : ¬C.has_cap 4 S) (a b : S) : Prop :=
  ∀ c : S, b < c → C.cup3 a b c

instance decidable_cap4_free_slope {S : finset α} (h : ¬C.has_cap 4 S) :
  decidable_rel (C.cap4_free_slope h) := 
λ a b, by rw cap4_free_slope; simp; apply_instance

def cap4_free_label {S : finset α} (h : ¬C.has_cap 4 S) : C.label S :=
begin
  use C.cap4_free_slope h,
  apply_instance,
  { intros a b hab hn c hca, 
    by_contra h', apply hn, intros d hd, 
    by_contra h'', apply h, use [[c, a, b, d]], split, {simp; tauto}, simp,  },
  { intros a b hab hy c hbc,
    exact hy c hbc },
end

end config