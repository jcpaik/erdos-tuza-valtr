-- Mirror configuration

import config.defs

namespace config

variables {α : Type*} [linear_order α] (C : config α)

def mirror : config (order_dual α) :=
⟨(λ x y z, C.cup3 z y x), (λ p q r, C.decidable_cup3 r q p)⟩  

end config