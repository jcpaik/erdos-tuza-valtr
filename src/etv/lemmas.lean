import etv.defs
import etv.label

variables {α : Type*} [linear_order α] (C : config α)

lemma config.join_ncup_ncup (S : finset α)
  {n : ℕ} (hn : 2 ≤ n)
  (cap4_free : ¬C.has_cap 4 S)
  (cup_sn_free : ¬C.has_cup (n+1) S)
  {c1 : list α} (hc1 : C.cup n c1)
  {c2 : list α} (hc2 : C.cup n c2)
  (p : α) (hp1 : p ∈ c1.last') (hp2 : p ∈ c2.head') : C.has_gon n S :=
begin
  have l := C.cap4_free_label cap4_free,
  
end