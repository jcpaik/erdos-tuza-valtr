import config
import etv.defs

open order_dual

variables {α : Type*} [linear_order α] {C : config α}

def mirror.has_laced {n : ℕ} {S : finset α} (p q : α) :
  C.mirror.has_laced n (finset.image to_dual S) 
    (to_dual q) (to_dual p) ↔
  C.has_laced n S p q :=
begin
  split,
  { intro h, rcases h with ⟨b, a, cqm, cm, cpm, hcqm, hcm, hcpm, h⟩,
    rw ←@list.of_mirror_mirror _ _ cpm at hcpm h,
    set cp := cpm.of_mirror with eq_cp, 
    rw mirror.ncup at hcpm,
    rw ←@list.of_mirror_mirror _ _ cm at hcm h,
    set c := cm.of_mirror with eq_c, 
    rw mirror.ncup at hcm,
    rw ←@list.of_mirror_mirror _ _ cqm at hcqm h,
    set cq := cqm.of_mirror with eq_cq, 
    rw mirror.ncup at hcqm,
    use [a, b, cp, c, cq, hcpm, hcm, hcqm],
    repeat { rw list.mirror_in at h }, simp at h, 
    rw [nat.add_comm a b, eq_cp, eq_c, eq_cq], simp, tauto, },
  { intro h, rcases h with ⟨a, b, cp, c, cq, hcp, hc, hcq, h⟩,
    use [b, a, cq.mirror, c.mirror, cp.mirror],
    refine ⟨_, _, _, _⟩; try {rw mirror.ncup; tauto},
    simp, simp at h, rw nat.add_comm b a, tauto, },
end

def mirror.has_interweaved_laced {n : ℕ} {S : finset α} (p q r s : α) :
  C.mirror.has_interweaved_laced n (finset.image to_dual S) 
    (to_dual s) (to_dual r) (to_dual q) (to_dual p) ↔
  C.has_interweaved_laced n S p q r s :=
begin
  simp [config.has_interweaved_laced, mirror.has_laced],
  tauto,
end