import config
import etv.defs

open order_dual

variables {α : Type*} [linear_order α] {C : config α}

def mirror.has_laced {n : ℕ} {S : finset α} (p q : α) :
  C.mirror.has_laced n S.mirror 
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
    repeat { rw list.mirror_in at h }, 
    simp [list.mirror_last', list.mirror_head'] at h, 
    rw [nat.add_comm a b, eq_cp, eq_c, eq_cq], 
    simp [list.of_mirror_last', list.of_mirror_head'], tauto, },
  { intro h, rcases h with ⟨a, b, cp, c, cq, hcp, hc, hcq, h⟩,
    use [b, a, cq.mirror, c.mirror, cp.mirror],
    refine ⟨_, _, _, _⟩; try {rw mirror.ncup; tauto},
    repeat {rw [list.mirror_mem_last', list.mirror_mem_head']},
    simp, simp at h, rw nat.add_comm b a, tauto, },
end

def mirror.has_interweaved_laced {n : ℕ} {S : finset α} (p q r s : α) :
  C.mirror.has_interweaved_laced n S.mirror 
    (to_dual s) (to_dual r) (to_dual q) (to_dual p) ↔
  C.has_interweaved_laced n S p q r s :=
begin
  simp [config.has_interweaved_laced, mirror.has_laced],
  tauto,
end

def mirror.has_join {a b : ℕ} {S : finset α} :
  C.mirror.has_join b a S.mirror ↔ C.has_join a b S :=
begin
  split,
  { intro h, rcases h with ⟨pm, crm, clm, 
      ⟨crm_cup, crm_in, crm_last⟩, ⟨clm_cup, clm_in, clm_head⟩⟩,
    have eq_p := order_dual.to_dual_of_dual pm,
    have eq_cl := @list.of_mirror_mirror _ _ clm,
    have eq_cr := @list.of_mirror_mirror _ _ crm,
    set p := pm.of_dual,
    set cl := clm.of_mirror, set cr := crm.of_mirror,
    use [p, cl, cr],
    rw ←eq_p at clm_head crm_last,
    rw ←eq_cl at clm_cup clm_in clm_head,
    rw ←eq_cr at crm_cup crm_in crm_last,
    rw mirror.ncup at clm_cup crm_cup,
    rw list.mirror_in at clm_in crm_in,
    rw list.mirror_mem_head' at clm_head, 
    rw list.mirror_mem_last' at crm_last, tauto, },
  { intro h, rcases h with ⟨p, cl, cr, ⟨cl_cup, cl_in, cl_head⟩, 
      ⟨cr_cup, cr_in, cr_last⟩⟩,
    use [to_dual p, cr.mirror, cl.mirror],
    rw [list.mirror_mem_last', list.mirror_mem_head'],
    simp only [list.mirror_in, mirror.ncup, option.mem_def],
    tauto, },
end