import Mathlib.Project.Config.Default
import ErdosTuzaValtr.Etv.Defs

#align_import ErdosTuzaValtr.Etv.mirror

open OrderDual

variable {α : Type _} [LinearOrder α] {C : Config α}

def Mirror.hasLaced {n : ℕ} {S : Finset α} (p q : α) :
    C.mirror.HasLaced n S.mirror (toDual q) (toDual p) ↔ C.HasLaced n S p q :=
  by
  constructor
  · intro h; rcases h with ⟨b, a, cqm, cm, cpm, hcqm, hcm, hcpm, h⟩
    rw [← @List.ofMirror_mirror _ _ cpm] at hcpm h
    set cp := cpm.of_mirror with eq_cp
    rw [Mirror.ncup] at hcpm
    rw [← @List.ofMirror_mirror _ _ cm] at hcm h
    set c := cm.of_mirror with eq_c
    rw [Mirror.ncup] at hcm
    rw [← @List.ofMirror_mirror _ _ cqm] at hcqm h
    set cq := cqm.of_mirror with eq_cq
    rw [Mirror.ncup] at hcqm
    use a, b, cp, c, cq, hcpm, hcm, hcqm
    repeat' rw [List.mirror_in] at h
    simp [List.mirror_getLast?, List.mirror_head?] at h
    rw [Nat.add_comm a b, eq_cp, eq_c, eq_cq]
    simp [List.ofMirror_getLast?, List.ofMirror_head?]; tauto
  · intro h; rcases h with ⟨a, b, cp, c, cq, hcp, hc, hcq, h⟩
    use b, a, cq.mirror, c.mirror, cp.mirror
    refine' ⟨_, _, _, _⟩ <;> try rw [Mirror.ncup] <;> tauto
    repeat' rw [List.mirror_mem_getLast?, List.mirror_mem_head?]
    simp; simp at h; rw [Nat.add_comm b a]; tauto

def Mirror.hasInterweavedLaced {n : ℕ} {S : Finset α} (p q r s : α) :
    C.mirror.HasInterweavedLaced n S.mirror (toDual s) (toDual r) (toDual q) (toDual p) ↔
      C.HasInterweavedLaced n S p q r s :=
  by
  simp [Config.HasInterweavedLaced, Mirror.hasLaced]
  tauto

def Mirror.hasJoin {a b : ℕ} {S : Finset α} : C.mirror.HasJoin b a S.mirror ↔ C.HasJoin a b S :=
  by
  constructor
  · intro h; rcases h with ⟨pm, crm, clm, ⟨crm_cup, crm_in, crm_last⟩, ⟨clm_cup, clm_in, clm_head⟩⟩
    have eq_p := OrderDual.toDual_ofDual pm
    have eq_cl := @List.ofMirror_mirror _ _ clm
    have eq_cr := @List.ofMirror_mirror _ _ crm
    set p := pm.of_dual
    set cl := clm.of_mirror; set cr := crm.of_mirror
    use p, cl, cr
    rw [← eq_p] at clm_head crm_last
    rw [← eq_cl] at clm_cup clm_in clm_head
    rw [← eq_cr] at crm_cup crm_in crm_last
    rw [Mirror.ncup] at clm_cup crm_cup
    rw [List.mirror_in] at clm_in crm_in
    rw [List.mirror_mem_head?] at clm_head
    rw [List.mirror_mem_getLast?] at crm_last; tauto
  · intro h; rcases h with ⟨p, cl, cr, ⟨cl_cup, cl_in, cl_head⟩, ⟨cr_cup, cr_in, cr_last⟩⟩
    use to_dual p, cr.mirror, cl.mirror
    rw [List.mirror_mem_getLast?, List.mirror_mem_head?]
    simp only [List.mirror_in, Mirror.ncup, Option.mem_def]
    tauto
