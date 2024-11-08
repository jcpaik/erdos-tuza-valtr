import Mathlib.Project.Config.Default
import ErdosTuzaValtr.Etv.Defs

open OrderDual

variable {α : Type _} [LinearOrder α] {C : Config α}

def Mirror.hasLaced {n : ℕ} {S : Finset α} (p q : α) :
    C.Mirror.HasLaced n S.Mirror (toDual q) (toDual p) ↔ C.HasLaced n S p q :=
  by
  constructor
  · intro h; rcases h with ⟨b, a, cqm, cm, cpm, hcqm, hcm, hcpm, h⟩
    rw [← @List.ofMirrorMirror _ _ cpm] at hcpm h
    set cp := cpm.ofMirror with eq_cp
    rw [Mirror.ncup] at hcpm
    rw [← @List.ofMirrorMirror _ _ cm] at hcm h
    set c := cm.ofMirror with eq_c
    rw [Mirror.ncup] at hcm
    rw [← @List.ofMirrorMirror _ _ cqm] at hcqm h
    set cq := cqm.ofMirror with eq_cq
    rw [Mirror.ncup] at hcqm
    use a, b, cp, c, cq, hcpm, hcm, hcqm
    repeat' rw [List.Mirror_in] at h
    simp [List.Mirror_getLast?, List.Mirror_head?] at h
    rw [Nat.add_comm a b, eq_cp, eq_c, eq_cq]
    simp [List.ofMirror_getLast?, List.ofMirror_head?]; tauto
  · intro h; rcases h with ⟨a, b, cp, c, cq, hcp, hc, hcq, h⟩
    use b, a, cq.Mirror, c.Mirror, cp.Mirror
    refine' ⟨_, _, _, _⟩ <;> try rw [Mirror.ncup] <;> tauto
    repeat' rw [List.Mirror_mem_getLast?, List.Mirror_mem_head?]
    simp; simp at h; rw [Nat.add_comm b a]; tauto

def Mirror.hasInterweavedLaced {n : ℕ} {S : Finset α} (p q r s : α) :
    C.Mirror.HasInterweavedLaced n S.Mirror (toDual s) (toDual r) (toDual q) (toDual p) ↔
      C.HasInterweavedLaced n S p q r s :=
  by
  simp [Config.HasInterweavedLaced, Mirror.hasLaced]
  tauto

def Mirror.hasJoin {a b : ℕ} {S : Finset α} : C.Mirror.HasJoin b a S.Mirror ↔ C.HasJoin a b S :=
  by
  constructor
  · intro h; rcases h with ⟨pm, crm, clm, ⟨crm_cup, crm_in, crm_last⟩, ⟨clm_cup, clm_in, clm_head⟩⟩
    have eq_p := OrderDual.toDual_ofDual pm
    have eq_cl := @List.ofMirrorMirror _ _ clm
    have eq_cr := @List.ofMirrorMirror _ _ crm
    set p := pm.of_dual
    set cl := clm.ofMirror; set cr := crm.ofMirror
    use p, cl, cr
    rw [← eq_p] at clm_head crm_last
    rw [← eq_cl] at clm_cup clm_in clm_head
    rw [← eq_cr] at crm_cup crm_in crm_last
    rw [Mirror.ncup] at clm_cup crm_cup
    rw [List.Mirror_in] at clm_in crm_in
    rw [List.Mirror_mem_head?] at clm_head
    rw [List.Mirror_mem_getLast?] at crm_last; tauto
  · intro h; rcases h with ⟨p, cl, cr, ⟨cl_cup, cl_in, cl_head⟩, ⟨cr_cup, cr_in, cr_last⟩⟩
    use to_dual p, cr.Mirror, cl.Mirror
    rw [List.Mirror_mem_getLast?, List.Mirror_mem_head?]
    simp only [List.Mirror_in, Mirror.ncup, Option.mem_def]
    tauto
