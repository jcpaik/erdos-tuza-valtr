-- Mirror configuration
import ErdosTuzaValtr.Lib.Core.Rel3
import ErdosTuzaValtr.Lib.List.Default
import ErdosTuzaValtr.Config.Defs

variable {α : Type _} [LinearOrder α] (C : Config α)

open OrderDual

-- to_dual : α → αᵒᵈ
-- of_dual : αᵒᵈ → α
def Config.mirror : Config (OrderDual α) :=
  ⟨mirror3 C.Cup3, C.decidableCup3.mirror3⟩

variable {C}

@[simp]
def Mirror.cap {l : List α} : C.mirror.Cap l.mirror ↔ C.Cap l :=
  by
  constructor
  · rw [Config.Cap]; intro h; constructor
    exact list.chain'_mirror.mp h.left
    exact list.chain3'_mirror.mp h.right
  · intro h; rw [Config.Cap]; constructor
    exact list.chain'_mirror.mpr h.left
    exact list.chain3'_mirror.mpr h.right

@[simp]
def Mirror.cup {l : List α} : C.mirror.Cup l.mirror ↔ C.Cup l :=
  by
  constructor
  · rw [Config.Cup]; intro h; constructor
    exact list.chain'_mirror.mp h.left
    exact list.chain3'_mirror.mp h.right
  · intro h; rw [Config.Cup]; constructor
    exact list.chain'_mirror.mpr h.left
    exact list.chain3'_mirror.mpr h.right

@[simp]
def Mirror.gon {l1 l2 : List α} : C.mirror.Gon l1.mirror l2.mirror ↔ C.Gon l1 l2 :=
  by
  rw [Config.Gon]; rw [Config.Gon]
  simp [List.mirror_getLast?, List.mirror_head?]
  have t_inj : Function.Injective to_dual := fun a b => to_dual_inj.mp
  have ot_inj := Option.map_injective t_inj
  rw [ot_inj.eq_iff]; rw [ot_inj.eq_iff]; tauto

@[simp]
def Mirror.ncap {n : ℕ} {l : List α} : C.mirror.Ncap n l.mirror ↔ C.Ncap n l := by rw [Config.Ncap];
  rw [Config.Ncap]; simp

@[simp]
def Mirror.ncup {n : ℕ} {l : List α} : C.mirror.Ncup n l.mirror ↔ C.Ncup n l := by rw [Config.Ncup];
  rw [Config.Ncup]; simp

@[simp]
def Mirror.ngon {n : ℕ} {l1 l2 : List α} : C.Ngon n l1 l2 ↔ C.mirror.Ngon n l1.mirror l2.mirror :=
  by
  rw [Config.Ngon]; rw [Config.Ngon]
  rw [Mirror.gon]; simp

@[simp]
def Mirror.hasNcap {n : ℕ} {S : Finset α} : C.mirror.HasNcap n S.mirror ↔ C.HasNcap n S :=
  by
  constructor
  · intro h; rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩
    use c.of_mirror
    constructor; rw [← Mirror.ncap]; convert c_ncap; simp
    rw [← @List.ofMirror_mirror α _ c] at c_in c_ncap
    set co := c.of_mirror
    rw [← List.mirror_in]; assumption
  · intro h; rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩
    use c.mirror
    constructor; rw [Mirror.ncap]; tauto
    rw [List.mirror_in]; assumption

@[simp]
def Mirror.hasNcup {n : ℕ} {S : Finset α} : C.mirror.HasNcup n S.mirror ↔ C.HasNcup n S :=
  by
  constructor
  · intro h; rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩
    use c.of_mirror
    rw [← @List.ofMirror_mirror α _ c] at c_in c_ncup
    set co := c.of_mirror
    rw [List.mirror_in] at c_in
    rw [Mirror.ncup] at c_ncup; tauto
  · intro h; rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩
    use c.mirror
    constructor; rw [Mirror.ncup]; tauto
    rw [List.mirror_in]; assumption

def Mirror.hasNgon {n : ℕ} {S : Finset α} : C.mirror.HasNgon n S.mirror ↔ C.HasNgon n S :=
  by
  constructor
  · intro h; rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩
    use c1.of_mirror, c2.of_mirror
    rw [← @List.ofMirror_mirror α _ c1] at c1_in c_ngon
    rw [← @List.ofMirror_mirror α _ c2] at c2_in c_ngon
    set c1o := c1.of_mirror; set c2o := c2.of_mirror
    rw [List.mirror_in] at c1_in c2_in
    rw [← Mirror.ngon] at c_ngon; tauto
  · intro h; rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩
    use c1.mirror, c2.mirror
    constructor; rw [← Mirror.ngon]; tauto
    simp [List.mirror_in]; tauto
