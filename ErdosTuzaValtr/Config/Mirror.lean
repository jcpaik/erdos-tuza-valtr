-- Mirror configuration
import ErdosTuzaValtr.Lib.Core.Rel3
import ErdosTuzaValtr.Lib.List.Default
import ErdosTuzaValtr.Config.Defs

variable {α : Type _} [LinearOrder α] (C : Config α)

open OrderDual

-- to_dual : α → αᵒᵈ
-- of_dual : αᵒᵈ → α
def Config.Mirror : Config (OrderDual α) :=
  ⟨Mirror3 C.Cup3, C.DecidableCup3.Mirror3⟩

variable {C}

@[simp]
def Mirror.cap {l : List α} : C.Mirror.Cap l.Mirror ↔ C.Cap l :=
  by
  constructor
  · rw [Config.Cap]; intro h; constructor
    exact List.chain'_mirror.mp h.left
    exact List.chain3'_mirror.mp h.right
  · intro h; rw [Config.Cap]; constructor
    exact List.chain'_mirror.mpr h.left
    exact List.chain3'_mirror.mpr h.right

@[simp]
def Mirror.cup {l : List α} : C.Mirror.Cup l.Mirror ↔ C.Cup l :=
  by
  constructor
  · rw [Config.Cup]; intro h; constructor
    exact List.chain'_mirror.mp h.left
    exact List.chain3'_mirror.mp h.right
  · intro h; rw [Config.Cup]; constructor
    exact List.chain'_mirror.mpr h.left
    exact List.chain3'_mirror.mpr h.right

@[simp]
def Mirror.gon {l1 l2 : List α} : C.Mirror.Gon l1.Mirror l2.Mirror ↔ C.Gon l1 l2 :=
  by
  rw [Config.Gon]; rw [Config.Gon]
  simp [List.Mirror_getLast?, List.Mirror_head?]
  have t_inj : Function.Injective (⇑toDual : α → αᵒᵈ) := fun a b => toDual_inj.mp
  have ot_inj := Option.map_injective t_inj
  rw [ot_inj.eq_iff]; rw [ot_inj.eq_iff]; tauto

@[simp]
def Mirror.ncap {n : ℕ} {l : List α} : C.Mirror.NCap n l.Mirror ↔ C.NCap n l := by
  rw [Config.NCap]; rw [Config.NCap]; simp

@[simp]
def Mirror.ncup {n : ℕ} {l : List α} : C.Mirror.NCup n l.Mirror ↔ C.NCup n l := by
  rw [Config.NCup]; rw [Config.NCup]; simp

@[simp]
def Mirror.ngon {n : ℕ} {l1 l2 : List α} : C.NGon n l1 l2 ↔ C.Mirror.NGon n l1.Mirror l2.Mirror :=
  by
  rw [Config.NGon]; rw [Config.NGon]
  rw [Mirror.gon]; simp

@[simp]
def Mirror.hasNCap {n : ℕ} {S : Finset α} : C.Mirror.HasNCap n S.Mirror ↔ C.HasNCap n S :=
  by
  constructor
  · intro h; rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩
    use c.ofMirror
    constructor; rw [← Mirror.ncap]; convert c_ncap; simp
    rw [← @List.ofMirrorMirror α _ c] at c_in c_ncap
    set co := c.ofMirror
    rw [← List.Mirror_in]; assumption
  · intro h; rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩
    use c.Mirror
    constructor; rw [Mirror.ncap]; tauto
    rw [List.Mirror_in]; assumption

@[simp]
def Mirror.hasNCup {n : ℕ} {S : Finset α} : C.Mirror.HasNCup n S.Mirror ↔ C.HasNCup n S :=
  by
  constructor
  · intro h; rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩
    use c.ofMirror
    rw [← @List.ofMirrorMirror α _ c] at c_in c_ncup
    set co := c.ofMirror
    rw [List.Mirror_in] at c_in
    rw [Mirror.ncup] at c_ncup; tauto
  · intro h; rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩
    use c.Mirror
    constructor; rw [Mirror.ncup]; tauto
    rw [List.Mirror_in]; assumption

def Mirror.hasNGon {n : ℕ} {S : Finset α} : C.Mirror.HasNGon n S.Mirror ↔ C.HasNGon n S :=
  by
  constructor
  · intro h; rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩
    use c1.ofMirror, c2.ofMirror
    rw [← @List.ofMirrorMirror α _ c1] at c1_in c_ngon
    rw [← @List.ofMirrorMirror α _ c2] at c2_in c_ngon
    set c1o := c1.ofMirror; set c2o := c2.ofMirror
    rw [List.Mirror_in] at c1_in c2_in
    rw [← Mirror.ngon] at c_ngon; tauto
  · intro h; rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩
    use c1.Mirror, c2.Mirror
    constructor; rw [← Mirror.ngon]; tauto
    simp [List.Mirror_in]; tauto
