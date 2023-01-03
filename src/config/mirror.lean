-- Mirror configuration

import lib.core.trel
import lib.list
import config.defs

variables {α : Type*} [linear_order α] (C : config α)

open order_dual

-- to_dual : α → αᵒᵈ
-- of_dual : αᵒᵈ → α

def config.mirror : config (order_dual α) :=
⟨mirror3 C.cup3, C.decidable_cup3.mirror3⟩

variable {C}

@[simp]
def mirror.cap {l : list α} : 
  C.mirror.cap l.mirror ↔ C.cap l:=
begin 
  split,
  { rw config.cap, intro h, split,
    exact list.chain'_mirror.mp h.left, 
    exact list.chain3'_mirror.mp h.right, },
  { intro h, rw config.cap, split,
    exact list.chain'_mirror.mpr h.left,
    exact list.chain3'_mirror.mpr h.right },
end

@[simp]
def mirror.cup {l : list α} : 
  C.mirror.cup l.mirror ↔ C.cup l :=
begin 
  split,
  { rw config.cup, intro h, split,
    exact list.chain'_mirror.mp h.left, 
    exact list.chain3'_mirror.mp h.right, },
  { intro h, rw config.cup, split,
    exact list.chain'_mirror.mpr h.left,
    exact list.chain3'_mirror.mpr h.right },
end

@[simp]
def mirror.gon {l1 l2 : list α} : 
  C.mirror.gon l1.mirror l2.mirror ↔ C.gon l1 l2 :=
begin
  rw config.gon, rw config.gon, simp,
  have t_inj : function.injective to_dual :=
    λ a b, to_dual_inj.mp,
  have ot_inj := option.map_injective t_inj,
  rw ot_inj.eq_iff, rw ot_inj.eq_iff, tauto,
end

@[simp]
def mirror.ncap {n : ℕ} {l : list α} : 
  C.mirror.ncap n l.mirror ↔ C.ncap n l :=
begin
  rw config.ncap, rw config.ncap, simp,
end

@[simp]
def mirror.ncup {n : ℕ} {l : list α} : 
  C.mirror.ncup n l.mirror ↔ C.ncup n l :=
begin
  rw config.ncup, rw config.ncup, simp,
end

@[simp]
def mirror.ngon {n : ℕ} {l1 l2 : list α} : 
  C.ngon n l1 l2 ↔ 
  C.mirror.ngon n l1.mirror l2.mirror :=
begin
  rw config.ngon, rw config.ngon,
  rw mirror.gon, simp, 
end

@[simp]
def mirror.has_ncap {n : ℕ} {S : finset α} : 
  (C.mirror).has_ncap n S.mirror ↔
  C.has_ncap n S :=
begin
  split,
  { intro h, rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩,
    use c.of_mirror,
    split, rw ←mirror.ncap, convert c_ncap, simp,
    rw ←(@list.of_mirror_mirror α _ c) at c_in c_ncap,
    set co := c.of_mirror,
    rw ←list.mirror_in, assumption, },
  { intro h, rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩,
    use c.mirror,
    split, rw mirror.ncap, tauto,
    rw list.mirror_in, assumption, },
end

@[simp]
def mirror.has_ncup {n : ℕ} {S : finset α} : 
  (C.mirror).has_ncup n S.mirror ↔
  C.has_ncup n S :=
begin
  split,
  { intro h, rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩,
    use c.of_mirror,
    rw ←(@list.of_mirror_mirror α _ c) at c_in c_ncup,
    set co := c.of_mirror,
    rw list.mirror_in at c_in, 
    rw mirror.ncup at c_ncup, tauto, },
  { intro h, rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩,
    use c.mirror,
    split, rw mirror.ncup, tauto,
    rw list.mirror_in, assumption, },
end

def mirror.has_ngon {n : ℕ} {S : finset α} : 
  (C.mirror).has_ngon n S.mirror ↔
  C.has_ngon n S :=
begin
  split,
  { intro h, rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩,
    use [c1.of_mirror, c2.of_mirror],
    rw ←(@list.of_mirror_mirror α _ c1) at c1_in c_ngon,
    rw ←(@list.of_mirror_mirror α _ c2) at c2_in c_ngon,
    set c1o := c1.of_mirror, set c2o := c2.of_mirror,
    rw list.mirror_in at c1_in c2_in,
    rw ←mirror.ngon at c_ngon, tauto },
  { intro h, rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩,
    use [c1.mirror, c2.mirror], 
    split, rw ←mirror.ngon, tauto,
    simp [list.mirror_in], tauto },
end