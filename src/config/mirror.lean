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

def cap.mirror {l : list α} : 
  C.cap l ↔ C.mirror.cap l.mirror :=
begin 
  split,
  { intro h, rw config.cap, split,
    exact list.chain'_mirror.mp h.left,
    exact list.chain3'_mirror.mp h.right },
  { rw config.cap, intro h, split,
    exact list.chain'_mirror.mpr h.left, 
    exact list.chain3'_mirror.mpr h.right, }
end

def cup.mirror {l : list α} : 
  C.cup l ↔ C.mirror.cup l.mirror :=
begin 
  split,
  { intro h, rw config.cup, split,
    exact list.chain'_mirror.mp h.left,
    exact list.chain3'_mirror.mp h.right },
  { rw config.cup, intro h, split,
    exact list.chain'_mirror.mpr h.left, 
    exact list.chain3'_mirror.mpr h.right, }
end

def gon.mirror {l1 l2 : list α} : 
  C.gon l1 l2 ↔ C.mirror.gon l1.mirror l2.mirror :=
begin
  rw config.gon, rw config.gon, simp,
  rw [←cap.mirror, ←cup.mirror], simp,
  have t_inj : function.injective to_dual :=
    λ a b, to_dual_inj.mp,
  have ot_inj := option.map_injective t_inj,
  rw ot_inj.eq_iff, rw ot_inj.eq_iff, tauto,
end

def ncap.mirror {n : ℕ} {l : list α} : 
  C.ncap n l ↔ C.mirror.ncap n l.mirror :=
begin
  rw config.ncap, rw config.ncap,
  rw cap.mirror, simp,
end

def ncup.mirror {n : ℕ} {l : list α} : 
  C.ncup n l ↔ C.mirror.ncup n l.mirror :=
begin
  rw config.ncup, rw config.ncup,
  rw cup.mirror, simp,
end

def ngon.mirror {n : ℕ} {l1 l2 : list α} : 
  C.ngon n l1 l2 ↔ 
  C.mirror.ngon n l1.mirror l2.mirror :=
begin
  rw config.ngon, rw config.ngon,
  rw ←gon.mirror, simp, 
end

def has_ncap.mirror {n : ℕ} {S : finset α} : 
  C.has_ncap n S ↔ 
  (C.mirror).has_ncap n (finset.image to_dual S) :=
begin
  split,
  { intro h, rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩,
    use c.mirror,
    split, rw ←ncap.mirror, tauto,
    rw list.mirror_in, assumption, },
  { intro h, rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩,
    use c.of_mirror,
    split, rw ncap.mirror, convert c_ncap, simp,
    rw ←(@list.of_mirror_mirror α _ c) at c_in c_ncap,
    set co := c.of_mirror,
    rw ←list.mirror_in, assumption, }
end

def has_ncup.mirror {n : ℕ} {S : finset α} : 
  C.has_ncup n S ↔ 
  (C.mirror).has_ncup n (finset.image to_dual S) :=
begin
  split,
  { intro h, rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩,
    use c.mirror,
    split, rw ←ncup.mirror, tauto,
    rw list.mirror_in, assumption, },
  { intro h, rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩,
    use c.of_mirror,
    rw ←(@list.of_mirror_mirror α _ c) at c_in c_ncup,
    set co := c.of_mirror,
    rw list.mirror_in at c_in, 
    rw ←ncup.mirror at c_ncup, tauto, }
end

def has_ngon.mirror {n : ℕ} {S : finset α} : 
  C.has_ngon n S ↔ 
  (C.mirror).has_ngon n (finset.image to_dual S) :=
begin
  split,
  { intro h, rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩,
    use [c1.mirror, c2.mirror], 
    split, rw ←ngon.mirror, tauto,
    simp [list.mirror_in], tauto },
  { intro h, rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩,
    use [c1.of_mirror, c2.of_mirror],
    rw ←(@list.of_mirror_mirror α _ c1) at c1_in c_ngon,
    rw ←(@list.of_mirror_mirror α _ c2) at c2_in c_ngon,
    set c1o := c1.of_mirror, set c2o := c2.of_mirror,
    rw list.mirror_in at c1_in c2_in,
    rw ←ngon.mirror at c_ngon, tauto }
end