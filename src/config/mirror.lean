-- Mirror configuration

import lib.core.trel
import config.defs

variables {α : Type*} [linear_order α] (C : config α)

-- Identifies α and αᵒᵖ with abuse

def config.mirror : config (order_dual α) :=
⟨flip3 C.cup3, (λ p q r, C.decidable_cup3 r q p)⟩

variable {C}

def cap3.mirror : C.mirror.cap3 = flip3 C.cap3 :=
begin 
  apply funext, intro a,
  apply funext, intro b,
  apply funext, intro c,
  simp [config.mirror, config.cap3, flip3],
end

def cap.mirror {l : list α} : 
  C.cap l ↔ C.mirror.cap l.reverse :=
begin 
  split,
  { intro h, rw config.cap, split,
    exact list.chain'_reverse.mpr h.left,
    exact list.chain3'_reverse.mpr h.right },
  { rw config.cap, intro h, split,
    exact list.chain'_reverse.mp h.left, 
    exact list.chain3'_reverse.mp h.right, }
end

def cup.mirror {l : list α} : 
  C.cup l ↔ C.mirror.cup l.reverse :=
begin 
  split,
  { intro h, rw config.cup, split,
    exact list.chain'_reverse.mpr h.left,
    exact list.chain3'_reverse.mpr h.right },
  { rw config.cup, intro h, split,
    exact list.chain'_reverse.mp h.left, 
    exact list.chain3'_reverse.mp h.right, }
end

def gon.mirror {l1 l2 : list α} : 
  C.gon l1 l2 ↔ C.mirror.gon l1.reverse l2.reverse :=
begin
  rw config.gon, rw config.gon, simp,
  rw [←cap.mirror, ←cup.mirror], tauto,
end

def ncap.mirror {n : ℕ} {l : list α} : 
  C.ncap n l ↔ C.mirror.ncap n l.reverse :=
begin
  rw config.ncap, rw config.ncap,
  rw cap.mirror, simp,
end

def ncup.mirror {n : ℕ} {l : list α} : 
  C.ncup n l ↔ C.mirror.ncup n l.reverse :=
begin
  rw config.ncup, rw config.ncup,
  rw cup.mirror, simp,
end

def ngon.mirror {n : ℕ} {l1 l2 : list α} : 
  C.ngon n l1 l2 ↔ 
  C.mirror.ngon n l1.reverse l2.reverse :=
begin
  rw config.ngon, rw config.ngon,
  rw ←gon.mirror, simp, 
end

def has_ncap.mirror {n : ℕ} {S : finset α} : 
  C.has_ncap n S ↔ 
  (C.mirror).has_ncap n (order_dual.to_dual S) :=
begin
  split,
  { intro h, rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩,
    use (order_dual.to_dual c).reverse,
    split, rw ←ncap.mirror, tauto,
    simp [list.in, has_subset.subset],
    intro x, simp [list.in] at c_in,
    intro hx, have x_in_c : x ∈ c, assumption, 
    rw ←list.mem_to_finset at x_in_c,
    have x_in_S : x ∈ S := c_in x_in_c, assumption },
  { intro h, rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩,
    use (order_dual.of_dual c).reverse,
    simp, split, rw ncap.mirror, convert c_ncap, simp, tauto,
    intro x, simp [list.in] at c_in, simp,
    intro hx, have x_in_c : order_dual.to_dual x ∈ c.to_finset,
    simp, assumption,
    have x_in_S := c_in x_in_c, tauto,
}
end
def has_ncup.mirror (n : ℕ) (S : finset α) : Prop :=
  ∃ (l : list α), C.ncup n l ∧ l.in S
def has_ngon.mirror (n : ℕ) (S : finset α) : Prop :=
  ∃ (l1 l2 : list α), C.ngon n l1 l2 ∧ l1.in S ∧ l2.in S