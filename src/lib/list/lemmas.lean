import data.list
import data.finset
import order
import lib.list.defs

variable {α : Type*}

section list_in

variable [decidable_eq α]

protected def list.in_superset {l : list α}
  {S T : finset α} (h : S ⊆ T) : l.in S → l.in T := 
λ l_in_S, finset.subset.trans l_in_S h

@[simp]
theorem list.nil_in {S : finset α} : [].in S := 
  by rw list.in; simp

@[simp]
theorem list.cons_in 
  {a : α} {l : list α} {S : finset α} : 
  (a :: l).in S ↔ a ∈ S ∧ l.in S := 
  by simp [list.in]; exact finset.insert_subset

@[simp]
theorem list.in_append
  {l1 l2 : list α} {S : finset α} : 
  (l1 ++ l2).in S ↔ l1.in S ∧ l2.in S :=
  by simp [list.in]; exact finset.forall_mem_union

@[simp]
theorem list.reverse_in
  {l : list α} {S : finset α} : l.reverse.in S ↔ l.in S :=
by simp [list.in] 

end list_in

@[simp]
theorem list.reverse_last' {l : list α} : 
  l.reverse.last' = l.head' := 
by cases l; simp

@[simp]
theorem list.reverse_head' {l : list α} :
  l.reverse.head' = l.last' := 
begin convert (list.reverse_last').symm, simp end

section mirror

variable [linear_order α]

open order_dual

@[simp] theorem list.nil_mirror : ([] : list α).mirror = [] := rfl

@[simp] theorem list.nil_of_mirror : ([] : list αᵒᵈ).of_mirror = [] := rfl

@[simp] theorem list.of_mirror_mirror {l : list αᵒᵈ} :
  l.of_mirror.mirror = l :=
begin
  induction l with a l ih, simp,
  rw [list.of_mirror, list.mirror]; simp,
  rw [list.of_mirror, list.mirror] at ih; simp at ih,
  exact ih
end

@[simp] theorem list.mirror_length {l : list α} :
  l.mirror.length = l.length := by rw [list.mirror]; simp

theorem list.chain'_mirror {l : list α} :
  list.chain' (<) l ↔ list.chain' (<) l.mirror :=
begin
  rw [list.mirror, list.chain'_reverse, list.chain'_map, flip],
  simp,
end

@[simp]
theorem list.mirror_last' {l : list α} : 
  l.mirror.last' = option.map to_dual l.head' := 
by rw [list.mirror]; cases l; simp; tauto

@[simp]
theorem list.mirror_head' {l : list α} : 
  l.mirror.head' = option.map to_dual l.last' := 
begin 
  rw [list.mirror, list.reverse_head'], 
  -- quick-and-dirty proof
  induction l with a l ih, simp,
  simp, cases l with b l, simp,
  simp, simp at ih, exact ih,
end

@[simp]
theorem list.mirror_in {l : list α} {S : finset α} :
  l.mirror.in (finset.image to_dual S) ↔ l.in S :=
begin
  rw list.mirror, simp, split,
  { simp [list.in, has_subset.subset] },
  { simp [list.in], intro h, exact (λ a : αᵒᵈ,
    begin -- Why do we need to go through all this? 
      intro h', -- Typecheck fails miserably because (αᵒᵈ) is really α
      rw @list.mem_to_finset (αᵒᵈ) at h',
      rw @finset.mem_image α (αᵒᵈ),
      simp at h', cases h' with a' ha', 
      use a', rw ←list.mem_to_finset at ha',
      tauto,
    end ) } 
end

end mirror

@[simp]
theorem list.init_singleton (a : α) : [a].init = [] := by rw list.init

@[simp]
theorem list.last'_cons_append_cons (a b : α) (l1 l2 : list α) : 
  (a :: (l1 ++ b :: l2)).last' = (b :: l2).last' := 
by revert a; induction l1 with c l1 ih; simp; intro; exact ih c

def list.take_head : ∀ {l : list α}, l ≠ [] → 
  Σ' (h1 : α) (t : list α), l = h1 :: t
| [] h := absurd rfl h
| (h1 :: t) _ := ⟨h1, t, rfl⟩

def list.take_head2 : ∀ {l : list α}, 2 ≤ l.length →
  Σ' (h1 h2 : α) (t : list α), l = h1 :: h2 :: t
| [] h := absurd h (of_to_bool_ff rfl)
| [a] h := absurd h (of_to_bool_ff rfl)
| (a :: b :: t) _ := ⟨a, b, t, rfl⟩

def list.take_head3 : ∀ {l : list α}, 3 ≤ l.length →
  Σ' (h1 h2 h3 : α) (t : list α), l = h1 :: h2 :: h3 :: t
| [] h := absurd h (of_to_bool_ff rfl) 
| [a] h := absurd h (of_to_bool_ff rfl)
| [a, b] h := absurd h (of_to_bool_ff rfl)
| (a :: b :: c :: t) _ := ⟨a, b, c, t, rfl⟩

def list.take_last : ∀ {l : list α}, l ≠ [] →
  Σ' (e1 : α) (m : list α), l = m ++ [e1]
| [] h := absurd rfl h
| [a] h := ⟨a, [], rfl⟩
| (a :: b :: rest) _ := 
  let h : b :: rest ≠ [] := λ h, list.no_confusion h in
  let ⟨e1, m', eq_l'⟩ := list.take_last h in 
  ⟨e1, a :: m', congr_arg (list.cons a) eq_l'⟩ 

def list.take_last2 : ∀ {l : list α}, 2 ≤ l.length →
  Σ' (e1 e2 : α) (m : list α), l = m ++ [e1, e2]
| [] h := absurd h (of_to_bool_ff rfl)
| [a] h := absurd h (of_to_bool_ff rfl)
| [a, b] h := ⟨a, b, [], rfl⟩
| (a :: b :: c :: t) _ := 
  let h : 2 ≤ (b :: c :: t).length := 
    (2 : ℕ).le_add_left (list.length t) in
  let ⟨e1, e2, m', eq_l'⟩ := list.take_last2 h in 
  ⟨e1, e2, a :: m', congr_arg (list.cons a) eq_l'⟩

def list.take_last3 : ∀ {l : list α}, 3 ≤ l.length →
  Σ' (e1 e2 e3 : α) (m : list α), l = m ++ [e1, e2, e3]
| [] h := absurd h (of_to_bool_ff rfl)
| [a] h := absurd h (of_to_bool_ff rfl)
| [a, b] h := absurd h (of_to_bool_ff rfl)
| [a, b, c] h := ⟨a, b, c, [], rfl⟩
| (a :: b :: c :: d :: t) _ := 
  let h : 3 ≤ (b :: c :: d :: t).length := 
    (3 : ℕ).le_add_left (list.length t) in
  let ⟨e1, e2, e3, m', eq_l'⟩ := list.take_last3 h in 
  ⟨e1, e2, e3, a :: m', congr_arg (list.cons a) eq_l'⟩