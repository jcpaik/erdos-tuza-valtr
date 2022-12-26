import data.list

variable {α : Type*}

@[simp]
theorem list.init_singleton (a : α) : [a].init = [] := by rw list.init

@[simp]
theorem list.last'_cons_append_cons (a b : α) (l1 l2 : list α) : 
  (a :: (l1 ++ b :: l2)).last' = (b :: l2).last' := 
by revert a; induction l1 with c l1 ih; simp; intro; exact ih c

@[simp]
theorem list.reverse_last' {l : list α} : 
  l.reverse.last' = l.head' := by cases l; simp

@[simp]
theorem list.reverse_head' {l : list α} :
  l.reverse.head' = l.last' := 
begin convert (list.reverse_last').symm, simp end

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