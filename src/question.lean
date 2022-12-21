example (l : list ℕ) (a : ℕ) ()

section find
parameter {p : ℕ → Prop}

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k ≤ n, ¬p k

parameters [decidable_pred p] (H : ∃n, p n)

private def wf_lbp : well_founded lbp :=
⟨let ⟨n, pn⟩ := H in
suffices ∀m k, n ≤ k + m → acc lbp k, from λa, this _ _ (nat.le_add_left _ _),
λm, nat.rec_on m
  (λk kn, ⟨_, λy r, match y, r with ._, ⟨rfl, a⟩ := absurd pn (a _ kn) end⟩)
  (λm IH k kn, ⟨_, λy r, match y, r with ._, ⟨rfl, a⟩ := IH _ (by rw nat.add_right_comm; exact kn) end⟩)⟩

protected def find_x : {n // p n ∧ ∀m < n, ¬p m} :=
@well_founded.fix _ (λk, (∀n < k, ¬p n) → {n // p n ∧ ∀m < n, ¬p m}) lbp wf_lbp
(λm IH al, if pm : p m then ⟨m, pm, al⟩ else
    have ∀ n ≤ m, ¬p n, from λn h, or.elim (decidable.lt_or_eq_of_le h) (al n) (λe, by rw e; exact pm),
    IH _ ⟨rfl, this⟩ (λn h, this n $ nat.le_of_succ_le_succ h))
0 (λn h, absurd h (nat.not_lt_zero _))

end find