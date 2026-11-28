import OMAStatements.S_oeis_a322859

/-! M. Farrokhi D. G.'s OEIS entry A322859 records the sequence values.
This certificate recomputes the first nontrivial failure of the upper
bound after n = 2 directly from permutations. Credit: @jatin6. -/

namespace OMA.S_oeis_a322859

private theorem counts : a 3 = 4 ∧ a 4 = 14 := by decide

theorem upper_bound_fails_at_four : ¬ a 4 ≤ (4-1) * a (4-1) := by
  change ¬ a 4 ≤ 3 * a 3
  rw [counts.1, counts.2]
  decide

end OMA.S_oeis_a322859

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a322859.main) := by
  intro h
  exact OMA.S_oeis_a322859.upper_bound_fails_at_four (h.2.1 4 (by decide)).2
