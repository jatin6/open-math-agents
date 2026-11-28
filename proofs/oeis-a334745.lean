import OMAStatements.S_oeis_a334745
import Mathlib.Tactic.Ring

namespace OMA.S_oeis_a334745

private theorem adjacentAbs (f : ℕ → ℕ) (z : ℤ) :
    f (z-1).natAbs + f (z+1).natAbs =
      f (z.natAbs+1) + f (if z.natAbs = 0 then 1 else z.natAbs-1) := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [show Int.ofNat (n+1) - 1 = Int.ofNat n by change (↑n + 1 : ℤ) - 1 = ↑n; omega]
      change f n + f (n+2) = f (n+2) + f n
      exact Nat.add_comm _ _
  | negSucc n =>
    cases n <;> rfl

private def bin (r a b : ℕ) := if a+b = r then r.choose a else 0

private theorem wave_bin (r : ℕ) (u v : ℤ) : wave r u v = bin r u.natAbs v.natAbs := by
  induction r generalizing u v with
  | zero =>
    simp [wave, bin, Nat.add_eq_zero_iff, Int.natAbs_eq_zero]
    split <;> simp_all
  | succ r ih =>
    rw [wave]
    split
    next h =>
      simp only [ih]
      rw [Nat.add_assoc (bin r (u-1).natAbs v.natAbs + _)]
      rw [adjacentAbs (fun a => bin r a v.natAbs) u, adjacentAbs (bin r u.natAbs) v]
      generalize u.natAbs = a at *
      generalize v.natAbs = b at *
      cases a <;> cases b <;> simp_all [bin, Nat.choose_succ_succ'] <;> (repeat' split) <;> (try simp_all) <;> omega
    next h => simp [bin, h]


private def oddForm (r : ℕ) :=
  ∀ j, j < 2*r+1 → table (2*r+1) j =
    if j < r then r.choose j else (r+1).choose (j-r)

private def evenForm (r : ℕ) :=
  ∀ j, j < 2*r → table (2*r) j =
    if j < r then r.choose j else r.choose (j-r)

private theorem nextEven (r : ℕ) (old : oddForm r) : evenForm (r+1) := by
  intro j hj
  have left (k : ℕ) (hk : k ≤ r) : table (2*r+1) k = r.choose k := by
    rw [old k (by omega)]
    split
    · rfl
    · have : k = r := by omega
      simp [this]
  have pascal (k : ℕ) (hk : k < r+1) :
      (if k=0 then 1 else table (2*r+1) (k-1) + table (2*r+1) k) = (r+1).choose k := by
    cases k with
    | zero => simp
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
      rw [left k (by omega), left (k+1) (by omega), Nat.choose_succ_succ]
  rw [show 2*(r+1) = (2*r+1)+1 by omega, table]
  dsimp only
  by_cases h0 : j=0
  · subst j
    simp
  by_cases he : j+1 = 2*r+1+1
  · have hj' : j - (r+1) = r := by omega
    simp [h0, he, hj', if_neg (show ¬ j < r+1 by omega), Nat.choose_succ_self_right]
    omega
  · simp only [if_neg h0, if_neg he, show (2*r+1+1)%2 ≠ 1 by omega, if_false,
      show (2*r+1+1)/2 = r+1 by omega]
    split
    · simpa [h0] using pascal j (by omega)
    · exact pascal _ (by omega)

private theorem nextOdd (r : ℕ) (old : evenForm (r+1)) : oddForm (r+1) := by
  intro j hj
  rw [table]
  dsimp only
  by_cases h0 : j=0
  · subst j
    simp
  by_cases he : j+1 = 2*(r+1)+1
  · have hj' : j - (r+1) = r+1 := by omega
    simp [h0, he, hj', if_neg (show ¬ j < r+1 by omega), Nat.choose_succ_self_right]
    omega
  · simp only [if_neg h0, if_neg he, show (2*(r+1)+1)%2 = 1 by omega, if_true,
      show (2*(r+1)+1)/2 = r+1 by omega]
    by_cases hl : j ≤ r+1
    · rw [if_pos hl, old j (by omega)]
      split
      · rfl
      · have : j = r+1 := by omega
        simp [this]
    · rw [if_neg hl, old (j-1) (by omega), old j (by omega)]
      simp only [if_neg (show ¬ j-1 < r+1 by omega), if_neg (show ¬ j < r+1 by omega)]
      rw [show j-(r+1) = (j-1-(r+1))+1 by omega]
      exact (Nat.choose_succ_succ' _ _).symm

private theorem tableForms (r : ℕ) : oddForm r ∧ evenForm r := by
  induction r with
  | zero =>
    constructor
    · intro j h
      have : j = 0 := by omega
      subst j
      decide
    · intro j h
      omega
  | succ r ih =>
    exact ⟨nextOdd r (nextEven r ih.1), nextEven r ih.1⟩


private def block (r : ℕ) := (List.range r).map (r.choose ·)
private def tailBlock (r : ℕ) := (List.range r).map fun j => r.choose (j+1)

private theorem shiftBlock (r : ℕ) : 1 :: tailBlock r = block r ++ [1] := by
  have h : (List.range (r+1)).map (r.choose ·) = block r ++ [1] := by
    rw [List.range_succ, List.map_append]
    simp [block]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map] at h
  simpa [tailBlock, Function.comp_def] using h

private theorem twoBlocks (p q : ℕ) (f : ℕ → ℕ)
    (hf : ∀ j, j < p+q → f j = if j < p then p.choose j else q.choose (j-p)) :
    (List.range (p+q)).map f = block p ++ block q := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have h := List.mem_range.mp hj
    simpa [h] using hf j (by omega)
  · apply List.map_congr_left
    intro j hj
    have h := List.mem_range.mp hj
    simpa [Function.comp_def] using hf (p+j) (by omega)

private theorem oddRow (r : ℕ) :
    (List.range (2*r+1)).map (table (2*r+1)) = block r ++ block (r+1) := by
  have H := twoBlocks r (r+1) (table (2*r+1)) (fun j h => (tableForms r).1 j (by omega))
  rwa [show r+(r+1) = 2*r+1 by omega] at H

private theorem evenRow (r : ℕ) :
    (List.range (2*r)).map (table (2*r)) = block r ++ block r := by
  have H := twoBlocks r r (table (2*r)) (fun j h => (tableForms r).2 j (by omega))
  rwa [show r+r = 2*r by omega] at H

private def bulk : ℕ → List ℕ
  | 0 => []
  | r+1 => bulk r ++ block (r+1) ++ block (r+1) ++ block (r+1) ++ block (r+1)

private theorem rows_bulk (r : ℕ) : rows (2*r+1) = bulk r ++ block (r+1) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [rows, oddRow, show rows (2*(r+1)) =
       rows (2*r+1) ++ (List.range (2*(r+1))).map (table (2*(r+1))) by
          rw [show 2*(r+1) = (2*r+1)+1 by omega, rows], evenRow, ih]
    simp only [bulk, List.append_assoc]

private theorem edge_tail (r : ℕ) (q : ℤ → ℤ → ℕ)
    (h : ∀ a b : ℕ, a+b=r → q a b = r.choose a) : edge r q = tailBlock r := by
  apply List.map_congr_left
  intro j hj
  have := List.mem_range.mp hj
  exact h _ _ (by omega)

private theorem all_edges (r : ℕ) :
    edge r (wave r) = tailBlock r ∧
    edge r (fun u v => wave r v (-u)) = tailBlock r ∧
    edge r (fun u v => wave r (-u) (-v)) = tailBlock r ∧
    edge r (fun u v => wave r (-v) u) = tailBlock r := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply edge_tail <;> intro a b h <;>
    simp [wave_bin, bin, Nat.add_comm b a, h] <;> exact Nat.choose_symm_of_eq_add (by omega)

private theorem spiral_bulk (r : ℕ) : spiral r = bulk r ++ [1] := by
  induction r with
  | zero => rfl
  | succ r ih =>
    obtain ⟨a,b,c,d⟩ := all_edges (r+1)
    rw [spiral, a, b, c, d, ih]
    have h := shiftBlock (r+1)
    change [1] ++ tailBlock (r+1) = _ at h
    simp only [bulk, List.append_assoc]
    repeat rw [← List.append_assoc [1], h, List.append_assoc]
    rw [h]

theorem prefix_identity (r : ℕ) : (spiral r).IsPrefix (rows (2*r+1)) := by
  rw [spiral_bulk, rows_bulk]
  unfold block
  rw [List.range_succ_eq_map, List.map_cons, Nat.choose_zero_right]
  exact ⟨_, List.append_assoc _ _ _⟩


end OMA.S_oeis_a334745

theorem OMA.solution : type_of% @OMA.S_oeis_a334745.main :=
  OMA.S_oeis_a334745.prefix_identity
