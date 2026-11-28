import OMAStatements.S_oeis_a359558
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.IntervalCases

/-!
Robert Israel conjectured that the maximal number of representations is six.
The block decomposition below is the principle in F. V. Weinstein, "Notes on
Fibonacci Partitions", Lemma 1.5(b,c). We prove the properties we use from the
Fibonacci recurrence. A representation is determined by the numbers of pieces
assigned to the successive Zeckendorf summands. These form a composition of 5.
-/

open OMA.S_oeis_a359558

namespace OMA.FiveFibonacci

private def total (l : List ℕ) := (l.map weight).sum

private theorem pos (j : ℕ) : 0 < weight j := Nat.fib_pos.mpr (by omega)
private theorem step (i : ℕ) : weight (i+2) = weight i + weight (i+1) :=
  Nat.fib_add_two

private theorem total_lt (i : ℕ) (l : List ℕ) (hs : l.Pairwise (· > ·))
    (hb : ∀ j ∈ l, j < i) : total l + 2 ≤ weight (i+1) := by
  induction i generalizing l with
  | zero =>
    cases l with
    | nil => decide
    | cons a l => exact False.elim (Nat.not_lt_zero _ (hb a (by simp)))
  | succ i ih =>
    cases l with
    | nil =>
      exact (show 2 = weight 1 by decide).le.trans (Nat.fib_add_two_strictMono.monotone (by omega))
    | cons a l =>
      obtain ⟨ht, hl⟩ := List.pairwise_cons.mp hs
      have ha := hb a (by simp)
      by_cases e : a = i
      · subst a
        have ht' := ih l hl ht
        simp only [total, List.map_cons, List.sum_cons] at *
        rw [step]
        omega
      · have h' := ih (a::l) hs (by
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hm
          · omega
          · have := ht j hm
            omega)
        exact h'.trans (Nat.fib_add_two_strictMono.monotone (by omega))

/-- The unique possible expansion of Fibonacci number i into r distinct
decreasing parts (invalid input can produce a list that is not a partition). -/
private def chunk (i : ℕ) : ℕ → List ℕ
  | 0 => []
  | 1 => [i]
  | r + 2 => (i-1) :: chunk (i-2) (r+1)

private theorem split (l : List ℕ) (hs : l.Pairwise (· > ·)) (i : ℕ)
    (hb : ∀ j ∈ l, j ≤ i) (h : weight i ≤ total l) :
    ∃ r tail, 0 < r ∧ l = chunk i r ++ tail ∧
      r + tail.length = l.length ∧ weight i + total tail = total l ∧
      tail.Pairwise (· > ·) := by
  induction l generalizing i with
  | nil =>
    simp only [total, List.map_nil, List.sum_nil] at h
    have := pos i
    omega
  | cons a l ih =>
    obtain ⟨ht, hl⟩ := List.pairwise_cons.mp hs
    have ha := hb a (by simp)
    have hv : total (a::l) = weight a + total l := rfl
    by_cases hi : a = i
    · subst a
      exact ⟨1, l, by decide, rfl, by simp [Nat.add_comm], hv.symm, hl⟩
    · cases i with
      | zero => omega
      | succ s =>
        cases s with
        | zero =>
          have ea : a = 0 := by omega
          subst a
          cases l with
          | nil => change 2 ≤ 1 at h; omega
          | cons b l => have := ht b (by simp); omega
        | succ j =>
          have ea : a = j+1 := by
            by_contra e
            have bad := total_lt (j+1) (a::l) hs (by
              intro b hm
              rcases List.mem_cons.mp hm with rfl | hm
              · omega
              · have := ht b hm
                omega)
            omega
          subst a
          have sub : weight j ≤ total l := by
            rw [hv, step] at h
            omega
          obtain ⟨r, tail, hr, hrep, hlen, htot, hsorted⟩ :=
            ih hl j (fun b hm => by have := ht b hm; omega) sub
          obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
          refine ⟨r+2, tail, by omega, ?_, ?_, ?_, hsorted⟩
          · simp [chunk, hrep]
          · simp only [List.length_cons]; omega
          · rw [step, hv]; omega

private def decode (zs counts : List ℕ) : List ℕ :=
  (List.zipWith (fun i r => chunk (i-2) r) zs counts).flatten

private theorem mem_le_total (j : ℕ) (l : List ℕ) (h : j ∈ l) : weight j ≤ total l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    change weight j ≤ weight a + total l
    rcases List.mem_cons.mp h with rfl | hm
    · omega
    · have := ih hm
      omega

private theorem encode (n : ℕ) (l : List ℕ) (hs : l.Pairwise (· > ·)) (ht : total l = n) :
    ∃ counts, (∀ r ∈ counts, 0 < r) ∧ counts.sum = l.length ∧
      counts.length = n.zeckendorf.length ∧ decode n.zeckendorf counts = l := by
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hn : n = 0
    · rw [hn] at ht ⊢
      cases l with
      | nil => exact ⟨[], by simp, rfl, by simp, by simp [decode]⟩
      | cons a l =>
        have hp := pos a
        change weight a + total l = 0 at ht
        omega
    · let g := n.greatestFib
      have hg : 2 ≤ g := Nat.le_greatestFib.mpr (by rw [Nat.fib_two]; omega)
      have hw : weight (g-2) = Nat.fib g := by
        unfold weight
        rw [Nat.sub_add_cancel hg]
      have lower := n.fib_greatestFib_le
      have hb : ∀ j ∈ l, j ≤ g-2 := by
        intro j hj
        have aux := mem_le_total j l hj
        have hle : j+2 ≤ g := Nat.le_greatestFib.mpr (by simpa [weight, ht] using aux)
        omega
      obtain ⟨r, tail, hr, hrep, hlen, htot, hs'⟩ :=
        split l hs (g-2) hb (by rw [ht, hw]; exact lower)
      have hp := pos (g-2)
      rw [hw, ht] at htot
      have hd : n - Nat.fib g < n := by omega
      obtain ⟨counts, hpos, hsum, hlen', he⟩ :=
        ih (n - Nat.fib g) hd tail hs' (by omega)
      refine ⟨r::counts, ?_, ?_, ?_, ?_⟩
      · simpa [hr] using hpos
      · simp [hsum, hlen]
      · rw [Nat.zeckendorf_of_pos (Nat.pos_of_ne_zero hn)]
        simpa [g] using congrArg Nat.succ hlen'
      · rw [Nat.zeckendorf_of_pos (Nat.pos_of_ne_zero hn)]
        change chunk (g-2) r ++ decode (n - Nat.fib g).zeckendorf counts = l
        rw [he, ← hrep]

private def compositions : ℕ → ℕ → List (List ℕ)
  | 0, n => if n = 0 then [[]] else []
  | slots+1, n => (List.range n).flatMap fun i =>
      (compositions slots (n-(i+1))).map (fun tail => (i+1)::tail)

private theorem mem_compositions (l : List ℕ) (hp : ∀ a ∈ l, 0 < a) :
    l ∈ compositions l.length l.sum := by
  induction l with
  | nil => decide
  | cons a l ih =>
    have ha := hp a (by simp)
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    simp only [List.length_cons, List.sum_cons, compositions, List.mem_flatMap,
      List.mem_range, List.mem_map]
    exact ⟨a, by omega, l, by simpa using ih (fun b hb => hp b (by simp [hb])), rfl⟩

private theorem short_of_pos (l : List ℕ) (hp : ∀ a ∈ l, 0 < a) : l.length ≤ l.sum := by
  induction l with
  | nil => decide
  | cons a l ih =>
    have ha := hp a (by simp)
    have ht := ih (fun b hb => hp b (by simp [hb]))
    simp only [List.length_cons, List.sum_cons]
    omega

private theorem bound (n : ℕ) (s : Finset (List ℕ))
    (hs : ∀ l ∈ s, Represents n l) : s.card ≤ 6 := by
  by_cases hnon : s.Nonempty
  · let z := n.zeckendorf
    have cover : s ⊆ ((compositions z.length 5).map (decode z)).toFinset := by
      intro l hl
      obtain ⟨hord, hlen, ht⟩ := hs l hl
      obtain ⟨c, hpos, hsum, hc, hd⟩ := encode n l hord ht
      have hm := mem_compositions c hpos
      rw [hc, hsum, hlen] at hm
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨c, hm, hd⟩)
    obtain ⟨l, hl⟩ := hnon
    obtain ⟨hord, hlen, ht⟩ := hs l hl
    obtain ⟨c, hp, hsum, hc, _⟩ := encode n l hord ht
    have hz : z.length ≤ 5 := by
      have := short_of_pos c hp
      simpa only [hc, hsum, hlen] using this
    have hcount : (compositions z.length 5).length ≤ 6 := by
      generalize z.length = m at hz ⊢
      interval_cases m <;> decide
    calc
      s.card ≤ _ := Finset.card_le_card cover
      _ ≤ ((compositions z.length 5).map (decode z)).length := List.toFinset_card_le _
      _ ≤ 6 := by simpa using hcount
  · simp [Finset.not_nonempty_iff_eq_empty.mp hnon]

end OMA.FiveFibonacci

theorem OMA.solution : type_of% @OMA.S_oeis_a359558.main := OMA.FiveFibonacci.bound
