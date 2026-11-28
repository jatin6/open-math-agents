import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Choose.Basic

/-!
Sharp bounds for representations by a fixed number of distinct Fibonacci numbers.
The initial encoding is from the A359558 proof, following F. V. Weinstein,
Notes on Fibonacci Partitions, Lemma 1.5. The remaining argument counts
all possible block sizes and realizes them simultaneously at separated indices.
-/

namespace FibonacciExtrema

/-- Index zero denotes 1, index one denotes 2, and higher indices follow the Fibonacci recurrence. -/
def weight (i : ℕ) := Nat.fib (i+2)

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

private def bump : List ℕ → List ℕ
  | [] => []
  | a::l => (a+1)::l

private def cuts : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[1]]
  | 0, _+1 => []
  | k+1, 0 => [[k+2]]
  | k+1, r+1 => ((cuts k r).map (1::·)) ++ ((cuts k (r+1)).map bump)

private theorem cuts_length (k r : ℕ) : (cuts k r).length = k.choose r := by
  induction k generalizing r with
  | zero => cases r <;> simp [cuts]
  | succ k ih => cases r <;> simp [cuts, ih, Nat.choose_succ_succ]

private theorem short (l : List ℕ) (hp : ∀ a ∈ l, 0 < a) : l.length ≤ l.sum := by
  induction l with
  | nil => decide
  | cons a l ih =>
    have ha := hp a (by simp)
    have ht := ih (fun b hb => hp b (by simp [hb]))
    simp only [List.length_cons, List.sum_cons]; omega

private theorem cuts_spec (k r : ℕ) (l : List ℕ) : l ∈ cuts k r ↔
    (∀ a ∈ l, 0 < a) ∧ l.sum = k+1 ∧ l.length = r+1 := by
  induction k generalizing r l with
  | zero =>
    cases r with
    | zero =>
      cases l with
      | nil => simp [cuts]
      | cons a l => cases l <;> (simp [cuts]; try omega)
    | succ r =>
      simp only [cuts, List.not_mem_nil, false_iff]
      rintro ⟨hp, hs, hl⟩
      have := short l hp; omega
  | succ k ih =>
    cases r with
    | zero =>
      cases l with
      | nil => simp [cuts]
      | cons a l => cases l <;> (simp [cuts]; try omega)
    | succ r =>
      simp only [cuts, List.mem_append, List.mem_map]
      constructor
      · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
        · obtain ⟨hp, hs, hl⟩ := (ih r u).mp hu
          simp [hs, hl, Nat.add_comm]; exact hp
        · obtain ⟨hp, hs, hl⟩ := (ih (r+1) u).mp hu
          cases u with
          | nil => simp at hl
          | cons a l =>
            simp only [List.sum_cons, List.length_cons] at hs hl
            have htail := fun b (hb : b ∈ l) => hp b (List.mem_cons_of_mem _ hb)
            refine ⟨?_, ?_, ?_⟩
            · simpa [bump] using htail
            · simp [bump]; omega
            · simpa [bump] using hl
      · rintro ⟨hp, hs, hl⟩
        cases l with
        | nil => simp at hl
        | cons a l =>
          have ha := hp a (by simp)
          have htail := fun b (hb : b ∈ l) => hp b (List.mem_cons_of_mem _ hb)
          simp only [List.sum_cons, List.length_cons] at hl hs
          by_cases h : a = 1
          · subst a; left; exact ⟨l, (ih r l).mpr ⟨htail, by omega, by omega⟩, rfl⟩
          · right
            obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
            refine ⟨a::l, (ih _ _).mpr ⟨?_, ?_, ?_⟩, rfl⟩
            · simpa using (And.intro (show 0 < a by omega) htail)
            · simp; omega
            · simpa using hl

/-- At fixed number r+1 of Zeckendorf summands there are at most (k choose r)
representations with k+1 pieces. Each representation is listed in decreasing order. -/
theorem upper (k r n : ℕ) (hz : n.zeckendorf.length = r+1) (s : Finset (List ℕ))
    (hs : ∀ l ∈ s, l.Pairwise (· > ·) ∧ l.length = k+1 ∧ (l.map weight).sum = n) :
    s.card ≤ k.choose r := by
  have cover : s ⊆ ((cuts k r).map (decode n.zeckendorf)).toFinset := by
    intro l hl
    obtain ⟨ho, hlen, ht⟩ := hs l hl
    obtain ⟨c, hp, hc, hr, hd⟩ := encode n l ho ht
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨c, (cuts_spec _ _ _).mpr ⟨hp, hc.trans hlen, hr.trans hz⟩, hd⟩)
  calc
    s.card ≤ _ := Finset.card_le_card cover
    _ ≤ _ := List.toFinset_card_le _
    _ = _ := by simp [cuts_length]

/-- A large enough gap lets a single part be replaced by any requested number of pieces. -/
private theorem chunk_spec (r i : ℕ) (hi : 2*r ≤ i) :
    (chunk i (r+1)).length = r+1 ∧ total (chunk i (r+1)) = weight i ∧
    (chunk i (r+1)).Pairwise (· > ·) ∧
    ∀ j ∈ chunk i (r+1), j ≤ i ∧ i ≤ j+2*r := by
  induction r generalizing i with
  | zero => simp [chunk, total]
  | succ r ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ i by omega)
    have h := ih t (by omega)
    obtain ⟨hlen, hsum, hsort, hb⟩ := h
    rw [show 2+t = t+2 by omega, chunk]
    simp only [Nat.add_sub_cancel, show t+2-1 = t+1 by omega, List.length_cons,hlen]
    refine ⟨True.intro, ?_, List.pairwise_cons.mpr ⟨?_, hsort⟩, ?_⟩
    · change weight (t+1) + total (chunk t (r+1)) = weight (t+2)
      rw [hsum, step, Nat.add_comm]
    · intro j hj; have := hb j hj; omega
    · intro j hj; rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · have := hb j hj; omega

private def witness (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => weight (B*(m+1)) + witness B m

private def realize (B : ℕ) : List ℕ → List ℕ
  | [] => []
  | a::l => chunk (B*(l.length+1)) a ++ realize B l

private theorem realize_spec (B : ℕ) (l : List ℕ)
    (hp : ∀ a ∈ l, 0 < a ∧ 2*a < B) :
    (realize B l).Pairwise (· > ·) ∧ (realize B l).length = l.sum ∧
    total (realize B l) = witness B l.length ∧ ∀ j ∈ realize B l, j ≤ B*l.length := by
  induction l with
  | nil => simp [realize, total, witness]
  | cons a l ih =>
    have ha := hp a (by simp)
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    obtain ⟨ht, hlen, hsum, hmax⟩ := ih (fun b hb => hp b (by simp [hb]))
    have eb : B*(l.length+1) = B*l.length+B := Nat.mul_add_one ..
    obtain ⟨hc, hv, ho, hbounds⟩ := chunk_spec r (B*(l.length+1)) (by omega)
    simp only [realize, List.length_cons, List.sum_cons, List.length_append, hc, hlen,
      List.pairwise_append, ho, ht, true_and]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi j hj; have := hbounds i hi; have := hmax j hj; omega
    · change ((chunk (B*(l.length+1)) (r+1) ++ realize B l).map weight).sum = _
      simp only [List.map_append,List.sum_append,witness]; exact congrArg₂ (·+·) hv hsum
    · intro i hi; rcases List.mem_append.mp hi with hi | hi
      · exact (hbounds _ hi).1
      · have := hmax i hi; omega

private theorem bump_inj : Function.Injective bump := by
  intro x y h; cases x <;> cases y <;> simp_all [bump]

private theorem cuts_nodup (k r : ℕ) : (cuts k r).Nodup := by
  induction k generalizing r with
  | zero => cases r <;> simp [cuts]
  | succ k ih =>
    cases r with
    | zero => simp [cuts]
    | succ r =>
      apply List.nodup_append'.mpr
      refine ⟨(ih _).map (fun _ _ h => List.cons.inj h |>.2), (ih _).map bump_inj, ?_⟩
      intro x hx hy
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v, hv, eq⟩ := List.mem_map.mp hy
      have hp := ((cuts_spec _ _ _).mp hv).1
      cases v with
      | nil => simp [bump] at eq
      | cons a l => have := hp a (by simp); simp [bump] at eq; omega

private theorem extract (B a : ℕ) (l : List ℕ) (ha : 0 < a ∧ 2*a < B)
    (hp : ∀ b ∈ l, 0 < b ∧ 2*b < B) :
    ((realize B (a::l)).filter (fun j => decide (B*l.length < j))).length = a := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have eb : B*(l.length+1) = B*l.length+B := Nat.mul_add_one ..
  obtain ⟨hlen, _, _, hb⟩ := chunk_spec r (B*(l.length+1)) (by omega)
  have ht := (realize_spec B l hp).2.2.2
  rw [realize, List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr,
    List.append_nil, hlen]
  · intro j hj; have := ht j hj; simp; omega
  · intro j hj; have := hb j hj; simp; omega

private theorem realize_inj (B : ℕ) (xs ys : List ℕ) (hl : xs.length = ys.length)
    (hx : ∀ a ∈ xs, 0 < a ∧ 2*a < B) (hy : ∀ a ∈ ys, 0 < a ∧ 2*a < B)
    (he : realize B xs = realize B ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => symm; apply List.length_eq_zero_iff.mp; simpa using hl.symm
  | cons a xs ih =>
    cases ys with
    | nil => simp at hl
    | cons b ys =>
      have hl' : xs.length = ys.length := by simpa using hl
      have hxs := fun c (hc : c ∈ xs) => hx c (List.mem_cons_of_mem _ hc)
      have hys := fun c (hc : c ∈ ys) => hy c (List.mem_cons_of_mem _ hc)
      have ex := extract B a xs (hx a (by simp)) hxs
      have ey := extract B b ys (hy b (by simp)) hys
      rw [he, hl', ey] at ex
      subst b
      simp only [realize, hl'] at he
      exact congrArg (a::·) (ih ys hl' hxs hys (List.append_cancel_left he))

private theorem le_sum {a : ℕ} {xs : List ℕ} (h : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons b xs ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    · have := ih hm; simp; omega

private def indices (B : ℕ) : ℕ → List ℕ
  | 0 => []
  | m+1 => (B*(m+1)+2) :: indices B m

private theorem witness_digits (B m : ℕ) (hB : 2 ≤ B) :
    (witness B m).zeckendorf.length = m := by
  have hv : ((indices B m).map Nat.fib).sum = witness B m := by
    induction m with
    | zero => rfl
    | succ m ih => simp [indices, witness, weight, ih]
  have hz : (indices B m).IsZeckendorfRep := by
    clear hv
    induction m with
    | zero => exact List.IsZeckendorfRep_nil
    | succ m ih =>
      cases m with
      | zero => simp [indices, List.IsZeckendorfRep]
      | succ m =>
        change List.IsChain _ ((B*(m+1+1)+2)::(B*(m+1)+2)::(indices B m ++ [0]))
        apply List.IsChain.cons_cons _ ih
        have := Nat.mul_add_one B (m+1); omega
  rw [← hv, Nat.zeckendorf_sum_fib hz]
  clear hv hz
  induction m with
  | zero => rfl
  | succ m ih => simpa [indices] using ih

/-- For every composition size the binomial upper bound can be realized at one target. -/
theorem attained (k r : ℕ) : ∃ n : ℕ, n.zeckendorf.length = r+1 ∧
    ∃ s : Finset (List ℕ), s.card = k.choose r ∧
      ∀ l ∈ s, l.Pairwise (· > ·) ∧ l.length = k+1 ∧ (l.map weight).sum = n := by
  let B := 2*(k+1)+2
  let words := (cuts k r).map (realize B)
  have prop (c : List ℕ) (hc : c ∈ cuts k r) : ∀ a ∈ c, 0 < a ∧ 2*a < B := by
    obtain ⟨hp, hs, _⟩ := (cuts_spec _ _ _).mp hc
    intro a ha; have := le_sum ha
    exact ⟨hp a ha, by dsimp [B]; omega⟩
  have nodup : words.Nodup := (cuts_nodup k r).map_on (by
    intro x hx y hy h
    exact realize_inj B x y (((cuts_spec _ _ _).mp hx).2.2.trans
      ((cuts_spec _ _ _).mp hy).2.2.symm) (prop _ hx) (prop _ hy) h)
  refine ⟨witness B (r+1), witness_digits _ _ (by dsimp [B]; omega), words.toFinset, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup nodup]; simp [words, cuts_length]
  · intro l hl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
    obtain ⟨ho, hlen, hsum, _⟩ := realize_spec B c (prop _ hc)
    obtain ⟨_, hcSum, hcLen⟩ := (cuts_spec _ _ _).mp hc
    exact ⟨ho, hlen.trans hcSum, hcLen ▸ hsum⟩

/-- The sharp global maximum at k+1 distinct positive Fibonacci summands. -/
theorem maximum (k : ℕ) : IsGreatest
    {v : ℕ | ∃ (n : ℕ) (s : Finset (List ℕ)), v = s.card ∧
      ∀ l ∈ s, l.Pairwise (· > ·) ∧ l.length = k+1 ∧ (l.map weight).sum = n}
    (k.choose (k/2)) := by
  constructor
  · obtain ⟨n, _, s, hc, hp⟩ := attained k (k/2)
    exact ⟨n, s, hc.symm, hp⟩
  · rintro v ⟨n, s, rfl, hp⟩
    cases h : n.zeckendorf.length with
    | succ r => exact (upper k r n h s hp).trans (Nat.choose_le_middle r k)
    | zero =>
      by_cases hn : s.Nonempty
      · obtain ⟨l, hl⟩ := hn
        obtain ⟨ho, hlen, ht⟩ := hp l hl
        obtain ⟨c, _, hs, hr, _⟩ := encode n l ho ht
        have hc := List.length_eq_zero_iff.mp (hr.trans h)
        simp [hc, hlen] at hs
      · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

end FibonacciExtrema

#print axioms FibonacciExtrema.maximum
