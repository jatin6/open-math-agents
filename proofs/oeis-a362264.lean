import OMAStatements.S_oeis_a362264
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Ring

/-! Put X = 10^(k+3). The root is 16(1+X^16) - (X+...+X^15).
Its square has negative coefficients except in degrees 0, 16 and 32.
Borrowing in base X turns 30 of its lower 32 blocks into blocks with
k leading nines. Both normalized expansions are checked below. -/

namespace SquareBlocks

private structure Block where
  units : ℕ
  tens : ℕ
  hundreds : ℕ
  nines : Bool
  deriving DecidableEq

private def padding (k : ℕ) (b : Bool) :=
  List.replicate k (if b then 9 else 0 : ℕ)

private def word (k : ℕ) (blocks : List Block) (top : List ℕ) : List ℕ :=
  match blocks with
  | [] => top
  | b :: bs => b.units :: b.tens :: b.hundreds :: (padding k b.nines ++ word k bs top)

private def ninesValue (k : ℕ) := Nat.ofDigits 10 (List.replicate k 9)

private theorem nines_succ (k : ℕ) : 10 ^ k = ninesValue k + 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [ninesValue, List.replicate_succ, Nat.ofDigits_cons] at *
    rw [pow_succ, ih]
    omega

private theorem padding_value (k : ℕ) (b : Bool) :
    Nat.ofDigits 10 (padding k b) = if b then ninesValue k else 0 := by
  cases b <;> simp [padding, ninesValue]

private def value (q p : ℕ) (blocks : List Block) (top : ℕ) : ℕ :=
  match blocks with
  | [] => top
  | b :: bs => b.units + 10 * (b.tens + 10 * (b.hundreds +
        10 * ((if b.nines then p else 0) + q * value q p bs top)))

private theorem word_value (k : ℕ) (bs : List Block) (top : List ℕ) :
    Nat.ofDigits 10 (word k bs top) =
      value (10 ^ k) (ninesValue k) bs (Nat.ofDigits 10 top) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [word, value, Nat.ofDigits_cons, Nat.ofDigits_append, padding_value, ih]
    simp [padding]

private theorem word_length (k : ℕ) (bs : List Block) (top : List ℕ) :
    (word k bs top).length = (k+3) * bs.length + top.length := by
  induction bs with
  | nil => simp [word]
  | cons b bs ih =>
    simp only [word, List.length_cons, List.length_append, padding, List.length_replicate,
      ih, Nat.mul_add, Nat.mul_one]
    omega

private def lowSum (bs : List Block) := (bs.map fun b => b.units+b.tens+b.hundreds).sum

private theorem word_sum (k : ℕ) (bs : List Block) (top : List ℕ) :
    (word k bs top).sum = lowSum bs + (bs.filter (·.nines)).length * (k*9) + top.sum := by
  induction bs with
  | nil => simp [word, lowSum]
  | cons b bs ih =>
    cases h : b.nines <;>
      simp [word, padding, lowSum, List.sum_replicate, ih, h, Nat.add_mul, nsmul_eq_mul] <;> omega

private theorem word_valid (k : ℕ) (bs : List Block) (top : List ℕ)
    (hb : ∀ b ∈ bs, b.units < 10 ∧ b.tens < 10 ∧ b.hundreds < 10)
    (ht : ∀ d ∈ top, d < 10) : ∀ d ∈ word k bs top, d < 10 := by
  induction bs with
  | nil => exact ht
  | cons b bs ih =>
    obtain ⟨hu, hv, hw⟩ := hb b (by simp)
    have hr := ih (fun c hc => hb c (by simp [hc]))
    intro d hd
    simp only [word, List.mem_cons, List.mem_append] at hd
    rcases hd with h | h | h | h | h
    · simpa [h] using hu
    · simpa [h] using hv
    · simpa [h] using hw
    · have hd' := (List.mem_replicate.mp h).2
      split at hd' <;> omega
    · exact hr d h

private theorem word_end (k : ℕ) (bs : List Block) (top : List ℕ) :
    ∃ front, word k bs top = front ++ top := by
  induction bs with
  | nil => exact ⟨[], rfl⟩
  | cons b bs ih =>
    obtain ⟨front, h⟩ := ih
    exact ⟨b.units :: b.tens :: b.hundreds :: (padding k b.nines ++ front),
      by simp [word, h, List.append_assoc]⟩

private def rootBlocks : List Block := [
  ⟨6, 1, 0, false⟩, ⟨9, 9, 9, true⟩, ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩,
  ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩,
  ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩,
  ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩, ⟨8, 9, 9, true⟩]
private def rootTop : List ℕ := [5, 1]

private def squareBlocks : List Block := [
  ⟨6, 5, 2, false⟩, ⟨8, 6, 9, true⟩, ⟨8, 6, 9, true⟩, ⟨9, 6, 9, true⟩,
  ⟨0, 7, 9, true⟩, ⟨1, 7, 9, true⟩, ⟨2, 7, 9, true⟩, ⟨3, 7, 9, true⟩,
  ⟨4, 7, 9, true⟩, ⟨5, 7, 9, true⟩, ⟨6, 7, 9, true⟩, ⟨7, 7, 9, true⟩,
  ⟨8, 7, 9, true⟩, ⟨9, 7, 9, true⟩, ⟨0, 8, 9, true⟩, ⟨1, 8, 9, true⟩,
  ⟨6, 2, 5, false⟩, ⟨2, 8, 9, true⟩, ⟨0, 8, 9, true⟩, ⟨9, 7, 9, true⟩,
  ⟨8, 7, 9, true⟩, ⟨7, 7, 9, true⟩, ⟨6, 7, 9, true⟩, ⟨5, 7, 9, true⟩,
  ⟨4, 7, 9, true⟩, ⟨3, 7, 9, true⟩, ⟨2, 7, 9, true⟩, ⟨1, 7, 9, true⟩,
  ⟨0, 7, 9, true⟩, ⟨9, 6, 9, true⟩, ⟨8, 6, 9, true⟩, ⟨7, 6, 9, true⟩]
private def squareTop : List ℕ := [5, 5, 2]

private def root (k : ℕ) := Nat.ofDigits 10 (word k rootBlocks rootTop)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem certificate (y : ℕ) :
    value (y+1) y rootBlocks 15 ^ 2 = value (y+1) y squareBlocks 255 := by
  simp only [value, rootBlocks, squareBlocks, Bool.false_eq_true, if_false, if_true]
  ring

private theorem expansion (k : ℕ) :
    Nat.digits 10 (root k ^ 2) = word k squareBlocks squareTop := by
  have h : root k ^ 2 = Nat.ofDigits 10 (word k squareBlocks squareTop) := by
    unfold root
    rw [word_value, word_value, nines_succ]
    exact certificate _
  rw [h]
  apply Nat.digits_ofDigits _ (by decide)
  · apply word_valid <;> decide
  · obtain ⟨front, hf⟩ := word_end k squareBlocks squareTop
    rw [hf]
    simp [squareTop]

private theorem sizes (k : ℕ) :
    (Nat.digits 10 (root k ^ 2)).length = 32*k+99 ∧
    (Nat.digits 10 (root k ^ 2)).sum = 270*k+658 := by
  rw [expansion, word_length, word_sum]
  change (k + 3) * 32 + 3 = _ ∧ _ = _
  have hl : lowSum squareBlocks + squareTop.sum = 658 := by decide
  have hc : (squareBlocks.filter (·.nines)).length = 30 := by decide
  rw [hc]
  omega

theorem unbounded : ¬ type_of% @OMA.S_oeis_a362264.main := by
  intro h
  let digitsLength := fun n : ℕ => (Nat.digits 10 (n^2)).length
  obtain ⟨bound, hbound⟩ := (h.image digitsLength).bddAbove
  let k := bound + 100
  obtain ⟨hlen, hsum⟩ := sizes k
  have hmem : root k ∈ {n : ℕ | 83 * (Nat.digits 10 (n^2)).length <
      10 * (Nat.digits 10 (n^2)).sum} := by
    change 83 * _ < 10 * _
    rw [hlen, hsum]
    dsimp [k]
    omega
  have hle := hbound (Set.mem_image_of_mem digitsLength hmem)
  change (Nat.digits 10 (root k ^ 2)).length ≤ bound at hle
  rw [hlen] at hle
  dsimp [k] at hle
  omega

end SquareBlocks

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a362264.main) := SquareBlocks.unbounded
