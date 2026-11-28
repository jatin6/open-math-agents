import OMAStatements.S_oeis_a392604
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
A uniform upper bound for Karttunen's carry-free arithmetic derivatives.
The first three primorial columns suffice. If 2, 3 and 5 all divide N,
the residues of N/2, N/3 and N/5 modulo 30 add to at least 15+10+6.
Otherwise count the positive digits in the first missing prime's column.
-/

open OMA.S_oeis_a392604
namespace OMA.PrimorialBound

def cofactor (s : Finset ℕ) (p : ℕ) := (∏ q ∈ s, q) / p

private theorem dvd_cofactor {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p)
    {p r : ℕ} (hp : p ∈ s) (hr : r.Prime) :
    r ∣ cofactor s p ↔ r ∈ s ∧ r ≠ p := by
  have hprod := Finset.prod_erase_mul s id hp
  have hquot : cofactor s p = (s.erase p).prod id := by
    change s.prod id / p = _
    rw [← hprod, id_eq, Nat.mul_div_cancel _ (hs p hp).pos]
  rw [hquot, hr.prime.dvd_finsetProd_iff id]
  constructor
  · rintro ⟨q,hq,hd⟩
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hq
    have heq := (Nat.prime_dvd_prime_iff_eq hr (hs q hm)).mp hd
    exact heq ▸ ⟨hm,hne⟩
  · rintro ⟨hm,hne⟩
    exact ⟨r, Finset.mem_erase.mpr ⟨hne,hm⟩, dvd_rfl⟩

private theorem count_positive {s : Finset ℕ} (small : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ p ∈ s, p ∉ small → 1 ≤ f p) :
    s.card ≤ small.card + ∑ p ∈ s, f p := by
  have a : (s \ small).card ≤ ∑ p ∈ s \ small, f p := by
    calc
      _ = ∑ _p ∈ s \ small, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp =>
        h p (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2
  have b : (∑ p ∈ s \ small, f p) ≤ ∑ p ∈ s, f p :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by intros; omega)
  have c := Finset.card_le_card_sdiff_add_card (s := s) (t := small)
  omega

theorem atMostSixPrimes {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p)
    (hc : ∀ j, (∑ p ∈ s, digit (cofactor s p) j) < radix j) : s.card ≤ 6 := by
  let f := cofactor s
  have h0 : (∑ p ∈ s, f p % 2) < 2 := by
    simpa [digit, radix, place, f] using hc 0
  have h1 : (∑ p ∈ s, f p / 2 % 3) < 3 := by
    simpa [digit, radix, place, f] using hc 1
  have h2 : (∑ p ∈ s, f p / 6 % 5) < 5 := by
    simpa [digit, radix, place, f] using hc 2
  have d2 (p : ℕ) (hp : p ∈ s) : 2 ∣ f p ↔ 2 ∈ s ∧ 2 ≠ p :=
    dvd_cofactor hs hp Nat.prime_two
  have d3 (p : ℕ) (hp : p ∈ s) : 3 ∣ f p ↔ 3 ∈ s ∧ 3 ≠ p :=
    dvd_cofactor hs hp Nat.prime_three
  have d5 (p : ℕ) (hp : p ∈ s) : 5 ∣ f p ↔ 5 ∈ s ∧ 5 ≠ p :=
    dvd_cofactor hs hp Nat.prime_five
  by_cases m2 : 2 ∈ s
  swap
  · have h := count_positive (s := s) ∅ (fun p => f p % 2) (by
      intro p hp _
      have h : ¬ 2 ∣ f p := by simpa [m2] using d2 p hp
      omega)
    simp at h
    omega
  by_cases m3 : 3 ∈ s
  swap
  · have h := count_positive (s := s) {2} (fun p => f p / 2 % 3) (by
      intro p hp hn
      have ne : 2 ≠ p := by simpa [eq_comm] using hn
      have a := (d2 p hp).2 ⟨m2,ne⟩
      have b : ¬ 3 ∣ f p := by simpa [m3] using d3 p hp
      omega)
    simp at h
    omega
  by_cases m5 : 5 ∈ s
  swap
  · have h := count_positive (s := s) {2,3} (fun p => f p / 6 % 5) (by
      intro p hp hn
      have ns : 2 ≠ p ∧ 3 ≠ p := by simpa [eq_comm] using hn
      have a := (d2 p hp).2 ⟨m2,ns.1⟩
      have b := (d3 p hp).2 ⟨m3,ns.2⟩
      have c : ¬ 5 ∣ f p := by simpa [m5] using d5 p hp
      omega)
    simp at h
    omega
  have expand (x : ℕ) : x % 30 = x % 2 + 2 * (x / 2 % 3) + 6 * (x / 6 % 5) := by omega
  have h30 : (∑ p ∈ s, f p % 30) < 30 := by
    simp_rw [expand]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    omega
  have sub : ({2, 3, 5} : Finset ℕ) ⊆ s := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p => f p % 30) sub (by intros; omega)
  simp at h
  have a2 : ¬2 ∣ f 2 := by simpa using d2 2 m2
  have b2 := (d3 2 m2).2 ⟨m3, by decide⟩
  have c2 := (d5 2 m2).2 ⟨m5, by decide⟩
  have a3 := (d2 3 m3).2 ⟨m2, by decide⟩
  have b3 : ¬3 ∣ f 3 := by simpa using d3 3 m3
  have c3 := (d5 3 m3).2 ⟨m5, by decide⟩
  have a5 := (d2 5 m5).2 ⟨m2, by decide⟩
  have b5 := (d3 5 m5).2 ⟨m3, by decide⟩
  have c5 : ¬5 ∣ f 5 := by simpa using d5 5 m5
  have lower (x d r : ℕ) (hd : d ∣ 30) (hr : r ∣ 30) (dx : d ∣ x) (rx : ¬r ∣ x) :
      d ≤ x % 30 := by
    apply Nat.le_of_dvd _ ((Nat.dvd_mod_iff hd).2 dx)
    apply Nat.pos_of_ne_zero
    intro hzero
    apply rx
    exact (Nat.dvd_mod_iff hr).1 (hzero ▸ dvd_zero r)
  have l2 := lower (f 2) 15 2 (by decide) (by decide)
    ((show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd b2 c2) a2
  have l3 := lower (f 3) 10 3 (by decide) (by decide)
    ((show Nat.Coprime 2 5 by decide).mul_dvd_of_dvd_of_dvd a3 c3) b3
  have l5 := lower (f 5) 6 5 (by decide) (by decide)
    ((show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd a5 b5) c5
  omega

theorem atMostSix (k : ℕ) (hk : qualifies k) : k.bitIndices.length ≤ 6 := by
  let l := selected k
  have hn : l.Nodup := Nat.bitIndices_sorted.nodup.map
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective
  have hp : ∀ p ∈ l.toFinset, Nat.Prime p := by
    intro p hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i
  have hprod : l.toFinset.prod id = l.prod := by simpa using List.prod_toFinset id hn
  have h := atMostSixPrimes hp (by
    intro j
    rw [List.sum_toFinset _ hn]
    change (l.map (fun p => digit (l.toFinset.prod id / p) j)).sum < radix j
    rw [hprod]
    exact hk j)
  rw [List.toFinset_card_of_nodup hn] at h
  simpa [l, selected] using h

end OMA.PrimorialBound
