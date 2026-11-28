import OMAStatements.S_oeis_a392604
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases

/-!
A counterexample to Antti Karttunen's binary-weight conjecture.
The five primes were found by searching allowable column residues. The
binary integer is specified exactly by its five prime indices. No expansion
of its enormous binary representation is needed.
-/

open OMA.S_oeis_a392604

namespace OMA.CarryCounterexample

private abbrev bigPrime : ℕ := 1434164555051

private def modPower (r : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % r
  | t+1, k =>
      let v := modPower r t (k/2)
      (v * v * (if k%2 = 0 then 1 else (2 : ℕ) % r)) % r

private theorem cast_power (r t k : ℕ) (hk : k < 2^t) :
    ((modPower r t k : ℕ) : ZMod r) = ((2 : ℕ) : ZMod r)^k := by
  induction t generalizing k with
  | zero =>
    have h : k = 0 := by simpa using hk
    simp [h, modPower, ZMod.natCast_mod]
  | succ t ih =>
    rw [pow_succ] at hk
    have hh := ih (k / 2) (by omega)
    have he : k = k / 2 * 2 + k % 2 := by omega
    conv_rhs => rw [he, pow_add, pow_mul]
    simp only [modPower, ZMod.natCast_mod, Nat.cast_mul, hh]
    rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with h | h <;>
      simp [h, pow_two, ZMod.natCast_mod]


private theorem power_test (k : ℕ) (hk : k < 2^41) :
    (2 : ZMod bigPrime)^k = 1 ↔ modPower bigPrime 41 k % bigPrime = 1 % bigPrime := by
  have hc := cast_power bigPrime 41 k hk
  norm_num only [Nat.cast_ofNat] at hc
  rw [← hc]
  simpa only [Nat.cast_one] using ZMod.natCast_eq_natCast_iff' (modPower bigPrime 41 k) 1 bigPrime

set_option maxRecDepth 4096 in
private theorem big_prime : bigPrime.Prime := by
  apply lucas_primality bigPrime (2 : ZMod bigPrime)
  · exact (power_test (bigPrime-1) (by decide)).2 (by decide)
  intro q hq hdiv
  have hfac : bigPrime - 1 = 2 * 5 * 5 * 101161 * 283541 := by decide
  rw [hfac] at hdiv
  have h2 : Nat.Prime 2 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h101 : Nat.Prime 101161 := by norm_num
  have h283 : Nat.Prime 283541 := by norm_num
  simp only [Nat.Prime.dvd_mul hq, Nat.prime_dvd_prime_iff_eq hq h2,
    Nat.prime_dvd_prime_iff_eq hq h5, Nat.prime_dvd_prime_iff_eq hq h101,
    Nat.prime_dvd_prime_iff_eq hq h283] at hdiv
  intro heq
  have hk : (bigPrime - 1) / q < 2^41 := lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
  have test := (power_test _ hk).mp heq
  rcases hdiv with (((rfl | rfl) | rfl) | rfl) | rfl <;> revert test <;> decide

private def primes : List ℕ := [2, 3, 541, 3221, bigPrime]
private def indices : List ℕ := primes.map (Nat.count Nat.Prime)
private def witness : ℕ := (indices.map (fun i => 2 ^ i)).sum

private theorem bits : witness.bitIndices = indices := by
  apply Nat.bitIndices_sum_map_two_pow
  have allPrime : ∀ p ∈ primes, Nat.Prime p := by
    simp [primes, Nat.prime_two, Nat.prime_three, big_prime, show Nat.Prime 541 by norm_num, show Nat.Prime 3221 by norm_num]
  have ordered : primes.SortedLT := by decide
  apply List.sortedLT_of_getElem_lt_getElem_of_lt
  intro i j hi hj hij
  simp only [indices, List.getElem_map]
  apply Nat.count_strict_mono (allPrime _ (List.getElem_mem _))
  exact ordered.getElem_lt_getElem_of_lt hij

private theorem selection : selected witness = primes := by
  have h2 := Nat.nth_count (p := Nat.Prime) Nat.prime_two
  have h3 := Nat.nth_count (p := Nat.Prime) Nat.prime_three
  have h541 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 541 by norm_num)
  have h3221 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 3221 by norm_num)
  have hb := Nat.nth_count (p := Nat.Prime) big_prime
  simp only [selected, bits, indices, primes, List.map_cons, List.map_nil, radix,
    h2, h3, h541, h3221, hb]

private theorem radix_pos (j : ℕ) : 0 < radix j :=
  (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j).pos

private theorem place_mono : Monotone place := by
  apply monotone_nat_of_le_succ
  intro j
  exact Nat.le_mul_of_pos_right _ (radix_pos j)

private theorem rad0 : radix 0 = 2 := by
  change Nat.nth Nat.Prime 0 = _
  rw [show (0:ℕ) = Nat.count Nat.Prime 2 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad1 : radix 1 = 3 := by
  change Nat.nth Nat.Prime 1 = _
  rw [show (1:ℕ) = Nat.count Nat.Prime 3 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad2 : radix 2 = 5 := by
  change Nat.nth Nat.Prime 2 = _
  rw [show (2:ℕ) = Nat.count Nat.Prime 5 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad3 : radix 3 = 7 := by
  change Nat.nth Nat.Prime 3 = _
  rw [show (3:ℕ) = Nat.count Nat.Prime 7 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad4 : radix 4 = 11 := by
  change Nat.nth Nat.Prime 4 = _
  rw [show (4:ℕ) = Nat.count Nat.Prime 11 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad5 : radix 5 = 13 := by
  change Nat.nth Nat.Prime 5 = _
  rw [show (5:ℕ) = Nat.count Nat.Prime 13 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad6 : radix 6 = 17 := by
  change Nat.nth Nat.Prime 6 = _
  rw [show (6:ℕ) = Nat.count Nat.Prime 17 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad7 : radix 7 = 19 := by
  change Nat.nth Nat.Prime 7 = _
  rw [show (7:ℕ) = Nat.count Nat.Prime 19 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad8 : radix 8 = 23 := by
  change Nat.nth Nat.Prime 8 = _
  rw [show (8:ℕ) = Nat.count Nat.Prime 23 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad9 : radix 9 = 29 := by
  change Nat.nth Nat.Prime 9 = _
  rw [show (9:ℕ) = Nat.count Nat.Prime 29 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad10 : radix 10 = 31 := by
  change Nat.nth Nat.Prime 10 = _
  rw [show (10:ℕ) = Nat.count Nat.Prime 31 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad11 : radix 11 = 37 := by
  change Nat.nth Nat.Prime 11 = _
  rw [show (11:ℕ) = Nat.count Nat.Prime 37 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad12 : radix 12 = 41 := by
  change Nat.nth Nat.Prime 12 = _
  rw [show (12:ℕ) = Nat.count Nat.Prime 41 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad13 : radix 13 = 43 := by
  change Nat.nth Nat.Prime 13 = _
  rw [show (13:ℕ) = Nat.count Nat.Prime 43 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad14 : radix 14 = 47 := by
  change Nat.nth Nat.Prime 14 = _
  rw [show (14:ℕ) = Nat.count Nat.Prime 47 by decide]
  exact Nat.nth_count (by norm_num)

private theorem rad15 : radix 15 = 53 := by
  change Nat.nth Nat.Prime 15 = _
  rw [show (15:ℕ) = Nat.count Nat.Prime 53 by decide]
  exact Nat.nth_count (by norm_num)

private theorem place1 : place 1 = 2 := by
  change place 0 * radix 0 = _
  rw [show place 0 = 1 by rfl, rad0]

private theorem place2 : place 2 = 6 := by
  change place 1 * radix 1 = _
  rw [place1, rad1]

private theorem place3 : place 3 = 30 := by
  change place 2 * radix 2 = _
  rw [place2, rad2]

private theorem place4 : place 4 = 210 := by
  change place 3 * radix 3 = _
  rw [place3, rad3]

private theorem place5 : place 5 = 2310 := by
  change place 4 * radix 4 = _
  rw [place4, rad4]

private theorem place6 : place 6 = 30030 := by
  change place 5 * radix 5 = _
  rw [place5, rad5]

private theorem place7 : place 7 = 510510 := by
  change place 6 * radix 6 = _
  rw [place6, rad6]

private theorem place8 : place 8 = 9699690 := by
  change place 7 * radix 7 = _
  rw [place7, rad7]

private theorem place9 : place 9 = 223092870 := by
  change place 8 * radix 8 = _
  rw [place8, rad8]

private theorem place10 : place 10 = 6469693230 := by
  change place 9 * radix 9 = _
  rw [place9, rad9]

private theorem place11 : place 11 = 200560490130 := by
  change place 10 * radix 10 = _
  rw [place10, rad10]

private theorem place12 : place 12 = 7420738134810 := by
  change place 11 * radix 11 = _
  rw [place11, rad11]

private theorem place13 : place 13 = 304250263527210 := by
  change place 12 * radix 12 = _
  rw [place12, rad12]

private theorem place14 : place 14 = 13082761331670030 := by
  change place 13 * radix 13 = _
  rw [place13, rad13]

private theorem place15 : place 15 = 614889782588491410 := by
  change place 14 * radix 14 = _
  rw [place14, rad14]

private theorem place16 : place 16 = 32589158477190044730 := by
  change place 15 * radix 15 = _
  rw [place15, rad15]

set_option maxRecDepth 4096 in
private theorem no_carries : qualifies witness := by
  intro j
  rw [selection]
  by_cases small : j < 16
  · interval_cases j <;>
      simp only [primes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.prod_cons, List.prod_nil, digit, rad0, rad1, rad2, rad3, rad4, rad5, rad6, rad7, rad8, rad9, rad10, rad11, rad12, rad13, rad14, rad15, place1, place2, place3, place4, place5, place6, place7, place8, place9, place10, place11, place12, place13, place14, place15, show place 0 = 1 by rfl, bigPrime] <;> decide
  · have hbound := place_mono (a := 16) (b := j) (by omega)
    rw [place16] at hbound
    have allZero (p : ℕ) : digit (primes.prod / p) j = 0 := by
      have h : primes.prod / p ≤ primes.prod := Nat.div_le_self _ _
      have bound : primes.prod < 32589158477190044730 := by decide
      simp [digit, Nat.div_eq_of_lt (lt_of_le_of_lt h (lt_of_lt_of_le bound hbound))]
    have hz : primes.map (fun p => digit (primes.prod / p) j) = primes.map (fun _ => (0 : ℕ)) :=
      List.map_congr_left fun p _ => allZero p
    rw [hz]
    simpa [primes] using radix_pos j

end OMA.CarryCounterexample

open OMA.CarryCounterexample in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a392604.main) := by
  intro claim
  have h := claim witness no_carries
  rw [bits] at h
  change 5 ≤ 4 at h
  omega
