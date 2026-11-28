import OMAStatements.S_oeis_a394432
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.RingTheory.Fintype
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
A separate conjecture in Jianing Song's A394432 concerns powers of two.
Equality of the threshold would force 2 itself to have order e³. We exhibit
an eligible modulus at most e³ using powers of 3 or 5, with small exceptions.
-/

open OMA.S_oeis_a394432

namespace OMA.A394432

private def idx (p e : ℕ) := Nat.log p (e^3) - 1

private def enough (p e : ℕ) : Prop :=
  p^(idx p e+1) ≤ e^3 ∧ e^2 ≤ p^(idx p e) / Nat.gcd (p^(idx p e)) e

private instance (p e : ℕ) : Decidable (enough p e) := by unfold enough; infer_instance

private theorem powers (p e : ℕ) (hp : 1 < p) (hle : p ≤ e^3) :
    p^(idx p e+1) ≤ e^3 ∧ e^3 < (p^(idx p e)) * p^2 := by
  have hpos : 0 < Nat.log p (e^3) := Nat.log_pos hp hle
  have hidx : idx p e+1 = Nat.log p (e^3) := by unfold idx; omega
  constructor
  · rw [hidx]
    exact Nat.pow_log_le_self _ (by omega)
  · rw [← pow_add, show idx p e+2 = Nat.log p (e^3)+1 by omega]
    apply Nat.lt_pow_of_log_lt hp
    omega

private theorem costly (p e : ℕ) (hp : 1 < p) (hle : p ≤ e^3) (h : ¬enough p e) :
    e < p^2 * Nat.gcd (p^(idx p e)) e := by
  obtain ⟨hl, hu⟩ := powers p e hp hle
  let v := p^(idx p e)
  let g := Nat.gcd v e
  have hn : v / g < e^2 := by by_contra! hh; exact h ⟨hl, hh⟩
  have hv : v ≤ e^2 * g := by
    calc
      v = v / g * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left v e)).symm
      _ ≤ _ := Nat.mul_le_mul_right g hn.le
  by_contra! small
  exact (not_lt_of_ge (calc
    v * p ^ 2 ≤ (e^2 * g) * p^2 := Nat.mul_le_mul_right _ hv
    _ = e^2 * (p^2 * g) := by ac_rfl
    _ ≤ e^2 * e := Nat.mul_le_mul_left _ small
    _ = e^3 := by ring)) hu

private theorem large {e : ℕ} (he : 225 ≤ e) : enough 3 e ∨ enough 5 e := by
  by_contra! hf
  obtain ⟨a,b⟩ := hf
  have big : 5 ≤ e^3 := by calc
    5 ≤ 225^3 := by decide
    _ ≤ e^3 := Nat.pow_le_pow_left he _
  have h3 := costly 3 e (by decide) (by omega) a
  have h5 := costly 5 e (by decide) big b
  let g := Nat.gcd (3^(idx 3 e)) e
  let j := Nat.gcd (5^(idx 5 e)) e
  change e < 9*g at h3
  change e < 25*j at h5
  have cp : Nat.Coprime g j := Nat.Coprime.of_dvd (Nat.gcd_dvd_left _ _)
    (Nat.gcd_dvd_left _ _) (((by decide : Nat.Coprime 3 5).pow_left _).pow_right _)
  have prod : g*j ≤ e := Nat.le_of_dvd (by omega)
    (cp.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
  have impossible : e*e < (9*g)*(25*j) := Nat.mul_lt_mul_of_lt_of_le h3 h5.le (by omega)
  nlinarith [Nat.mul_le_mul_right e he, Nat.mul_le_mul_left 225 prod]

private def eligible (e r : ℕ) : Prop :=
  0 < r ∧ (2^e).Coprime r ∧ e^2 ≤ orderOf ((2:ZMod r)^e)

private theorem primePower {e p d : ℕ} (he : 1 < e) (hp : 0 < p) (hd : 0 < d)
    (hc : Nat.Coprime 2 p) (ok : enough p e)
    (ord : ∀ a : ℕ, orderOf ((2 : ZMod (p^(a+1)))^d) = p^a) :
    ∃ r, eligible e r ∧ r ≤ e^3 := by
  let a := idx p e
  let r := p^(a+1)
  have hlo : orderOf (((2:ZMod r)^e)^d) = p^a / Nat.gcd (p^a) e := by
    rw [← pow_mul, Nat.mul_comm e d, pow_mul, orderOf_pow' _ (by omega : e ≠ 0), ord a]
  have hle : orderOf (((2:ZMod r)^e)^d) ≤ orderOf ((2:ZMod r)^e) := by
    rw [orderOf_pow' _ hd.ne']
    exact Nat.div_le_self _ _
  exact ⟨r, ⟨pow_pos hp _, (hc.pow_left e).pow_right _, ok.2.trans (hlo ▸ hle)⟩, ok.1⟩

private theorem base3 (a : ℕ) : orderOf ((2 : ZMod (3^(a+1)))^2) = 3^a := by
  convert ZMod.orderOf_one_add_prime Nat.prime_three (by decide) a using 1
  norm_num

private theorem base5 (a : ℕ) : orderOf ((2 : ZMod (5^(a+1)))^4) = 5^a := by
  convert ZMod.orderOf_one_add_mul_prime (by decide : Nat.Prime 5) (by decide) 3 (by decide) a using 1
  norm_num

private theorem equal_order {M : Type*} [Monoid M] (x : M) {e : ℕ} (he : 1 < e)
    (h : orderOf (x^e) = e^2) : orderOf x = e^3 := by
  have hd : e ∣ orderOf x := (dvd_pow_self e (by decide : 2 ≠ 0)).trans
    (h ▸ orderOf_pow_dvd (x := x) e)
  have q := orderOf_pow_of_dvd (x := x) (by omega : e ≠ 0) hd
  calc
    orderOf x = orderOf x / e * e := (Nat.div_mul_cancel hd).symm
    _ = e^2 * e := by rw [← q, h]
    _ = e^3 := by ring


private theorem test_order {M : Type*} [Monoid M] (x : M) {d : ℕ} (hd : 0 < d)
    (full : x^d = 1) (short : ∀ i : Fin d, 0 < i.val → x^i.val ≠ 1) :
    orderOf x = d :=
  (orderOf_eq_iff hd).mpr ⟨full, fun m hm hp => short ⟨m,hm⟩ hp⟩

set_option maxRecDepth 4096 in
private theorem small2 : eligible 2 11 := by
  have h := test_order ((2 : ZMod 11)^2) (d := 5) (by decide) (by decide +kernel) (by decide +kernel)
  exact ⟨by decide, by decide, h.ge.trans' (by decide : 2^2 ≤ 5)⟩

set_option maxRecDepth 4096 in
private theorem small3 : eligible 3 11 := by
  have h := test_order ((2 : ZMod 11)^3) (d := 10) (by decide) (by decide +kernel) (by decide +kernel)
  exact ⟨by decide, by decide, h.ge.trans' (by decide : 3^2 ≤ 10)⟩

set_option maxRecDepth 4096 in
private theorem small4 : eligible 4 47 := by
  have h := test_order ((2 : ZMod 47)^4) (d := 23) (by decide) (by decide +kernel) (by decide +kernel)
  exact ⟨by decide, by decide, h.ge.trans' (by decide : 4^2 ≤ 23)⟩

set_option maxRecDepth 4096 in
private theorem small6 : eligible 6 83 := by
  have h := test_order ((2 : ZMod 83)^6) (d := 41) (by decide) (by decide +kernel) (by decide +kernel)
  exact ⟨by decide, by decide, h.ge.trans' (by decide : 6^2 ≤ 41)⟩

set_option maxRecDepth 4096 in
private theorem small12 : eligible 12 311 := by
  have h := test_order ((2 : ZMod 311)^12) (d := 155) (by decide) (by decide +kernel) (by decide +kernel)
  exact ⟨by decide, by decide, h.ge.trans' (by decide : 12^2 ≤ 155)⟩

private theorem small_table : ∀ t : Fin 225, t.val ≤ 1 ∨ t.val = 2 ∨ t.val = 3 ∨
    t.val = 4 ∨ t.val = 6 ∨ t.val = 12 ∨ enough 3 t.val ∨ enough 5 t.val := by
  decide +kernel

private theorem bounded {e : ℕ} (he : 2 < e) : ∃ r, eligible e r ∧ r ≤ e^3 := by
  have build : enough 3 e ∨ enough 5 e → ∃ r, eligible e r ∧ r ≤ e^3 := by
    rintro (h | h)
    · exact primePower (by omega) (by decide) (by decide : 0 < 2) (by decide) h base3
    · exact primePower (by omega) (by decide) (by decide : 0 < 4) (by decide) h base5
  by_cases big : 225 ≤ e
  · exact build (large big)
  obtain h | h | h | h | h | h | h := small_table ⟨e, by omega⟩
  · change e ≤ 1 at h
    omega
  · change e = 2 at h
    omega
  · change e = 3 at h
    subst e
    exact ⟨_, small3, by decide⟩
  · change e = 4 at h
    subst e
    exact ⟨_, small4, by decide⟩
  · change e = 6 at h
    subst e
    exact ⟨_, small6, by decide⟩
  · change e = 12 at h
    subst e
    exact ⟨_, small12, by decide⟩
  · exact build h

private theorem qualify_iff (e r : ℕ) :
    eligible e r ↔ 0 < r ∧ (2^e).Coprime r ∧
      threshold (2^e) ≤ (orderOf (((2^e : ℕ):ZMod r)) : ℝ) := by
  unfold eligible threshold
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one]
  norm_cast

theorem strictAtPowersOfTwo : StrictAtPowersOfTwo := by
  classical
  intro e he
  have existsGood : ∃ r, eligible e r := by
    by_cases h : e = 2
    · subst e
      exact ⟨_, small2⟩
    · obtain ⟨r, hr, _⟩ := bounded (by omega : 2 < e)
      exact ⟨r, hr⟩
  let r := Nat.find existsGood
  have hr : eligible e r := Nat.find_spec existsGood
  have least : ∀ s, eligible e s → r ≤ s := fun s h => Nat.find_min' existsGood h
  refine ⟨r, ⟨(qualify_iff e r).mp hr, fun s hs => least s ((qualify_iff e s).mpr hs)⟩, ?_, ?_⟩
  · push_cast
    exact orderOf_pow' _ (by omega)
  · push_cast
    refine lt_of_le_of_ne hr.2.2 ?_
    intro h
    have hbase := equal_order (2:ZMod r) he h.symm
    have hpos := hr.1
    by_cases h2 : e = 2
    · subst e
      have ub := least 11 small2
      have every : ∀ i : Fin 12, 0 < i.val → (4:ℕ).Coprime i.val →
          (2^60:ℕ) % i.val = 1 % i.val := by decide +kernel
      have per := every ⟨r, by omega⟩ hpos hr.2.1
      have eq : (2 : ZMod r)^60 = 1 := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
          (ZMod.natCast_eq_natCast_iff' (2^60) 1 r).mpr per
      have dv := orderOf_dvd_of_pow_eq_one eq
      rw [hbase] at dv
      exact (by decide : ¬ 2^3 ∣ 60) dv
    · obtain ⟨s, hs, hu⟩ := bounded (by omega : 2 < e)
      have ub := (least s hs).trans hu
      by_cases trivial : r = 1
      · rw [trivial] at hbase
        have hone : (2:ZMod 1) = 1 := Subsingleton.elim _ _
        rw [hone, orderOf_one] at hbase
        have := Nat.pow_le_pow_left (show 2 ≤ e by omega) 3
        omega
      · have small := ZMod.orderOf_lt (by omega : 1 < r) (2:ZMod r)
        omega

end OMA.A394432
