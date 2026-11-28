import OMAStatements.S_oeis_a394432
import Mathlib.RingTheory.Fintype
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
For Jianing Song's OEIS A394432, the least modulus at 45087951844967 is 7^4.
The threshold is bounded using integer powers. Each smaller coprime modulus
above the automatic size bound has a certified exponent witnessing a short
order. The table uses zero for moduli not coprime to the input.
-/

open OMA.S_oeis_a394432

namespace OMA.A394432

private abbrev input : ℕ := 45087951844967

set_option maxRecDepth 4096 in
private theorem threshold_bounds : 2052 < threshold input ∧ threshold input < 2058 := by
  have loN : (2:ℕ)^136 < input^3 := by norm_num [input]
  have hiN : input^11 < (2:ℕ)^499 := by
    rw [show 499 = 249 + 250 by decide, pow_add]
    norm_num [input]
  have loR : (2:ℝ)^136 < (input:ℝ)^3 := by exact_mod_cast loN
  have hiR : (input:ℝ)^11 < (2:ℝ)^499 := by exact_mod_cast hiN
  have hl := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) loR
  have hu := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hiR
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hl hu
  norm_num only [Nat.cast_ofNat, mul_one] at hl hu
  let x := Real.logb 2 (input:ℝ)
  change (136:ℝ) < 3*x at hl
  change 11*x < (499:ℝ) at hu
  change 2052 < x^2 ∧ x^2 < 2058
  have xpos : 0 ≤ x := by linarith
  have above : (136:ℝ)/3 < x := by linarith
  have under : x < (499:ℝ)/11 := by linarith
  constructor
  · have h := mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 136/3) above
    nlinarith only [h]
  · have h := mul_self_lt_mul_self xpos under
    nlinarith only [h]

private def modPower (r : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % r
  | t+1, k =>
      let v := modPower r t (k/2)
      (v * v * (if k%2 = 0 then 1 else input % r)) % r

private theorem cast_power (r t k : ℕ) (hk : k < 2^t) :
    ((modPower r t k : ℕ) : ZMod r) = (input : ZMod r)^k := by
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

private theorem mod_test (r k : ℕ) (hk : k < 4096) :
    (input : ZMod r)^k = 1 ↔ modPower r 12 k % r = 1 % r := by
  rw [← cast_power r 12 k hk]
  simpa only [Nat.cast_one] using ZMod.natCast_eq_natCast_iff' (modPower r 12 k) 1 r

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem at_2401 : orderOf (input : ZMod 2401) = 2058 := by
  apply (orderOf_eq_iff (by decide : 0 < 2058)).mpr
  constructor
  · exact (mod_test 2401 2058 (by decide)).mpr (by decide +kernel)
  · have tests : ∀ k : Fin 2058, 0 < k.val → modPower 2401 12 k.val % 2401 ≠ 1 % 2401 := by
      decide +kernel
    intro k hk hp
    exact fun hh => tests ⟨k,hk⟩ hp ((mod_test 2401 k (by omega)).mp hh)

private def exponents : Array ℕ := #[
  2052, 52, 68, 64, 80, 294, 140, 204, 228, 1030, 1031, 42, 348, 258,
  52, 0, 517, 132, 36, 12, 690, 240, 820, 86, 330, 173, 90, 4,
  1040, 346, 1041, 104, 276, 444, 1043, 84, 1044, 180, 80, 174, 132, 348,
  836, 130, 696, 262, 1049, 60, 95, 42, 100, 262, 20, 108, 42, 80,
  36, 420, 1055, 40, 192, 30, 0, 506, 504, 352, 108, 52, 300, 1060,
  120, 174, 400, 177, 118, 18, 152, 140, 1065, 40, 234, 480, 60, 22,
  89, 267, 110, 212, 1070, 48, 1071, 132, 20, 84, 1008, 178, 306, 420,
  714, 268, 538, 358, 860, 210, 718, 164, 1008, 36, 270, 0, 102, 540,
  432, 342, 980, 30, 48, 60, 332, 18, 520, 1086, 140, 16, 930, 30,
  1089, 36, 726, 545, 348, 12, 396, 364, 1458, 546, 55, 72, 78, 68,
  336, 1096, 292, 60, 676, 78, 122, 20, 35, 366, 1101, 252, 84, 1102,
  1103, 44, 0, 16, 330, 78, 1106, 360, 68, 138, 82, 1108, 474, 12,
  148, 100, 36, 138, 220, 78, 1040, 278, 742, 444, 1056, 30, 420, 558,
  148, 84, 559, 372, 1119, 24, 738, 522, 1121, 80, 224, 102, 318, 280,
  172, 300, 1125, 562, 150, 462, 40, 0, 60, 1128, 750, 112, 144, 28,
  360, 94, 60, 255, 1133, 54, 756, 452, 756, 140, 71, 378, 60, 284,
  330, 528, 546, 36, 1140, 54, 380, 570, 456, 126, 381, 20, 36, 228,
  364, 190, 764, 60, 144, 120, 1148, 382, 90, 220, 116, 575, 0, 96,
  460, 576, 384, 96, 577, 60, 770, 272, 192, 44, 924, 24, 330, 180,
  386, 28, 105, 126, 1100, 246, 20, 1162, 356, 96, 272, 232, 12, 130,
  1166, 388, 932, 72, 360, 498, 1169, 12, 36, 39, 70, 146, 132, 176,
  46, 586, 756, 0, 1175, 42, 36, 530, 156, 90, 1178, 390, 336, 116,
  786, 236, 1104, 196, 420, 156, 786, 24, 1122, 52, 790, 74, 336, 593,
  900, 90, 792, 280, 60, 48, 595, 18, 1191, 148, 156, 149, 30, 22,
  796, 476, 398, 44, 184, 18, 956, 598, 0, 180, 1199, 20]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked : ∀ i : Fin 348, let r := 2053 + i.val
    let k := exponents[i.val]!
    input.Coprime r → 0 < k ∧ k ≤ 2052 ∧ modPower r 12 k % r = 1 % r := by
  decide +kernel

private theorem below {r : ℕ} (hr : 0 < r) (hb : r < 2401) (hc : input.Coprime r) :
    orderOf (input : ZMod r) ≤ 2052 := by
  by_cases hsmall : r < 2053
  · by_cases h1 : r = 1
    · subst r
      have hone : (input : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [hone, orderOf_one]
      decide
    · have h := ZMod.orderOf_lt (by omega : 1 < r) (input : ZMod r)
      omega
  · let i : Fin 348 := ⟨r - 2053, by omega⟩
    have hi : 2053 + i.val = r := by dsimp [i]; omega
    have h := checked i
    dsimp only at h
    rw [hi] at h
    obtain ⟨hk, hle, heq⟩ := h hc
    exact (Nat.le_of_dvd hk (orderOf_dvd_of_pow_eq_one ((mod_test r _ (by omega)).mpr heq))).trans hle

theorem term_45087951844967 : IsTerm 45087951844967 2401 := by
  refine ⟨⟨by decide, by decide, ?_⟩, ?_⟩
  · change threshold input ≤ (orderOf (input : ZMod 2401) : ℝ)
    rw [at_2401]
    exact threshold_bounds.2.le
  · intro r hr
    obtain ⟨hrpos, hc, hqual⟩ := hr
    by_contra! hb
    have h := below hrpos hb hc
    have h' : (orderOf (input : ZMod r) : ℝ) ≤ 2052 := by exact_mod_cast h
    exact (not_lt_of_ge h') (threshold_bounds.1.trans_le hqual)

theorem furtherPower : FurtherPower :=
  ⟨45087951844967, 2401, 7, 4, by decide, term_45087951844967, by decide,
    by decide, by decide, by simp [Listed]⟩

end OMA.A394432
