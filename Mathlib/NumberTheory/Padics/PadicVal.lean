/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard

! This file was ported from Lean 3 source module number_theory.padics.padic_val
! leanprover-community/mathlib commit 60fa54e778c9e85d930efae172435f42fb0d71f7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Tactic.IntervalCases

/-!
# p-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in padicNorm.lean.

## Notations

This file uses the local notation `/.` for `Rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/


universe u

open Nat

open Rat

open multiplicity

/-- For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such
that `p^k` divides `z`. If `n = 0` or `p = 1`, then `padicValNat p q` defaults to `0`. -/
def padicValNat (p : ℕ) (n : ℕ) : ℕ :=
  if h : p ≠ 1 ∧ 0 < n then (multiplicity p n).get (multiplicity.finite_nat_iff.2 h) else 0
#align padic_val_nat padicValNat

namespace padicValNat

open multiplicity

variable {p : ℕ}

/-- `padicValNat p 0` is `0` for any `p`. -/
@[simp]
protected theorem zero : padicValNat p 0 = 0 := by simp [padicValNat]
#align padic_val_nat.zero padicValNat.zero

/-- `padicValNat p 1` is `0` for any `p`. -/
@[simp]
protected theorem one : padicValNat p 1 = 0 := by
  unfold padicValNat
  split_ifs
  · simp
  · rfl
#align padic_val_nat.one padicValNat.one

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValNat p p` is `1`. -/
@[simp]
theorem self (hp : 1 < p) : padicValNat p p = 1 := by
  have neq_one : ¬p = 1 ↔ True := iff_of_true hp.ne' trivial
  have eq_zero_false : p = 0 ↔ False := iff_false_intro (zero_lt_one.trans hp).ne'
  simp [padicValNat, neq_one, eq_zero_false]
#align padic_val_nat.self padicValNat.self

@[simp]
theorem eq_zero_iff {n : ℕ} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n := by
  simp only [padicValNat, dite_eq_right_iff, PartENat.get_eq_iff_eq_coe, Nat.cast_zero,
    multiplicity_eq_zero, and_imp, pos_iff_ne_zero, Ne.def, ← or_iff_not_imp_left]
#align padic_val_nat.eq_zero_iff padicValNat.eq_zero_iff

theorem eq_zero_of_not_dvd {n : ℕ} (h : ¬p ∣ n) : padicValNat p n = 0 :=
  eq_zero_iff.2 <| Or.inr <| Or.inr h
#align padic_val_nat.eq_zero_of_not_dvd padicValNat.eq_zero_of_not_dvd

open Nat.maxPowDiv

theorem maxPowDiv_eq_multiplicity {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDiv n = multiplicity p n := by
  apply multiplicity.unique <| pow_dvd p n
  intro h
  apply Nat.not_lt.mpr <| le_of_dvd hp hn h
  simp

theorem maxPowDiv_eq_multiplicity_get {p n : ℕ} (hp : 1 < p) (hn : 0 < n) (h : Finite p n) :
    p.maxPowDiv n = (multiplicity p n).get h := by
  rw [PartENat.get_eq_iff_eq_coe.mpr]
  apply maxPowDiv_eq_multiplicity hp hn|>.symm

/-- Allows for more efficient code for `padicValNat` -/
@[csimp]
theorem padicValNat_eq_maxPowDiv : @padicValNat = @maxPowDiv := by
  ext p n
  by_cases (1 < p ∧ 0 < n)
  · dsimp [padicValNat]
    rw [dif_pos ⟨Nat.ne_of_gt h.1,h.2⟩, maxPowDiv_eq_multiplicity_get h.1 h.2]
  · simp only [not_and_or,not_gt_eq,le_zero_iff] at h
    apply h.elim
    · intro h
      interval_cases p
      · simp [Classical.em]
      · dsimp [padicValNat, maxPowDiv]
        rw [go_eq, if_neg, dif_neg] <;> simp
    · intro h
      simp [h]

end padicValNat

/-- For `p ≠ 1`, the `p`-adic valuation of an integer `z ≠ 0` is the largest natural number `k` such
that `p^k` divides `z`. If `x = 0` or `p = 1`, then `padicValInt p q` defaults to `0`. -/
def padicValInt (p : ℕ) (z : ℤ) : ℕ :=
  padicValNat p z.natAbs
#align padic_val_int padicValInt

namespace padicValInt

open multiplicity

variable {p : ℕ}

theorem of_ne_one_ne_zero {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValInt p z =
      (multiplicity (p : ℤ) z).get
        (by
          apply multiplicity.finite_int_iff.2
          simp [hp, hz]) := by
  rw [padicValInt, padicValNat, dif_pos (And.intro hp (Int.natAbs_pos.mpr hz))]
  simp only [multiplicity.Int.natAbs p z]
#align padic_val_int.of_ne_one_ne_zero padicValInt.of_ne_one_ne_zero

/-- `padicValInt p 0` is `0` for any `p`. -/
@[simp]
protected theorem zero : padicValInt p 0 = 0 := by simp [padicValInt]
#align padic_val_int.zero padicValInt.zero

/-- `padicValInt p 1` is `0` for any `p`. -/
@[simp]
protected theorem one : padicValInt p 1 = 0 := by simp [padicValInt]
#align padic_val_int.one padicValInt.one

/-- The `p`-adic value of a natural is its `p`-adic value as an integer. -/
@[simp]
theorem of_nat {n : ℕ} : padicValInt p n = padicValNat p n := by simp [padicValInt]
#align padic_val_int.of_nat padicValInt.of_nat

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValInt p p` is `1`. -/
theorem self (hp : 1 < p) : padicValInt p p = 1 := by simp [padicValNat.self hp]
#align padic_val_int.self padicValInt.self

theorem eq_zero_of_not_dvd {z : ℤ} (h : ¬(p : ℤ) ∣ z) : padicValInt p z = 0 := by
  rw [padicValInt, padicValNat]
  split_ifs <;> simp [multiplicity.Int.natAbs, multiplicity_eq_zero.2 h]
#align padic_val_int.eq_zero_of_not_dvd padicValInt.eq_zero_of_not_dvd

end padicValInt

/-- `padicValRat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.den`. If `q = 0` or `p = 1`, then `padicValRat p q` defaults to `0`. -/
def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den
#align padic_val_rat padicValRat

namespace padicValRat

open multiplicity

variable {p : ℕ}

/-- `padicValRat p q` is symmetric in `q`. -/
@[simp]
protected theorem neg (q : ℚ) : padicValRat p (-q) = padicValRat p q := by
  simp [padicValRat, padicValInt]
#align padic_val_rat.neg padicValRat.neg

/-- `padicValRat p 0` is `0` for any `p`. -/
@[simp]
protected theorem zero : padicValRat p 0 = 0 := by simp [padicValRat]
#align padic_val_rat.zero padicValRat.zero

/-- `padicValRat p 1` is `0` for any `p`. -/
@[simp]
protected theorem one : padicValRat p 1 = 0 := by simp [padicValRat]
#align padic_val_rat.one padicValRat.one

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic_value as a rational. -/
@[simp]
theorem of_int {z : ℤ} : padicValRat p z = padicValInt p z := by simp [padicValRat]
#align padic_val_rat.of_int padicValRat.of_int

/-- The `p`-adic value of an integer `z ≠ 0` is the multiplicity of `p` in `z`. -/
theorem of_int_multiplicity {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValRat p (z : ℚ) = (multiplicity (p : ℤ) z).get (finite_int_iff.2 ⟨hp, hz⟩) := by
  rw [of_int, padicValInt.of_ne_one_ne_zero hp hz]
#align padic_val_rat.of_int_multiplicity padicValRat.of_int_multiplicity

theorem multiplicity_sub_multiplicity {q : ℚ} (hp : p ≠ 1) (hq : q ≠ 0) :
    padicValRat p q =
      (multiplicity (p : ℤ) q.num).get (finite_int_iff.2 ⟨hp, Rat.num_ne_zero_of_ne_zero hq⟩) -
        (multiplicity p q.den).get
          (by
            rw [← finite_iff_dom, finite_nat_iff]
            exact ⟨hp, q.pos⟩) := by
  rw [padicValRat, padicValInt.of_ne_one_ne_zero hp, padicValNat, dif_pos]
  · exact ⟨hp, q.pos⟩
  · exact Rat.num_ne_zero_of_ne_zero hq
#align padic_val_rat.multiplicity_sub_multiplicity padicValRat.multiplicity_sub_multiplicity

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic value as a rational. -/
@[simp]
theorem of_nat {n : ℕ} : padicValRat p n = padicValNat p n := by simp [padicValRat]
#align padic_val_rat.of_nat padicValRat.of_nat

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValRat p p` is `1`. -/
theorem self (hp : 1 < p) : padicValRat p p = 1 := by simp [hp]
#align padic_val_rat.self padicValRat.self

end padicValRat

section padicValNat

variable {p : ℕ}

theorem zero_le_padicValRat_of_nat (n : ℕ) : 0 ≤ padicValRat p n := by simp
#align zero_le_padic_val_rat_of_nat zero_le_padicValRat_of_nat

/-- `padicValRat` coincides with `padicValNat`. -/
@[norm_cast]
theorem padicValRat_of_nat (n : ℕ) : ↑(padicValNat p n) = padicValRat p n := by simp
#align padic_val_rat_of_nat padicValRat_of_nat

/-- A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`. -/
theorem padicValNat_def [hp : Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    padicValNat p n = (multiplicity p n).get (multiplicity.finite_nat_iff.2 ⟨hp.out.ne_one, hn⟩) :=
  dif_pos ⟨hp.out.ne_one, hn⟩
#align padic_val_nat_def padicValNat_def

theorem padicValNat_def' {n : ℕ} (hp : p ≠ 1) (hn : 0 < n) :
    ↑(padicValNat p n) = multiplicity p n := by simp [padicValNat, hp, hn]
#align padic_val_nat_def' padicValNat_def'

@[simp]
theorem padicValNat_self [Fact p.Prime] : padicValNat p p = 1 := by
  rw [padicValNat_def (@Fact.out p.Prime).pos]
  simp
#align padic_val_nat_self padicValNat_self

theorem one_le_padicValNat_of_dvd {n : ℕ} [hp : Fact p.Prime] (hn : 0 < n) (div : p ∣ n) :
    1 ≤ padicValNat p n := by
  rwa [← PartENat.coe_le_coe, padicValNat_def' hp.out.ne_one hn, ← pow_dvd_iff_le_multiplicity,
    pow_one]
#align one_le_padic_val_nat_of_dvd one_le_padicValNat_of_dvd

theorem dvd_iff_padicValNat_ne_zero {p n : ℕ} [Fact p.Prime] (hn0 : n ≠ 0) :
    p ∣ n ↔ padicValNat p n ≠ 0 :=
  ⟨fun h => one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hn0.bot_lt h), fun h =>
    Classical.not_not.1 (mt padicValNat.eq_zero_of_not_dvd h)⟩
#align dvd_iff_padic_val_nat_ne_zero dvd_iff_padicValNat_ne_zero

end padicValNat

namespace padicValRat

open multiplicity

variable {p : ℕ} [hp : Fact p.Prime]

/-- The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`. -/
theorem finite_int_prime_iff {a : ℤ} : Finite (p : ℤ) a ↔ a ≠ 0 := by
  simp [finite_int_iff, hp.1.ne_one]
#align padic_val_rat.finite_int_prime_iff padicValRat.finite_int_prime_iff

/-- A rewrite lemma for `padicValRat p q` when `q` is expressed in terms of `Rat.mk`. -/
protected theorem defn (p : ℕ) [hp : Fact p.Prime] {q : ℚ} {n d : ℤ} (hqz : q ≠ 0)
    (qdf : q = n /. d) :
    padicValRat p q =
      (multiplicity (p : ℤ) n).get
          (finite_int_iff.2 ⟨hp.1.ne_one, fun hn => by simp_all⟩) -
        (multiplicity (p : ℤ) d).get
          (finite_int_iff.2 ⟨hp.1.ne_one, fun hd => by simp_all⟩) := by
  have hd : d ≠ 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  let ⟨c, hc1, hc2⟩ := Rat.num_den_mk hd qdf
  rw [padicValRat.multiplicity_sub_multiplicity hp.1.ne_one hqz]
  simp only [Nat.isUnit_iff, hc1, hc2]
  rw [multiplicity.mul' (Nat.prime_iff_prime_int.1 hp.1),
    multiplicity.mul' (Nat.prime_iff_prime_int.1 hp.1)]
  rw [Nat.cast_add, Nat.cast_add]
  simp_rw [Int.coe_nat_multiplicity p q.den]
  ring
  -- Porting note: was
  -- simp only [hc1, hc2, multiplicity.mul' (Nat.prime_iff_prime_int.1 hp.1),
  --   hp.1.ne_one, hqz, pos_iff_ne_zero, Int.coe_nat_multiplicity p q.den
#align padic_val_rat.defn padicValRat.defn

/-- A rewrite lemma for `padicValRat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected theorem mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q * r) = padicValRat p q + padicValRat p r := by
  have : q * r = q.num * r.num /. (q.den * r.den) := by rw_mod_cast [Rat.mul_num_den]
  have hq' : q.num /. q.den ≠ 0 := by rwa [Rat.num_den]
  have hr' : r.num /. r.den ≠ 0 := by rwa [Rat.num_den]
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.1
  rw [padicValRat.defn p (mul_ne_zero hq hr) this]
  conv_rhs =>
    rw [← @Rat.num_den q, padicValRat.defn p hq', ← @Rat.num_den r, padicValRat.defn p hr']
  rw [multiplicity.mul' hp', multiplicity.mul' hp', Nat.cast_add, Nat.cast_add]
  ring
  -- Porting note: was
  -- simp [add_comm, add_left_comm, sub_eq_add_neg]
#align padic_val_rat.mul padicValRat.mul

/-- A rewrite lemma for `padicValRat p (q^k)` with condition `q ≠ 0`. -/
protected theorem pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} : padicValRat p (q ^ k) = k * padicValRat p q :=
  by induction k <;>
    simp [*, padicValRat.mul hq (pow_ne_zero _ hq), _root_.pow_succ, add_mul, add_comm]
#align padic_val_rat.pow padicValRat.pow

/-- A rewrite lemma for `padicValRat p (q⁻¹)` with condition `q ≠ 0`. -/
protected theorem inv (q : ℚ) : padicValRat p q⁻¹ = -padicValRat p q := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul (inv_ne_zero hq) hq, inv_mul_cancel hq,
      padicValRat.one]
#align padic_val_rat.inv padicValRat.inv

/-- A rewrite lemma for `padicValRat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected theorem div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q / r) = padicValRat p q - padicValRat p r := by
  rw [div_eq_mul_inv, padicValRat.mul hq (inv_ne_zero hr), padicValRat.inv r, sub_eq_add_neg]
#align padic_val_rat.div padicValRat.div

/-- A condition for `padicValRat p (n₁ / d₁) ≤ padicValRat p (n₂ / d₂)`, in terms of
divisibility by `p^n`. -/
theorem padicValRat_le_padicValRat_iff {n₁ n₂ d₁ d₂ : ℤ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    padicValRat p (n₁ /. d₁) ≤ padicValRat p (n₂ /. d₂) ↔
      ∀ n : ℕ, (p : ℤ) ^ n ∣ n₁ * d₂ → (p : ℤ) ^ n ∣ n₂ * d₁ := by
  have hf1 : Finite (p : ℤ) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : Finite (p : ℤ) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  conv =>
    lhs
    rw [padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₁ hd₁) rfl,
      padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₂ hd₂) rfl, sub_le_iff_le_add', ←
      add_sub_assoc, _root_.le_sub_iff_add_le]
    norm_cast
    rw [← multiplicity.mul' (Nat.prime_iff_prime_int.1 hp.1) hf1, add_comm, ←
      multiplicity.mul' (Nat.prime_iff_prime_int.1 hp.1) hf2, PartENat.get_le_get,
      multiplicity_le_multiplicity_iff]
#align padic_val_rat.padic_val_rat_le_padic_val_rat_iff padicValRat.padicValRat_le_padicValRat_iff

/-- Sufficient conditions to show that the `p`-adic valuation of `q` is less than or equal to the
`p`-adic valuation of `q + r`. -/
theorem le_padicValRat_add_of_le {q r : ℚ} (hqr : q + r ≠ 0)
    (h : padicValRat p q ≤ padicValRat p r) : padicValRat p q ≤ padicValRat p (q + r) :=
  if hq : q = 0 then by simpa [hq] using h
  else
    if hr : r = 0 then by simp [hr]
    else by
      have hqn : q.num ≠ 0 := Rat.num_ne_zero_of_ne_zero hq
      have hqd : (q.den : ℤ) ≠ 0 := by exact_mod_cast Rat.den_nz _
      have hrn : r.num ≠ 0 := Rat.num_ne_zero_of_ne_zero hr
      have hrd : (r.den : ℤ) ≠ 0 := by exact_mod_cast Rat.den_nz _
      have hqreq : q + r = (q.num * r.den + q.den * r.num) /. (q.den * r.den) := Rat.add_num_den _ _
      have hqrd : q.num * r.den + q.den * r.num ≠ 0 := Rat.mk_num_ne_zero_of_ne_zero hqr hqreq
      conv_lhs => rw [← @Rat.num_den q]
      rw [hqreq, padicValRat_le_padicValRat_iff hqn hqrd hqd (mul_ne_zero hqd hrd), ←
        multiplicity_le_multiplicity_iff, mul_left_comm,
        multiplicity.mul (Nat.prime_iff_prime_int.1 hp.1), add_mul]
      rw [← @Rat.num_den q, ← @Rat.num_den r, padicValRat_le_padicValRat_iff hqn hrn hqd hrd, ←
        multiplicity_le_multiplicity_iff] at h
      calc
        _ ≤
            min (multiplicity (↑p) (q.num * r.den * q.den))
              (multiplicity (↑p) (↑q.den * r.num * ↑q.den)) :=
          le_min
            (by rw [@multiplicity.mul _ _ _ _ (_ * _) _ (Nat.prime_iff_prime_int.1 hp.1), add_comm])
            (by
              rw [mul_assoc,
                  @multiplicity.mul _ _ _ _ (q.den : ℤ) (_ * _)
                    (Nat.prime_iff_prime_int.1 hp.1)]
              exact add_le_add_left h _)
        _ ≤ _ := min_le_multiplicity_add
#align padic_val_rat.le_padic_val_rat_add_of_le padicValRat.le_padicValRat_add_of_le

/-- The minimum of the valuations of `q` and `r` is at most the valuation of `q + r`. -/
theorem min_le_padicValRat_add {q r : ℚ} (hqr : q + r ≠ 0) :
    min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r) :=
  (le_total (padicValRat p q) (padicValRat p r)).elim
  (fun h => by rw [min_eq_left h]; exact le_padicValRat_add_of_le hqr h)
  (fun h => by rw [min_eq_right h, add_comm]; exact le_padicValRat_add_of_le (by rwa [add_comm]) h)
#align padic_val_rat.min_le_padic_val_rat_add padicValRat.min_le_padicValRat_add

open BigOperators

/-- A finite sum of rationals with positive `p`-adic valuation has positive `p`-adic valuation
(if the sum is non-zero). -/
theorem sum_pos_of_pos {n : ℕ} {F : ℕ → ℚ} (hF : ∀ i, i < n → 0 < padicValRat p (F i))
    (hn0 : (∑ i in Finset.range n, F i) ≠ 0) : 0 < padicValRat p (∑ i in Finset.range n, F i) := by
  induction' n with d hd
  · exact False.elim (hn0 rfl)
  · rw [Finset.sum_range_succ] at hn0 ⊢
    by_cases h : (∑ x : ℕ in Finset.range d, F x) = 0
    · rw [h, zero_add]
      exact hF d (lt_add_one _)
    · refine' lt_of_lt_of_le _ (min_le_padicValRat_add hn0)
      · refine' lt_min (hd (fun i hi => _) h) (hF d (lt_add_one _))
        exact hF _ (lt_trans hi (lt_add_one _))
#align padic_val_rat.sum_pos_of_pos padicValRat.sum_pos_of_pos

end padicValRat

namespace padicValNat

variable {p a b : ℕ} [hp : Fact p.Prime]

/-- A rewrite lemma for `padicValNat p (a * b)` with conditions `a ≠ 0`, `b ≠ 0`. -/
protected theorem mul : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b :=
  by exact_mod_cast @padicValRat.mul p _ a b
#align padic_val_nat.mul padicValNat.mul

protected theorem div_of_dvd (h : b ∣ a) :
    padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm, k.mul_div_cancel hb.bot_lt, padicValNat.mul hk hb, Nat.add_sub_cancel]
#align padic_val_nat.div_of_dvd padicValNat.div_of_dvd

/-- Dividing out by a prime factor reduces the `padicValNat` by `1`. -/
protected theorem div (dvd : p ∣ b) : padicValNat p (b / p) = padicValNat p b - 1 := by
  rw [padicValNat.div_of_dvd dvd, padicValNat_self]
#align padic_val_nat.div padicValNat.div

/-- A version of `padicValRat.pow` for `padicValNat`. -/
protected theorem pow (n : ℕ) (ha : a ≠ 0) : padicValNat p (a ^ n) = n * padicValNat p a := by
  simpa only [← @Nat.cast_inj ℤ, push_cast] using padicValRat.pow (Nat.cast_ne_zero.mpr ha)
#align padic_val_nat.pow padicValNat.pow

@[simp]
protected theorem prime_pow (n : ℕ) : padicValNat p (p ^ n) = n := by
  rw [padicValNat.pow _ (@Fact.out p.Prime).ne_zero, padicValNat_self, mul_one]
#align padic_val_nat.prime_pow padicValNat.prime_pow

protected theorem div_pow (dvd : p ^ a ∣ b) : padicValNat p (b / p ^ a) = padicValNat p b - a := by
  rw [padicValNat.div_of_dvd dvd, padicValNat.prime_pow]
#align padic_val_nat.div_pow padicValNat.div_pow

protected theorem div' {m : ℕ} (cpm : coprime p m) {b : ℕ} (dvd : m ∣ b) :
    padicValNat p (b / m) = padicValNat p b := by
  rw [padicValNat.div_of_dvd dvd, eq_zero_of_not_dvd (hp.out.coprime_iff_not_dvd.mp cpm),
    Nat.sub_zero]
#align padic_val_nat.div' padicValNat.div'

end padicValNat

section padicValNat

variable {p : ℕ}

theorem dvd_of_one_le_padicValNat {n : ℕ} (hp : 1 ≤ padicValNat p n) : p ∣ n := by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)
#align dvd_of_one_le_padic_val_nat dvd_of_one_le_padicValNat

theorem pow_padicValNat_dvd {n : ℕ} : p ^ padicValNat p n ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn); · simp
  rcases eq_or_ne p 1 with (rfl | hp); · simp
  rw [multiplicity.pow_dvd_iff_le_multiplicity, padicValNat_def'] <;> assumption
#align pow_padic_val_nat_dvd pow_padicValNat_dvd

theorem padicValNat_dvd_iff_le [hp : Fact p.Prime] {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a := by
  rw [pow_dvd_iff_le_multiplicity, ← padicValNat_def' hp.out.ne_one ha.bot_lt, PartENat.coe_le_coe]
#align padic_val_nat_dvd_iff_le padicValNat_dvd_iff_le

theorem padicValNat_dvd_iff (n : ℕ) [hp : Fact p.Prime] (a : ℕ) :
    p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact iff_of_true (dvd_zero _) (Or.inl rfl)
  · rw [padicValNat_dvd_iff_le ha, or_iff_right ha]
#align padic_val_nat_dvd_iff padicValNat_dvd_iff

theorem pow_succ_padicValNat_not_dvd {n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) :
    ¬p ^ (padicValNat p n + 1) ∣ n := by
  rw [padicValNat_dvd_iff_le hn, not_le]
  exact Nat.lt_succ_self _
#align pow_succ_padic_val_nat_not_dvd pow_succ_padicValNat_not_dvd

theorem padicValNat_primes {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (neq : p ≠ q) :
    padicValNat p q = 0 :=
  @padicValNat.eq_zero_of_not_dvd p q <|
    (not_congr (Iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp neq
#align padic_val_nat_primes padicValNat_primes

open BigOperators

theorem range_pow_padicValNat_subset_divisors {n : ℕ} (hn : n ≠ 0) :
    (Finset.range (padicValNat p n + 1)).image (p ^ ·) ⊆ n.divisors := by
  intro t ht
  simp only [exists_prop, Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact ⟨(pow_dvd_pow p <| by linarith).trans pow_padicValNat_dvd, hn⟩
#align range_pow_padic_val_nat_subset_divisors range_pow_padicValNat_subset_divisors

theorem range_pow_padicValNat_subset_divisors' {n : ℕ} [hp : Fact p.Prime] :
    ((Finset.range (padicValNat p n)).image fun t => p ^ (t + 1)) ⊆ n.divisors.erase 1 := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  intro t ht
  simp only [exists_prop, Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_erase, Nat.mem_divisors]
  refine' ⟨_, (pow_dvd_pow p <| succ_le_iff.2 hk).trans pow_padicValNat_dvd, hn⟩
  exact (Nat.one_lt_pow _ _ k.succ_pos hp.out.one_lt).ne'
#align range_pow_padic_val_nat_subset_divisors' range_pow_padicValNat_subset_divisors'

end padicValNat

section padicValInt

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValInt_dvd_iff (n : ℕ) (a : ℤ) : (p : ℤ) ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValInt p a := by
  rw [padicValInt, ← Int.natAbs_eq_zero, ← padicValNat_dvd_iff, ← Int.coe_nat_dvd_left,
    Int.coe_nat_pow]
#align padic_val_int_dvd_iff padicValInt_dvd_iff

theorem padicValInt_dvd (a : ℤ) : (p : ℤ) ^ padicValInt p a ∣ a := by
  rw [padicValInt_dvd_iff]
  exact Or.inr le_rfl
#align padic_val_int_dvd padicValInt_dvd

theorem padicValInt_self : padicValInt p p = 1 :=
  padicValInt.self hp.out.one_lt
#align padic_val_int_self padicValInt_self

theorem padicValInt.mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
  simp_rw [padicValInt]
  rw [Int.natAbs_mul, padicValNat.mul] <;> rwa [Int.natAbs_ne_zero]
#align padic_val_int.mul padicValInt.mul

theorem padicValInt_mul_eq_succ (a : ℤ) (ha : a ≠ 0) :
    padicValInt p (a * p) = padicValInt p a + 1 := by
  rw [padicValInt.mul ha (Int.coe_nat_ne_zero.mpr hp.out.ne_zero)]
  simp only [eq_self_iff_true, padicValInt.of_nat, padicValNat_self]
#align padic_val_int_mul_eq_succ padicValInt_mul_eq_succ

end padicValInt
