/-
Copyright (c) 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn

! This file was ported from Lean 3 source module analysis.special_functions.stirling
! leanprover-community/mathlib commit 2c1d8ca2812b64f88992a5294ea3dba144755cd1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.PSeries
import Mathlib.Data.Real.Pi.Wallis

/-!
# Stirling's formula

This file proves Stirling's formula for the factorial.
It states that $n!$ grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.

## Proof outline

The proof follows: <https://proofwiki.org/wiki/Stirling%27s_Formula>.

We proceed in two parts.

**Part 1**: We consider the sequence $a_n$ of fractions $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$
and prove that this sequence converges to a real, positive number $a$. For this the two main
ingredients are
 - taking the logarithm of the sequence and
 - using the series expansion of $\log(1 + x)$.

**Part 2**: We use the fact that the series defined in part 1 converges against a real number $a$
and prove that $a = \sqrt{\pi}$. Here the main ingredient is the convergence of Wallis' product
formula for `π`.
-/


open scoped Topology Real BigOperators Nat

open Finset Filter Nat Real

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue #2220

namespace Stirling

/-!
 ### Part 1
 https://proofwiki.org/wiki/Stirling%27s_Formula#Part_1
-/


/-- Define `stirlingSeq n` as $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$.
Stirling's formula states that this sequence has limit $\sqrt(π)$.
-/
noncomputable def stirlingSeq (n : ℕ) : ℝ :=
  n ! / (Real.sqrt (2 * n) * (n / exp 1) ^ n)
#align stirling.stirling_seq Stirling.stirlingSeq

@[simp]
theorem stirlingSeq_zero : stirlingSeq 0 = 0 := by
  rw [stirlingSeq, cast_zero, MulZeroClass.mul_zero, Real.sqrt_zero, MulZeroClass.zero_mul,
    div_zero]
#align stirling.stirling_seq_zero Stirling.stirlingSeq_zero

@[simp]
theorem stirlingSeq_one : stirlingSeq 1 = exp 1 / Real.sqrt 2 := by
  rw [stirlingSeq, pow_one, factorial_one, cast_one, mul_one, mul_one_div, one_div_div]
#align stirling.stirling_seq_one Stirling.stirlingSeq_one

/-- We have the expression
`log (stirlingSeq (n + 1)) = log(n + 1)! - 1 / 2 * log(2 * n) - n * log ((n + 1) / e)`.
-/
theorem log_stirlingSeq_formula (n : ℕ) : log (stirlingSeq n.succ) =
    Real.log n.succ ! - 1 / 2 * Real.log (2 * n.succ) - n.succ * log (n.succ / exp 1) := by
  rw [stirlingSeq, log_div, log_mul, sqrt_eq_rpow, log_rpow, Real.log_pow, tsub_tsub] <;> positivity
#align stirling.log_stirling_seq_formula Stirling.log_stirlingSeq_formula

-- Porting note: the custom discharger of the simp in the theorem below has
-- unreachable tactics for some of its invocations
set_option linter.unreachableTactic false
/-- The sequence `log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2))` has the series expansion
   `∑ 1 / (2 * (k + 1) + 1) * (1 / 2 * (m + 1) + 1)^(2 * (k + 1))`
-/
theorem log_stirlingSeq_diff_hasSum (m : ℕ) :
    HasSum (fun k : ℕ => ↑1 / (↑2 * k.succ + ↑1) * (((1:ℝ) / (↑2 * m.succ + ↑1)) ^ 2) ^ k.succ)
      (log (stirlingSeq m.succ) - log (stirlingSeq m.succ.succ)) := by
  change HasSum
    ((fun b : ℕ => (1:ℝ) / ((2:ℝ) * b + (1:ℝ)) * (((1:ℝ) / (2 * m.succ + 1)) ^ 2) ^ b) ∘ succ) _
  refine' (hasSum_nat_add_iff (a := _ - _) -- Porting note: must give implicit arguments
    (f := (fun b : ℕ => ↑1 / (↑2 * b + ↑1) * (((1:ℝ) / (2 * m.succ + 1)) ^ 2) ^ b)) 1).mpr _
  convert (hasSum_log_one_add_inv <|
    cast_pos.mpr (succ_pos m)).mul_left ((m.succ : ℝ) + 1 / 2) using 1
  · ext k
    rw [← pow_mul, pow_add]
    push_cast
    have : 2 * (k : ℝ) + 1 ≠ 0 := by norm_cast; exact succ_ne_zero (2 * k)
    have : 2 * ((m : ℝ) + 1) + 1 ≠ 0 := by norm_cast; exact succ_ne_zero (2 * m.succ)
    field_simp
    ring
  · have h : ∀ (x : ℝ) (_ : x ≠ 0), 1 + x⁻¹ = (x + 1) / x := by
      intro x hx; rw [_root_.add_div, div_self hx, inv_eq_one_div]
    simp (disch := norm_cast <;> apply_rules [mul_ne_zero, succ_ne_zero, factorial_ne_zero,
      exp_ne_zero]) only [log_stirlingSeq_formula, log_div, log_mul, log_exp, factorial_succ,
      cast_mul, cast_succ, cast_zero, range_one, sum_singleton, h]
    ring
#align stirling.log_stirling_seq_diff_has_sum Stirling.log_stirlingSeq_diff_hasSum
set_option linter.unreachableTactic true

/-- The sequence `log ∘ stirlingSeq ∘ succ` is monotone decreasing -/
theorem log_stirlingSeq'_antitone : Antitone (Real.log ∘ stirlingSeq ∘ succ) :=
  antitone_nat_of_succ_le fun n =>
    sub_nonneg.mp <| (log_stirlingSeq_diff_hasSum n).nonneg fun m => by positivity
#align stirling.log_stirling_seq'_antitone Stirling.log_stirlingSeq'_antitone

/-- We have a bound for successive elements in the sequence `log (stirlingSeq k)`.
-/
theorem log_stirlingSeq_diff_le_geo_sum (n : ℕ) :
    log (stirlingSeq n.succ) - log (stirlingSeq n.succ.succ) ≤
      ((1:ℝ) / (2 * n.succ + 1)) ^ 2 / (↑1 - ((1:ℝ) / (2 * n.succ + 1)) ^ 2) := by
  have h_nonneg : ↑0 ≤ ((1:ℝ) / (2 * n.succ + 1)) ^ 2 := sq_nonneg _
  have g : HasSum (fun k : ℕ => (((1:ℝ) / (2 * n.succ + 1)) ^ 2) ^ k.succ)
      (((1:ℝ) / (2 * n.succ + 1)) ^ 2 / (↑1 - ((1:ℝ) / (2 * n.succ + 1)) ^ 2)) := by
    have := (hasSum_geometric_of_lt_1 h_nonneg ?_).mul_left (((1:ℝ) / (2 * n.succ + 1)) ^ 2)
    · simp_rw [← _root_.pow_succ] at this
      exact this
    rw [one_div, inv_pow]
    exact inv_lt_one (one_lt_pow ((lt_add_iff_pos_left 1).mpr <| by positivity) two_ne_zero)
  have hab : ∀ k : ℕ, (1:ℝ) / (↑2 * k.succ + ↑1) * (((1:ℝ) / (2 * n.succ + 1)) ^ 2) ^ k.succ ≤
      (((1:ℝ) / (2 * n.succ + 1)) ^ 2) ^ k.succ := by
    refine' fun k => mul_le_of_le_one_left (pow_nonneg h_nonneg k.succ) _
    rw [one_div]
    exact inv_le_one (le_add_of_nonneg_left <| by positivity)
  exact hasSum_le hab (log_stirlingSeq_diff_hasSum n) g
#align stirling.log_stirling_seq_diff_le_geo_sum Stirling.log_stirlingSeq_diff_le_geo_sum

/-- We have the bound `log (stirlingSeq n) - log (stirlingSeq (n+1))` ≤ 1/(4 n^2)
-/
theorem log_stirlingSeq_sub_log_stirlingSeq_succ (n : ℕ) :
    log (stirlingSeq n.succ) - log (stirlingSeq n.succ.succ) ≤ ↑1 / (↑4 * (n.succ:ℝ) ^ 2) := by
  have h₁ : ↑0 < ↑4 * ((n:ℝ) + 1) ^ 2 := by positivity
  have h₃ : ↑0 < (2 * ((n:ℝ) + 1) + 1) ^ 2 := by positivity
  have h₂ : ↑0 < ↑1 - (1 / (2 * ((n:ℝ) + 1) + 1)) ^ 2 := by
    rw [← mul_lt_mul_right h₃]
    have H : ↑0 < (2 * ((n:ℝ) + 1) + 1) ^ 2 - 1 := by nlinarith [@cast_nonneg ℝ _ n]
    convert H using 1 <;> field_simp [h₃.ne']
  refine' (log_stirlingSeq_diff_le_geo_sum n).trans _
  push_cast
  rw [div_le_div_iff h₂ h₁]
  field_simp [h₃.ne']
  rw [div_le_div_right h₃]
  ring_nf
  norm_cast
  linarith
#align stirling.log_stirling_seq_sub_log_stirling_seq_succ Stirling.log_stirlingSeq_sub_log_stirlingSeq_succ

/-- For any `n`, we have `log_stirlingSeq 1 - log_stirlingSeq n ≤ 1/4 * ∑' 1/k^2`  -/
theorem log_stirlingSeq_bounded_aux :
    ∃ c : ℝ, ∀ n : ℕ, log (stirlingSeq 1) - log (stirlingSeq n.succ) ≤ c := by
  let d := ∑' k : ℕ, ↑1 / (k.succ:ℝ) ^ 2
  use (1 / 4 * d : ℝ)
  let log_stirlingSeq' : ℕ → ℝ := fun k => log (stirlingSeq k.succ)
  intro n
  have h₁ : ∀ k, log_stirlingSeq' k - log_stirlingSeq' (k + 1) ≤
      ↑1 / ↑4 * (↑1 / (k.succ:ℝ) ^ 2) := by
    intro k; convert log_stirlingSeq_sub_log_stirlingSeq_succ k using 1; field_simp
  have h₂ : (∑ k : ℕ in range n, ↑1 / (k.succ:ℝ) ^ 2) ≤ d := by
    have := (summable_nat_add_iff 1).mpr <| Real.summable_one_div_nat_pow.mpr one_lt_two
    simp only [rpow_nat_cast] at this
    exact sum_le_tsum (range n) (fun k _ => by positivity) this
  calc
    log (stirlingSeq 1) - log (stirlingSeq n.succ) = log_stirlingSeq' 0 - log_stirlingSeq' n :=
      rfl
    _ = ∑ k in range n, (log_stirlingSeq' k - log_stirlingSeq' (k + 1)) := by
      rw [← sum_range_sub' log_stirlingSeq' n]
    _ ≤ ∑ k in range n, ↑1 / ↑4 * (↑1 / ↑(k.succ) ^ 2) := (sum_le_sum fun k _ => h₁ k)
    _ = ↑1 / ↑4 * ∑ k in range n, ↑1 / ↑(k.succ) ^ 2 := by rw [mul_sum]
    _ ≤ 1 / 4 * d := mul_le_mul_of_nonneg_left h₂ <| by positivity
#align stirling.log_stirling_seq_bounded_aux Stirling.log_stirlingSeq_bounded_aux

/-- The sequence `log_stirlingSeq` is bounded below for `n ≥ 1`. -/
theorem log_stirlingSeq_bounded_by_constant : ∃ c, ∀ n : ℕ, c ≤ log (stirlingSeq n.succ) := by
  obtain ⟨d, h⟩ := log_stirlingSeq_bounded_aux
  exact ⟨log (stirlingSeq 1) - d, fun n => sub_le_comm.mp (h n)⟩
#align stirling.log_stirling_seq_bounded_by_constant Stirling.log_stirlingSeq_bounded_by_constant

/-- The sequence `stirlingSeq` is positive for `n > 0`  -/
theorem stirlingSeq'_pos (n : ℕ) : 0 < stirlingSeq n.succ := by unfold stirlingSeq; positivity
#align stirling.stirling_seq'_pos Stirling.stirlingSeq'_pos

/-- The sequence `stirlingSeq` has a positive lower bound.
-/
theorem stirlingSeq'_bounded_by_pos_constant : ∃ a, 0 < a ∧ ∀ n : ℕ, a ≤ stirlingSeq n.succ := by
  cases' log_stirlingSeq_bounded_by_constant with c h
  refine' ⟨exp c, exp_pos _, fun n => _⟩
  rw [← le_log_iff_exp_le (stirlingSeq'_pos n)]
  exact h n
#align stirling.stirling_seq'_bounded_by_pos_constant Stirling.stirlingSeq'_bounded_by_pos_constant

/-- The sequence `stirlingSeq ∘ succ` is monotone decreasing -/
theorem stirlingSeq'_antitone : Antitone (stirlingSeq ∘ succ) := fun n m h =>
  (log_le_log (stirlingSeq'_pos m) (stirlingSeq'_pos n)).mp (log_stirlingSeq'_antitone h)
#align stirling.stirling_seq'_antitone Stirling.stirlingSeq'_antitone

/-- The limit `a` of the sequence `stirlingSeq` satisfies `0 < a` -/
theorem stirlingSeq_has_pos_limit_a : ∃ a : ℝ, 0 < a ∧ Tendsto stirlingSeq atTop (𝓝 a) := by
  obtain ⟨x, x_pos, hx⟩ := stirlingSeq'_bounded_by_pos_constant
  have hx' : x ∈ lowerBounds (Set.range (stirlingSeq ∘ succ)) := by simpa [lowerBounds] using hx
  refine' ⟨_, lt_of_lt_of_le x_pos (le_csInf (Set.range_nonempty _) hx'), _⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact tendsto_atTop_ciInf stirlingSeq'_antitone ⟨x, hx'⟩
#align stirling.stirling_seq_has_pos_limit_a Stirling.stirlingSeq_has_pos_limit_a

/-!
 ### Part 2
 https://proofwiki.org/wiki/Stirling%27s_Formula#Part_2
-/


/-- The sequence `n / (2 * n + 1)` tends to `1/2` -/
theorem tendsto_self_div_two_mul_self_add_one :
    Tendsto (fun n : ℕ => (n : ℝ) / (2 * n + 1)) atTop (𝓝 (1 / 2)) := by
  conv =>
    congr
    · skip
    · skip
    rw [one_div, ← add_zero (2 : ℝ)]
  refine' (((tendsto_const_div_atTop_nhds_0_nat 1).const_add (2 : ℝ)).inv₀
    ((add_zero (2 : ℝ)).symm ▸ two_ne_zero)).congr' (eventually_atTop.mpr ⟨1, fun n hn => _⟩)
  rw [add_div' (1 : ℝ) 2 n (cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn)), inv_div]
#align stirling.tendsto_self_div_two_mul_self_add_one Stirling.tendsto_self_div_two_mul_self_add_one

/-- For any `n ≠ 0`, we have the identity
`(stirlingSeq n)^4 / (stirlingSeq (2*n))^2 * (n / (2 * n + 1)) = W n`, where `W n` is the
`n`-th partial product of Wallis' formula for `π / 2`. -/
theorem stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq (n : ℕ) (hn : n ≠ 0) :
    stirlingSeq n ^ 4 / stirlingSeq (2 * n) ^ 2 * (n / (2 * n + 1)) = Wallis.W n := by
  have : 4 = 2 * 2 := by rfl
  rw [stirlingSeq, this, pow_mul, stirlingSeq, Wallis.W_eq_factorial_ratio]
  simp_rw [div_pow, mul_pow]
  rw [sq_sqrt, sq_sqrt]
  any_goals positivity
  have : (n : ℝ) ≠ 0 := cast_ne_zero.mpr hn
  have : exp 1 ≠ 0 := exp_ne_zero 1
  have : ((2 * n)! : ℝ) ≠ 0 := cast_ne_zero.mpr (factorial_ne_zero (2 * n))
  have : 2 * (n : ℝ) + 1 ≠ 0 := by norm_cast; exact succ_ne_zero (2 * n)
  field_simp
  simp only [mul_pow, mul_comm 2 n, mul_comm 4 n, pow_mul]
  ring
#align stirling.stirling_seq_pow_four_div_stirling_seq_pow_two_eq Stirling.stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq

/-- Suppose the sequence `stirlingSeq` (defined above) has the limit `a ≠ 0`.
Then the Wallis sequence `W n` has limit `a^2 / 2`.
-/
theorem second_wallis_limit (a : ℝ) (hane : a ≠ 0) (ha : Tendsto stirlingSeq atTop (𝓝 a)) :
    Tendsto Wallis.W atTop (𝓝 (a ^ 2 / 2)) := by
  refine' Tendsto.congr' (eventually_atTop.mpr ⟨1, fun n hn =>
    stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq n (one_le_iff_ne_zero.mp hn)⟩) _
  have h : a ^ 2 / ↑2 = a ^ 4 / a ^ 2 * (1 / 2) := by
    rw [mul_one_div, ← mul_one_div (a ^ 4) (a ^ 2), one_div, ← pow_sub_of_lt a]
    norm_num
  rw [h]
  exact ((ha.pow 4).div ((ha.comp (tendsto_id.const_mul_atTop' two_pos)).pow 2)
    (pow_ne_zero 2 hane)).mul tendsto_self_div_two_mul_self_add_one
#align stirling.second_wallis_limit Stirling.second_wallis_limit

/-- **Stirling's Formula** -/
theorem tendsto_stirlingSeq_sqrt_pi : Tendsto (fun n : ℕ => stirlingSeq n) atTop (𝓝 (sqrt π)) := by
  obtain ⟨a, hapos, halimit⟩ := stirlingSeq_has_pos_limit_a
  have hπ : π / 2 = a ^ 2 / 2 :=
    tendsto_nhds_unique Wallis.tendsto_W_nhds_pi_div_two (second_wallis_limit a hapos.ne' halimit)
  rwa [(div_left_inj' (two_ne_zero' ℝ)).mp hπ, sqrt_sq hapos.le]
#align stirling.tendsto_stirling_seq_sqrt_pi Stirling.tendsto_stirlingSeq_sqrt_pi

end Stirling
