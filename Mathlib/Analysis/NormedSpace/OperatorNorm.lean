/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo

! This file was ported from Lean 3 source module analysis.normed_space.operator_norm
! leanprover-community/mathlib commit 91862a6001a8b6ae3f261cdd8eea42f6ac596886
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.Topology.Algebra.Module.StrongTopology

/-!
# Operator norm on the space of continuous linear maps

Define the operator norm on the space of continuous (semi)linear maps between normed spaces, and
prove its basic properties. In particular, show that this space is itself a normed space.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup` and we specialize to `NormedAddCommGroup` at the end.

Note that most of statements that apply to semilinear maps only hold when the ring homomorphism
is isometric, as expressed by the typeclass `[RingHomIsometric σ]`.

-/


noncomputable section

open Classical NNReal Topology

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E Eₗ F Fₗ G Gₗ 𝓕 : Type _}

section SemiNormed

open Metric ContinuousLinearMap

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Eₗ] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup G] [SeminormedAddCommGroup Gₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  [NormedSpace 𝕜 Gₗ] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

set_option synthInstance.etaExperiment true in
/-- If `‖x‖ = 0` and `f` is continuous then `‖f x‖ = 0`. -/
theorem norm_image_of_norm_zero [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f) {x : E}
    (hx : ‖x‖ = 0) : ‖f x‖ = 0 := by
  refine' le_antisymm (le_of_forall_pos_le_add fun ε hε => _) (norm_nonneg (f x))
  rcases NormedAddCommGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) ε hε with ⟨δ, δ_pos, hδ⟩
  replace hδ := hδ x
  rw [sub_zero, hx] at hδ
  replace hδ := le_of_lt (hδ δ_pos)
  rw [map_zero, sub_zero] at hδ
  rwa [zero_add]
#align norm_image_of_norm_zero norm_image_of_norm_zero

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃]

set_option synthInstance.etaExperiment true in
theorem SemilinearMapClass.bound_of_shell_semi_normed [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) {x : E} (hx : ‖x‖ ≠ 0) :
    ‖f x‖ ≤ C * ‖x‖ := by
  rcases rescale_to_shell_semi_normed hc ε_pos hx with ⟨δ, hδ, δxle, leδx, _⟩
  have := hf (δ • x) leδx δxle
  simpa only [map_smulₛₗ, norm_smul, mul_left_comm C, mul_le_mul_left (norm_pos_iff.2 hδ),
    RingHomIsometric.is_iso] using hf (δ • x) leδx δxle
#align semilinear_map_class.bound_of_shell_semi_normed SemilinearMapClass.bound_of_shell_semi_normed

set_option synthInstance.etaExperiment true in
/-- A continuous linear map between seminormed spaces is bounded when the field is nontrivially
normed. The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε]`, whose image has a
controlled norm. The norm control for the original element follows by rescaling. -/
theorem SemilinearMapClass.bound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ := by
  rcases NormedAddCommGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one with ⟨ε, ε_pos, hε⟩
  simp only [sub_zero, map_zero] at hε
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < ‖c‖ / ε := div_pos (zero_lt_one.trans hc) ε_pos
  refine' ⟨‖c‖ / ε, this, fun x => _⟩
  by_cases hx : ‖x‖ = 0
  · rw [hx, MulZeroClass.mul_zero]
    exact le_of_eq (norm_image_of_norm_zero f hf hx)
  refine' SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc (fun x hle hlt => _) hx
  refine' (hε _ hlt).le.trans _
  rwa [← div_le_iff' this, one_div_div]
#align semilinear_map_class.bound_of_continuous SemilinearMapClass.bound_of_continuous

end

namespace ContinuousLinearMap

set_option synthInstance.etaExperiment true in
theorem bound [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ :=
  SemilinearMapClass.bound_of_continuous f f.2
#align continuous_linear_map.bound ContinuousLinearMap.bound

section

open Filter

variable (𝕜 E)

/-- Given a unit-length element `x` of a normed space `E` over a field `𝕜`, the natural linear
    isometry map from `𝕜` to `E` by taking multiples of `x`.-/
def _root_.LinearIsometry.toSpanSingleton {v : E} (hv : ‖v‖ = 1) : 𝕜 →ₗᵢ[𝕜] E :=
  { LinearMap.toSpanSingleton 𝕜 E v with norm_map' := fun x => by simp [norm_smul, hv] }
#align linear_isometry.to_span_singleton LinearIsometry.toSpanSingleton

variable {𝕜 E}

set_option synthInstance.etaExperiment true in
@[simp]
theorem _root_.LinearIsometry.toSpanSingleton_apply {v : E} (hv : ‖v‖ = 1) (a : 𝕜) :
    LinearIsometry.toSpanSingleton 𝕜 E hv a = a • v :=
  rfl
#align linear_isometry.to_span_singleton_apply LinearIsometry.toSpanSingleton_apply

@[simp]
theorem _root_.LinearIsometry.coe_toSpanSingleton {v : E} (hv : ‖v‖ = 1) :
    (LinearIsometry.toSpanSingleton 𝕜 E hv).toLinearMap = LinearMap.toSpanSingleton 𝕜 E v :=
  rfl
#align linear_isometry.coe_to_span_singleton LinearIsometry.coe_toSpanSingleton

end

section OpNorm

open Set Real

set_option synthInstance.etaExperiment true in
/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def opNorm (f : E →SL[σ₁₂] F) :=
  infₛ { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ }
#align continuous_linear_map.op_norm ContinuousLinearMap.opNorm

instance hasOpNorm : Norm (E →SL[σ₁₂] F) :=
  ⟨opNorm⟩
#align continuous_linear_map.has_op_norm ContinuousLinearMap.hasOpNorm

set_option synthInstance.etaExperiment true in
theorem norm_def (f : E →SL[σ₁₂] F) : ‖f‖ = infₛ { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  rfl
#align continuous_linear_map.norm_def ContinuousLinearMap.norm_def

set_option synthInstance.etaExperiment true in
-- So that invocations of `le_cinfₛ` make sense: we show that the set of
-- bounds is nonempty and bounded below.
theorem bounds_nonempty [RingHomIsometric σ₁₂] {f : E →SL[σ₁₂] F} :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩
#align continuous_linear_map.bounds_nonempty ContinuousLinearMap.bounds_nonempty

set_option synthInstance.etaExperiment true in
theorem bounds_bddBelow {f : E →SL[σ₁₂] F} : BddBelow { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩
#align continuous_linear_map.bounds_bdd_below ContinuousLinearMap.bounds_bddBelow

set_option synthInstance.etaExperiment true in
/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem op_norm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    ‖f‖ ≤ M :=
  cinfₛ_le bounds_bddBelow ⟨hMp, hM⟩
#align continuous_linear_map.op_norm_le_bound ContinuousLinearMap.op_norm_le_bound

set_option synthInstance.etaExperiment true in
/-- If one controls the norm of every `A x`, `‖x‖ ≠ 0`, then one controls the norm of `A`. -/
theorem op_norm_le_bound' (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ≠ 0 → ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  op_norm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, MulZeroClass.mul_zero, norm_image_of_norm_zero f f.2 h, le_refl]
#align continuous_linear_map.op_norm_le_bound' ContinuousLinearMap.op_norm_le_bound'

set_option synthInstance.etaExperiment true in
theorem op_norm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) : ‖f‖ ≤ K :=
  f.op_norm_le_bound K.2 fun x => by
    simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0
#align continuous_linear_map.op_norm_le_of_lipschitz ContinuousLinearMap.op_norm_le_of_lipschitz

set_option synthInstance.etaExperiment true in
theorem op_norm_eq_of_bounds {φ : E →SL[σ₁₂] F} {M : ℝ} (M_nonneg : 0 ≤ M)
    (h_above : ∀ x, ‖φ x‖ ≤ M * ‖x‖) (h_below : ∀ N ≥ 0, (∀ x, ‖φ x‖ ≤ N * ‖x‖) → M ≤ N) :
    ‖φ‖ = M :=
  le_antisymm (φ.op_norm_le_bound M_nonneg h_above)
    ((le_cinfₛ_iff ContinuousLinearMap.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)
#align continuous_linear_map.op_norm_eq_of_bounds ContinuousLinearMap.op_norm_eq_of_bounds

theorem op_norm_neg (f : E →SL[σ₁₂] F) : ‖-f‖ = ‖f‖ := by simp only [norm_def, neg_apply, norm_neg]
#align continuous_linear_map.op_norm_neg ContinuousLinearMap.op_norm_neg

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G)
  (x : E)

theorem op_norm_nonneg : 0 ≤ ‖f‖ :=
  le_cinfₛ bounds_nonempty fun _ ⟨hx, _⟩ => hx
#align continuous_linear_map.op_norm_nonneg ContinuousLinearMap.op_norm_nonneg

set_option synthInstance.etaExperiment true in
/-- The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
theorem le_op_norm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := by
  obtain ⟨C, _, hC⟩ := f.bound
  replace hC := hC x
  by_cases h : ‖x‖ = 0
  · rwa [h, MulZeroClass.mul_zero] at hC⊢
  have hlt : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
  exact
    (div_le_iff hlt).mp
      (le_cinfₛ bounds_nonempty fun c ⟨_, hc⟩ => (div_le_iff hlt).mpr <| by apply hc)
#align continuous_linear_map.le_op_norm ContinuousLinearMap.le_op_norm

set_option synthInstance.etaExperiment true in
theorem dist_le_op_norm (x y : E) : dist (f x) (f y) ≤ ‖f‖ * dist x y := by
  simp_rw [dist_eq_norm, ← map_sub, f.le_op_norm]
#align continuous_linear_map.dist_le_op_norm ContinuousLinearMap.dist_le_op_norm

set_option synthInstance.etaExperiment true in
theorem le_op_norm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
  le_trans (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)
#align continuous_linear_map.le_op_norm_of_le ContinuousLinearMap.le_op_norm_of_le

set_option synthInstance.etaExperiment true in
theorem le_of_op_norm_le {c : ℝ} (h : ‖f‖ ≤ c) (x : E) : ‖f x‖ ≤ c * ‖x‖ :=
  (f.le_op_norm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))
#align continuous_linear_map.le_of_op_norm_le ContinuousLinearMap.le_of_op_norm_le

set_option synthInstance.etaExperiment true in
theorem ratio_le_op_norm : ‖f x‖ / ‖x‖ ≤ ‖f‖ :=
  div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)
#align continuous_linear_map.ratio_le_op_norm ContinuousLinearMap.ratio_le_op_norm

set_option synthInstance.etaExperiment true in
/-- The image of the unit ball under a continuous linear map is bounded. -/
theorem unit_le_op_norm : ‖x‖ ≤ 1 → ‖f x‖ ≤ ‖f‖ :=
  mul_one ‖f‖ ▸ f.le_op_norm_of_le
#align continuous_linear_map.unit_le_op_norm ContinuousLinearMap.unit_le_op_norm

set_option synthInstance.etaExperiment true in
theorem op_norm_le_of_shell {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  f.op_norm_le_bound' hC fun _ hx => SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf hx
#align continuous_linear_map.op_norm_le_of_shell ContinuousLinearMap.op_norm_le_of_shell

set_option synthInstance.etaExperiment true in
theorem op_norm_le_of_ball {f : E →SL[σ₁₂] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
    (hf : ∀ x ∈ ball (0 : E) ε, ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine' op_norm_le_of_shell ε_pos hC hc fun x _ hx => hf x _
  rwa [ball_zero_eq]
#align continuous_linear_map.op_norm_le_of_ball ContinuousLinearMap.op_norm_le_of_ball

set_option synthInstance.etaExperiment true in
theorem op_norm_le_of_nhds_zero {f : E →SL[σ₁₂] F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  let ⟨_, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf
  op_norm_le_of_ball ε0 hC hε
#align continuous_linear_map.op_norm_le_of_nhds_zero ContinuousLinearMap.op_norm_le_of_nhds_zero

set_option synthInstance.etaExperiment true in
theorem op_norm_le_of_shell' {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : ‖c‖ < 1) (hf : ∀ x, ε * ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  by_cases h0 : c = 0
  · refine' op_norm_le_of_ball ε_pos hC fun x hx => hf x _ _
    · simp [h0]
    · rwa [ball_zero_eq] at hx
  · rw [← inv_inv c, norm_inv, inv_lt_one_iff_of_pos (norm_pos_iff.2 <| inv_ne_zero h0)] at hc
    refine' op_norm_le_of_shell ε_pos hC hc _
    rwa [norm_inv, div_eq_mul_inv, inv_inv]
#align continuous_linear_map.op_norm_le_of_shell' ContinuousLinearMap.op_norm_le_of_shell'

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖ = 1`, then
one controls the norm of `f`. -/
theorem op_norm_le_of_unit_norm [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E →L[ℝ] F} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖x‖ = 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  refine' op_norm_le_bound' f hC fun x hx => _
  have H₁ : ‖‖x‖⁻¹ • x‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel hx]
  have H₂ := hf _ H₁
  rwa [map_smul, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul, _root_.div_le_iff] at H₂
  exact (norm_nonneg x).lt_of_ne' hx
#align continuous_linear_map.op_norm_le_of_unit_norm ContinuousLinearMap.op_norm_le_of_unit_norm

set_option synthInstance.etaExperiment true in
/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  (f + g).op_norm_le_bound (add_nonneg f.op_norm_nonneg g.op_norm_nonneg) fun x =>
    (norm_add_le_of_le (f.le_op_norm x) (g.le_op_norm x)).trans_eq (add_mul _ _ _).symm
#align continuous_linear_map.op_norm_add_le ContinuousLinearMap.op_norm_add_le

set_option synthInstance.etaExperiment true in
/-- The norm of the `0` operator is `0`. -/
theorem op_norm_zero : ‖(0 : E →SL[σ₁₂] F)‖ = 0 :=
  le_antisymm (cinfₛ_le bounds_bddBelow ⟨le_rfl, fun _ => le_of_eq (by
    rw [MulZeroClass.zero_mul]
    exact norm_zero)⟩) (op_norm_nonneg _)
#align continuous_linear_map.op_norm_zero ContinuousLinearMap.op_norm_zero

set_option synthInstance.etaExperiment true in
/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
theorem norm_id_le : ‖id 𝕜 E‖ ≤ 1 :=
  op_norm_le_bound _ zero_le_one fun x => by simp
#align continuous_linear_map.norm_id_le ContinuousLinearMap.norm_id_le

set_option synthInstance.etaExperiment true in
/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
theorem norm_id_of_nontrivial_seminorm (h : ∃ x : E, ‖x‖ ≠ 0) : ‖id 𝕜 E‖ = 1 :=
  le_antisymm norm_id_le <| by
    let ⟨x, hx⟩ := h
    have := (id 𝕜 E).ratio_le_op_norm x
    rwa [id_apply, div_self hx] at this
#align continuous_linear_map.norm_id_of_nontrivial_seminorm ContinuousLinearMap.norm_id_of_nontrivial_seminorm

set_option synthInstance.etaExperiment true in
theorem op_norm_smul_le {𝕜' : Type _} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
    (c : 𝕜') (f : E →SL[σ₁₂] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
  (c • f).op_norm_le_bound (mul_nonneg (norm_nonneg _) (op_norm_nonneg _)) fun _ => by
    erw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
#align continuous_linear_map.op_norm_smul_le ContinuousLinearMap.op_norm_smul_le

set_option synthInstance.etaExperiment true in
/-- Continuous linear maps themselves form a seminormed space with respect to
the operator norm. This is only a temporary definition because we want to replace the topology
with `ContinuousLinearMap.topologicalSpace` to avoid diamond issues.
See Note [forgetful inheritance] -/
protected def tmpSeminormedAddCommGroup : SeminormedAddCommGroup (E →SL[σ₁₂] F) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := norm
      map_zero' := op_norm_zero
      add_le' := op_norm_add_le
      neg' := op_norm_neg }
#align continuous_linear_map.tmp_seminormed_add_comm_group ContinuousLinearMap.tmpSeminormedAddCommGroup

/-- The `PseudoMetricSpace` structure on `E →SL[σ₁₂] F` coming from
`ContinuousLinearMap.tmpSeminormedAddCommGroup`.
See Note [forgetful inheritance] -/
protected def tmpPseudoMetricSpace : PseudoMetricSpace (E →SL[σ₁₂] F) :=
  ContinuousLinearMap.tmpSeminormedAddCommGroup.toPseudoMetricSpace
#align continuous_linear_map.tmp_pseudo_metric_space ContinuousLinearMap.tmpPseudoMetricSpace

/-- The `UniformSpace` structure on `E →SL[σ₁₂] F` coming from
`ContinuousLinearMap.tmpSeminormedAddCommGroup`.
See Note [forgetful inheritance] -/
protected def tmpUniformSpace : UniformSpace (E →SL[σ₁₂] F) :=
  ContinuousLinearMap.tmpPseudoMetricSpace.toUniformSpace
#align continuous_linear_map.tmp_uniform_space ContinuousLinearMap.tmpUniformSpace

/-- The `TopologicalSpace` structure on `E →SL[σ₁₂] F` coming from
`ContinuousLinearMap.tmpSeminormedAddCommGroup`.
See Note [forgetful inheritance] -/
protected def tmpTopologicalSpace : TopologicalSpace (E →SL[σ₁₂] F) :=
  ContinuousLinearMap.tmpUniformSpace.toTopologicalSpace
#align continuous_linear_map.tmp_topological_space ContinuousLinearMap.tmpTopologicalSpace

section Tmp

attribute [-instance] ContinuousLinearMap.topologicalSpace

attribute [-instance] ContinuousLinearMap.uniformSpace

attribute [local instance] ContinuousLinearMap.tmpSeminormedAddCommGroup

set_option synthInstance.etaExperiment true in
protected theorem tmpTopologicalAddGroup : TopologicalAddGroup (E →SL[σ₁₂] F) :=
  inferInstance
#align continuous_linear_map.tmp_topological_add_group ContinuousLinearMap.tmpTopologicalAddGroup

set_option synthInstance.etaExperiment true in
protected theorem tmp_closedBall_div_subset {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    closedBall (0 : E →SL[σ₁₂] F) (a / b) ⊆
      { f | ∀ x ∈ closedBall (0 : E) b, f x ∈ closedBall (0 : F) a } := by
  intro f hf x hx
  rw [mem_closedBall_zero_iff] at hf hx⊢
  calc
    ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_op_norm _ _
    _ ≤ a / b * b := (mul_le_mul hf hx (norm_nonneg _) (div_pos ha hb).le)
    _ = a := div_mul_cancel a hb.ne.symm
#align continuous_linear_map.tmp_closed_ball_div_subset ContinuousLinearMap.tmp_closedBall_div_subset

end Tmp

set_option synthInstance.etaExperiment true in
protected theorem tmp_topology_eq :
    (ContinuousLinearMap.tmpTopologicalSpace : TopologicalSpace (E →SL[σ₁₂] F)) =
      ContinuousLinearMap.topologicalSpace := by
  refine'
    ContinuousLinearMap.tmpTopologicalAddGroup.ext inferInstance
      ((@Metric.nhds_basis_closedBall _ ContinuousLinearMap.tmpPseudoMetricSpace 0).ext
        (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall) _ _)
  · rcases NormedField.exists_norm_lt_one 𝕜 with ⟨c, hc₀, hc₁⟩
    intro ε hε
    refine' ⟨⟨closedBall 0 (1 / ‖c‖), ε⟩, ⟨⟨_, hε⟩, _⟩⟩
    · exact NormedSpace.isVonNBounded_closedBall _ _ _
    intro f (hf : ∀ x, _)
    simp_rw [mem_closedBall_zero_iff] at hf
    convert (@mem_closedBall_zero_iff _ (_) f ε).2 _ -- Porting note: needed `convert`
    refine' op_norm_le_of_shell' (div_pos one_pos hc₀) hε.le hc₁ fun x hx₁ hxc => _
    rw [div_mul_cancel 1 hc₀.ne.symm] at hx₁
    exact (hf x hxc.le).trans (le_mul_of_one_le_right hε.le hx₁)
  · rintro ⟨S, ε⟩ ⟨hS, hε⟩
    rw [NormedSpace.isVonNBounded_iff, ← bounded_iff_isBounded] at hS
    rcases hS.subset_ball_lt 0 0 with ⟨δ, hδ, hSδ⟩
    exact ⟨ε / δ, div_pos hε hδ,
      (ContinuousLinearMap.tmp_closedBall_div_subset hε hδ).trans fun f hf x hx => hf x <| hSδ hx⟩
#align continuous_linear_map.tmp_topology_eq ContinuousLinearMap.tmp_topology_eq

set_option synthInstance.etaExperiment true in
protected theorem tmpUniformSpace_eq :
    (ContinuousLinearMap.tmpUniformSpace : UniformSpace (E →SL[σ₁₂] F)) =
      ContinuousLinearMap.uniformSpace := by
  rw [← @UniformAddGroup.toUniformSpace_eq _ ContinuousLinearMap.tmpUniformSpace, ←
    @UniformAddGroup.toUniformSpace_eq _ ContinuousLinearMap.uniformSpace]
  congr! 1
  exact ContinuousLinearMap.tmp_topology_eq
#align continuous_linear_map.tmp_uniform_space_eq ContinuousLinearMap.tmpUniformSpace_eq

instance toPseudoMetricSpace : PseudoMetricSpace (E →SL[σ₁₂] F) :=
  ContinuousLinearMap.tmpPseudoMetricSpace.replaceUniformity
    (congr_arg _ ContinuousLinearMap.tmpUniformSpace_eq.symm)
#align continuous_linear_map.to_pseudo_metric_space ContinuousLinearMap.toPseudoMetricSpace

set_option synthInstance.etaExperiment true in
set_option maxHeartbeats 1600000 in
/-- Continuous linear maps themselves form a seminormed space with respect to
    the operator norm. -/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (E →SL[σ₁₂] F) where
  dist_eq := ContinuousLinearMap.tmpSeminormedAddCommGroup.dist_eq
#align continuous_linear_map.to_seminormed_add_comm_group ContinuousLinearMap.toSeminormedAddCommGroup

set_option synthInstance.etaExperiment true in
theorem nnnorm_def (f : E →SL[σ₁₂] F) : ‖f‖₊ = infₛ { c | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ } := by
  ext
  rw [NNReal.coe_infₛ, coe_nnnorm, norm_def, NNReal.coe_image]
  -- Porting note: this was `simp_rw`, and can probably be optimised.
  simp [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_setOf_eq, Subtype.coe_mk,
    exists_prop]
#align continuous_linear_map.nnnorm_def ContinuousLinearMap.nnnorm_def

set_option synthInstance.etaExperiment true in
/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem op_nnnorm_le_bound (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖f x‖₊ ≤ M * ‖x‖₊) : ‖f‖₊ ≤ M :=
  op_norm_le_bound f (zero_le M) hM
#align continuous_linear_map.op_nnnorm_le_bound ContinuousLinearMap.op_nnnorm_le_bound

set_option synthInstance.etaExperiment true in
/-- If one controls the norm of every `A x`, `‖x‖₊ ≠ 0`, then one controls the norm of `A`. -/
theorem op_nnnorm_le_bound' (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖x‖₊ ≠ 0 → ‖f x‖₊ ≤ M * ‖x‖₊) :
    ‖f‖₊ ≤ M :=
  op_norm_le_bound' f (zero_le M) fun x hx => hM x <| by rwa [← NNReal.coe_ne_zero]
#align continuous_linear_map.op_nnnorm_le_bound' ContinuousLinearMap.op_nnnorm_le_bound'

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖₊ = 1`, then
one controls the norm of `f`. -/
theorem op_nnnorm_le_of_unit_nnnorm [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E →L[ℝ] F} {C : ℝ≥0}
    (hf : ∀ x, ‖x‖₊ = 1 → ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ C :=
  op_norm_le_of_unit_norm C.coe_nonneg fun x hx => hf x <| by rwa [← NNReal.coe_eq_one]
#align continuous_linear_map.op_nnnorm_le_of_unit_nnnorm ContinuousLinearMap.op_nnnorm_le_of_unit_nnnorm

set_option synthInstance.etaExperiment true in
theorem op_nnnorm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ‖f‖₊ ≤ K :=
  op_norm_le_of_lipschitz hf
#align continuous_linear_map.op_nnnorm_le_of_lipschitz ContinuousLinearMap.op_nnnorm_le_of_lipschitz

set_option synthInstance.etaExperiment true in
theorem op_nnnorm_eq_of_bounds {φ : E →SL[σ₁₂] F} (M : ℝ≥0) (h_above : ∀ x, ‖φ x‖ ≤ M * ‖x‖)
    (h_below : ∀ N, (∀ x, ‖φ x‖₊ ≤ N * ‖x‖₊) → M ≤ N) : ‖φ‖₊ = M :=
  Subtype.ext <| op_norm_eq_of_bounds (zero_le M) h_above <| Subtype.forall'.mpr h_below
#align continuous_linear_map.op_nnnorm_eq_of_bounds ContinuousLinearMap.op_nnnorm_eq_of_bounds

set_option synthInstance.etaExperiment true in
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 80000 in
instance toNormedSpace {𝕜' : Type _} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] :
    NormedSpace 𝕜' (E →SL[σ₁₂] F) :=
  ⟨op_norm_smul_le⟩
#align continuous_linear_map.to_normed_space ContinuousLinearMap.toNormedSpace

set_option synthInstance.etaExperiment true in
/-- The operator norm is submultiplicative. -/
theorem op_norm_comp_le (f : E →SL[σ₁₂] F) : ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
  cinfₛ_le bounds_bddBelow
    ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _), fun x => by
      rw [mul_assoc]
      exact h.le_op_norm_of_le (f.le_op_norm x)⟩
#align continuous_linear_map.op_norm_comp_le ContinuousLinearMap.op_norm_comp_le

set_option synthInstance.etaExperiment true in
theorem op_nnnorm_comp_le [RingHomIsometric σ₁₃] (f : E →SL[σ₁₂] F) : ‖h.comp f‖₊ ≤ ‖h‖₊ * ‖f‖₊ :=
  op_norm_comp_le h f
#align continuous_linear_map.op_nnnorm_comp_le ContinuousLinearMap.op_nnnorm_comp_le

set_option synthInstance.etaExperiment true in
/-- Continuous linear maps form a seminormed ring with respect to the operator norm. -/
instance toSemiNormedRing : SeminormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toSeminormedAddCommGroup, ContinuousLinearMap.ring with
    norm_mul := fun f g => op_norm_comp_le f g }
#align continuous_linear_map.to_semi_normed_ring ContinuousLinearMap.toSemiNormedRing

end

end OpNorm

end ContinuousLinearMap

namespace LinearMap

set_option synthInstance.etaExperiment true in
/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
theorem mkContinuous_norm_le (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ C :=
  ContinuousLinearMap.op_norm_le_bound _ hC h
#align linear_map.mk_continuous_norm_le LinearMap.mkContinuous_norm_le

set_option synthInstance.etaExperiment true in
/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
theorem mkContinuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ max C 0 :=
  ContinuousLinearMap.op_norm_le_bound _ (le_max_right _ _) fun x =>
    (h x).trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)
#align linear_map.mk_continuous_norm_le' LinearMap.mkContinuous_norm_le'

variable [RingHomIsometric σ₂₃]

set_option synthInstance.etaExperiment true in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
def mkContinuous₂_aux (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
    E →ₛₗ[σ₁₃] F →SL[σ₂₃] G :=
{ toFun := fun x => (f x).mkContinuous (C * ‖x‖) (hC x)
  map_add' := fun x y => by
    ext z
    rw [ContinuousLinearMap.add_apply, mkContinuous_apply, mkContinuous_apply,
      mkContinuous_apply, map_add, add_apply]
  map_smul' := fun c x => by
    ext z
    rw [ContinuousLinearMap.smul_apply, mkContinuous_apply, mkContinuous_apply, map_smulₛₗ,
      smul_apply] }

set_option synthInstance.etaExperiment true in
theorem mkContinuous₂_aux_norm_le'
  (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖)  (x : E) :
    ‖f.mkContinuous₂_aux C hC x‖ ≤ max (C * ‖x‖) 0 :=
  mkContinuous_norm_le' _ (hC x)

set_option synthInstance.etaExperiment true in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and a bound on the norm of the image. The linear map can be constructed using
`LinearMap.mk₂`. -/
def mkContinuous₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
    E →SL[σ₁₃] F →SL[σ₂₃] G :=
  LinearMap.mkContinuous
    (mkContinuous₂_aux f C hC)
    (max C 0) fun x => (mkContinuous₂_aux_norm_le' f C hC x).trans_eq <| by
      rw [max_mul_of_nonneg _ _ (norm_nonneg x), MulZeroClass.zero_mul]
#align linear_map.mk_continuous₂ LinearMap.mkContinuous₂

set_option synthInstance.etaExperiment true in
@[simp]
theorem mkContinuous₂_apply (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) (y : F) : f.mkContinuous₂ C hC x y = f x y :=
  rfl
#align linear_map.mk_continuous₂_apply LinearMap.mkContinuous₂_apply

set_option synthInstance.etaExperiment true in
theorem mkContinuous₂_norm_le' (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ max C 0 :=
  mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) _
#align linear_map.mk_continuous₂_norm_le' LinearMap.mkContinuous₂_norm_le'

set_option synthInstance.etaExperiment true in
theorem mkContinuous₂_norm_le (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ C :=
  (f.mkContinuous₂_norm_le' hC).trans_eq <| max_eq_left h0
#align linear_map.mk_continuous₂_norm_le LinearMap.mkContinuous₂_norm_le

end LinearMap

end SemiNormed

section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

open Metric ContinuousLinearMap

section

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f g : E →SL[σ₁₂] F) (x y z : E)

namespace ContinuousLinearMap

section OpNorm

open Set Real

set_option synthInstance.etaExperiment true in
/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff [RingHomIsometric σ₁₂] : ‖f‖ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn =>
      ContinuousLinearMap.ext fun x =>
        norm_le_zero_iff.1
          (calc
            _ ≤ ‖f‖ * ‖x‖ := le_op_norm _ _
            _ = _ := by rw [hn, MulZeroClass.zero_mul]))
    (by
      rintro rfl
      exact op_norm_zero)
#align continuous_linear_map.op_norm_zero_iff ContinuousLinearMap.op_norm_zero_iff

set_option synthInstance.etaExperiment true in
/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
@[simp]
theorem norm_id [Nontrivial E] : ‖id 𝕜 E‖ = 1 := by
  refine' norm_id_of_nontrivial_seminorm _
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact ⟨x, ne_of_gt (norm_pos_iff.2 hx)⟩
#align continuous_linear_map.norm_id ContinuousLinearMap.norm_id

set_option synthInstance.etaExperiment true in
instance normOneClass [Nontrivial E] : NormOneClass (E →L[𝕜] E) :=
  ⟨norm_id⟩
#align continuous_linear_map.norm_one_class ContinuousLinearMap.normOneClass

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance toNormedAddCommGroup [RingHomIsometric σ₁₂] : NormedAddCommGroup (E →SL[σ₁₂] F) :=
  NormedAddCommGroup.ofSeparation fun f => (op_norm_zero_iff f).mp
#align continuous_linear_map.to_normed_add_comm_group ContinuousLinearMap.toNormedAddCommGroup

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
instance toNormedRing : NormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toNormedAddCommGroup, ContinuousLinearMap.toSemiNormedRing with }
#align continuous_linear_map.to_normed_ring ContinuousLinearMap.toNormedRing

end OpNorm

end ContinuousLinearMap

end

end Normed
