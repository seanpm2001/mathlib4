/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.ODE.gronwall
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Grönwall's inequality

The main technical result of this file is the Grönwall-like inequality
`norm_le_gronwallBound_of_norm_deriv_right_le`. It states that if `f : ℝ → E` satisfies `‖f a‖ ≤ δ`
and `∀ x ∈ [a, b), ‖f' x‖ ≤ K * ‖f x‖ + ε`, then for all `x ∈ [a, b]` we have `‖f x‖ ≤ δ * exp (K *
x) + (ε / K) * (exp (K * x) - 1)`.

Then we use this inequality to prove some estimates on the possible rate of growth of the distance
between two approximate or exact solutions of an ordinary differential equation.

The proofs are based on [Hubbard and West, *Differential Equations: A Dynamical Systems Approach*,
Sec. 4.5][HubbardWest-ode], where `norm_le_gronwallBound_of_norm_deriv_right_le` is called
“Fundamental Inequality”.

## TODO

- Once we have FTC, prove an inequality for a function satisfying `‖f' x‖ ≤ K x * ‖f x‖ + ε`,
  or more generally `liminf_{y→x+0} (f y - f x)/(y - x) ≤ K x * f x + ε` with any sign
  of `K x` and `f x`.
-/


variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

open Metric Set Asymptotics Filter Real

open scoped Classical Topology NNReal

/-! ### Technical lemmas about `gronwallBound` -/


/-- Upper bound used in several Grönwall-like inequalities. -/
noncomputable def gronwallBound (δ K ε x : ℝ) : ℝ :=
  if K = 0 then δ + ε * x else δ * exp (K * x) + ε / K * (exp (K * x) - 1)
#align gronwall_bound gronwallBound

theorem gronwallBound_K0 (δ ε : ℝ) : gronwallBound δ 0 ε = fun x => δ + ε * x :=
  funext fun _ => if_pos rfl
set_option linter.uppercaseLean3 false in
#align gronwall_bound_K0 gronwallBound_K0

theorem gronwallBound_of_K_ne_0 {δ K ε : ℝ} (hK : K ≠ 0) :
    gronwallBound δ K ε = fun x => δ * exp (K * x) + ε / K * (exp (K * x) - 1) :=
  funext fun _ => if_neg hK
set_option linter.uppercaseLean3 false in
#align gronwall_bound_of_K_ne_0 gronwallBound_of_K_ne_0

theorem hasDerivAt_gronwallBound (δ K ε x : ℝ) :
    HasDerivAt (gronwallBound δ K ε) (K * gronwallBound δ K ε x + ε) x := by
  by_cases hK : K = 0
  · subst K
    simp only [gronwallBound_K0, MulZeroClass.zero_mul, zero_add]
    convert ((hasDerivAt_id x).const_mul ε).const_add δ
    rw [mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK]
    convert (((hasDerivAt_id x).const_mul K).exp.const_mul δ).add
      ((((hasDerivAt_id x).const_mul K).exp.sub_const 1).const_mul (ε / K)) using 1
    simp only [id, mul_add, (mul_assoc _ _ _).symm, mul_comm _ K, mul_div_cancel' _ hK]
    ring
#align has_deriv_at_gronwall_bound hasDerivAt_gronwallBound

theorem hasDerivAt_gronwallBound_shift (δ K ε x a : ℝ) :
    HasDerivAt (fun y => gronwallBound δ K ε (y - a)) (K * gronwallBound δ K ε (x - a) + ε) x := by
  convert (hasDerivAt_gronwallBound δ K ε _).comp x ((hasDerivAt_id x).sub_const a) using 1
  rw [id, mul_one]
#align has_deriv_at_gronwall_bound_shift hasDerivAt_gronwallBound_shift

theorem gronwallBound_x0 (δ K ε : ℝ) : gronwallBound δ K ε 0 = δ := by
  by_cases hK : K = 0
  · simp only [gronwallBound, if_pos hK, MulZeroClass.mul_zero, add_zero]
  · simp only [gronwallBound, if_neg hK, MulZeroClass.mul_zero, exp_zero, sub_self, mul_one,
      add_zero]
#align gronwall_bound_x0 gronwallBound_x0

theorem gronwallBound_ε0 (δ K x : ℝ) : gronwallBound δ K 0 x = δ * exp (K * x) := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK, MulZeroClass.zero_mul, exp_zero, add_zero, mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK, zero_div, MulZeroClass.zero_mul, add_zero]
#align gronwall_bound_ε0 gronwallBound_ε0

theorem gronwallBound_ε0_δ0 (K x : ℝ) : gronwallBound 0 K 0 x = 0 := by
  simp only [gronwallBound_ε0, MulZeroClass.zero_mul]
#align gronwall_bound_ε0_δ0 gronwallBound_ε0_δ0

theorem gronwallBound_continuous_ε (δ K x : ℝ) : Continuous fun ε => gronwallBound δ K ε x := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK]
    exact continuous_const.add (continuous_id.mul continuous_const)
  · simp only [gronwallBound_of_K_ne_0 hK]
    exact continuous_const.add ((continuous_id.mul continuous_const).mul continuous_const)
#align gronwall_bound_continuous_ε gronwallBound_continuous_ε

/-! ### Inequality and corollaries -/

/-- A Grönwall-like inequality: if `f : ℝ → ℝ` is continuous on `[a, b]` and satisfies
the inequalities `f a ≤ δ` and
`∀ x ∈ [a, b), liminf_{z→x+0} (f z - f x)/(z - x) ≤ K * (f x) + ε`, then `f x`
is bounded by `gronwallBound δ K ε (x - a)` on `[a, b]`.

See also `norm_le_gronwallBound_of_norm_deriv_right_le` for a version bounding `‖f x‖`,
`f : ℝ → E`. -/
theorem le_gronwallBound_of_liminf_deriv_right_le {f f' : ℝ → ℝ} {δ K ε : ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r)
    (ha : f a ≤ δ) (bound : ∀ x ∈ Ico a b, f' x ≤ K * f x + ε) :
    ∀ x ∈ Icc a b, f x ≤ gronwallBound δ K ε (x - a) := by
  have H : ∀ x ∈ Icc a b, ∀ ε' ∈ Ioi ε, f x ≤ gronwallBound δ K ε' (x - a) := by
    intro x hx ε' hε'
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hf'
    · rwa [sub_self, gronwallBound_x0]
    · exact fun x => hasDerivAt_gronwallBound_shift δ K ε' x a
    · intro x hx hfB
      rw [← hfB]
      apply lt_of_le_of_lt (bound x hx)
      exact add_lt_add_left (mem_Ioi.1 hε') _
    · exact hx
  intro x hx
  change f x ≤ (fun ε' => gronwallBound δ K ε' (x - a)) ε
  convert continuousWithinAt_const.closure_le _ _ (H x hx)
  · simp only [closure_Ioi, left_mem_Ici]
  exact (gronwallBound_continuous_ε δ K (x - a)).continuousWithinAt
#align le_gronwall_bound_of_liminf_deriv_right_le le_gronwallBound_of_liminf_deriv_right_le

/-- A Grönwall-like inequality: if `f : ℝ → E` is continuous on `[a, b]`, has right derivative
`f' x` at every point `x ∈ [a, b)`, and satisfies the inequalities `‖f a‖ ≤ δ`,
`∀ x ∈ [a, b), ‖f' x‖ ≤ K * ‖f x‖ + ε`, then `‖f x‖` is bounded by `gronwallBound δ K ε (x - a)`
on `[a, b]`. -/
theorem norm_le_gronwallBound_of_norm_deriv_right_le {f f' : ℝ → E} {δ K ε : ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : ‖f a‖ ≤ δ) (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖ + ε) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ gronwallBound δ K ε (x - a) :=
  le_gronwallBound_of_liminf_deriv_right_le (continuous_norm.comp_continuousOn hf)
    (fun x hx _r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha bound
#align norm_le_gronwall_bound_of_norm_deriv_right_le norm_le_gronwallBound_of_norm_deriv_right_le

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_approx_trajectories_ODE_of_mem_set {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ}
    (hv : ∀ t, ∀ᵉ (x ∈ s t) (y ∈ s t), dist (v t x) (v t y) ≤ K * dist x y)
    {f g f' g' : ℝ → E} {a b : ℝ} {εf εg δ : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf) (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg) (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) := by
  simp only [dist_eq_norm] at ha ⊢
  have h_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => f t - g t) (f' t - g' t) (Ici t) t :=
    fun t ht => (hf' t ht).sub (hg' t ht)
  apply norm_le_gronwallBound_of_norm_deriv_right_le (hf.sub hg) h_deriv ha
  intro t ht
  have := dist_triangle4_right (f' t) (g' t) (v t (f t)) (v t (g t))
  rw [dist_eq_norm] at this 
  refine' this.trans ((add_le_add (add_le_add (f_bound t ht) (g_bound t ht))
    (hv t (f t) (hfs t ht) (g t) (hgs t ht))).trans _)
  rw [dist_eq_norm, add_comm]
set_option linter.uppercaseLean3 false in
#align dist_le_of_approx_trajectories_ODE_of_mem_set dist_le_of_approx_trajectories_ODE_of_mem_set

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_approx_trajectories_ODE {v : ℝ → E → E} {K : ℝ≥0}
    (hv : ∀ t, LipschitzWith K (v t)) {f g f' g' : ℝ → E} {a b : ℝ} {εf εg δ : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf) (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg) (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  dist_le_of_approx_trajectories_ODE_of_mem_set (fun t x _ y _ => (hv t).dist_le_mul x y) hf hf'
    f_bound hfs hg hg' g_bound (fun _ _ => trivial) ha
set_option linter.uppercaseLean3 false in
#align dist_le_of_approx_trajectories_ODE dist_le_of_approx_trajectories_ODE

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_trajectories_ODE_of_mem_set {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ}
    (hv : ∀ t, ∀ᵉ (x ∈ s t) (y ∈ s t), dist (v t x) (v t y) ≤ K * dist x y)
    {f g : ℝ → E} {a b : ℝ} {δ : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t) (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t) (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) := by
  have f_bound : ∀ t ∈ Ico a b, dist (v t (f t)) (v t (f t)) ≤ 0 := by intros; rw [dist_self]
  have g_bound : ∀ t ∈ Ico a b, dist (v t (g t)) (v t (g t)) ≤ 0 := by intros; rw [dist_self]
  intro t ht
  have :=
    dist_le_of_approx_trajectories_ODE_of_mem_set hv hf hf' f_bound hfs hg hg' g_bound hgs ha t ht
  rwa [zero_add, gronwallBound_ε0] at this 
set_option linter.uppercaseLean3 false in
#align dist_le_of_trajectories_ODE_of_mem_set dist_le_of_trajectories_ODE_of_mem_set

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_trajectories_ODE {v : ℝ → E → E} {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {f g : ℝ → E} {a b : ℝ} {δ : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t) (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t) (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  dist_le_of_trajectories_ODE_of_mem_set (fun t x _ y _ => (hv t).dist_le_mul x y) hf hf' hfs hg
    hg' (fun _ _ => trivial) ha
set_option linter.uppercaseLean3 false in
#align dist_le_of_trajectories_ODE dist_le_of_trajectories_ODE

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) in a set `s ⊆ ℝ × E` with
a given initial value provided that RHS is Lipschitz continuous in `x` within `s`,
and we consider only solutions included in `s`. -/
theorem ODE_solution_unique_of_mem_set {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ}
    (hv : ∀ t, ∀ᵉ (x ∈ s t) (y ∈ s t), dist (v t x) (v t y) ≤ K * dist x y)
    {f g : ℝ → E} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t) (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t) (ha : f a = g a) : ∀ t ∈ Icc a b, f t = g t := fun t ht ↦ by
  have := dist_le_of_trajectories_ODE_of_mem_set hv hf hf' hfs hg hg' hgs (dist_le_zero.2 ha) t ht
  rwa [MulZeroClass.zero_mul, dist_le_zero] at this 
set_option linter.uppercaseLean3 false in
#align ODE_solution_unique_of_mem_set ODE_solution_unique_of_mem_set

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) with
a given initial value provided that RHS is Lipschitz continuous in `x`. -/
theorem ODE_solution_unique {v : ℝ → E → E} {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {f g : ℝ → E} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t) (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t) (ha : f a = g a) :
    ∀ t ∈ Icc a b, f t = g t :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  ODE_solution_unique_of_mem_set (fun t x _ y _ => (hv t).dist_le_mul x y) hf hf' hfs hg hg'
    (fun _ _ => trivial) ha
set_option linter.uppercaseLean3 false in
#align ODE_solution_unique ODE_solution_unique

