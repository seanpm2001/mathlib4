/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module sorgenfrey_line
! leanprover-community/mathlib commit 328375597f2c0dd00522d9c2e5a33b6a6128feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.Irrational
import Mathbin.Topology.Algebra.Order.Archimedean
import Mathbin.Topology.Paracompact
import Mathbin.Topology.MetricSpace.Metrizable
import Mathbin.Topology.MetricSpace.EmetricParacompact
import Mathbin.Data.Set.Intervals.Monotone

/-!
# Sorgenfrey line

In this file we define `sorgenfrey_line` (notation: `ℝₗ`) to be the Sorgenfrey line. It is the real
line with the topology space structure generated by half-open intervals `set.Ico a b`.

We prove that this line is a completely normal Hausdorff space but its product with itself is not a
normal space. In particular, this implies that the topology on `ℝₗ` is neither metrizable, nor
second countable.

## Notations

- `ℝₗ`: Sorgenfrey line.

## TODO

Prove that the Sorgenfrey line is a paracompact space.

-/


open Set Filter TopologicalSpace

open scoped Topology Filter

namespace Counterexample

noncomputable section

/-- The Sorgenfrey line. It is the real line with the topology space structure generated by
half-open intervals `set.Ico a b`. -/
def SorgenfreyLine : Type :=
  ℝ
deriving ConditionallyCompleteLinearOrder, LinearOrderedField, Archimedean
#align counterexample.sorgenfrey_line Counterexample.SorgenfreyLine

-- mathport name: sorgenfrey_line
scoped[SorgenfreyLine] notation "ℝₗ" => SorgenfreyLine

namespace SorgenfreyLine

/-- Ring homomorphism between the Sorgenfrey line and the standard real line. -/
def toReal : ℝₗ ≃+* ℝ :=
  RingEquiv.refl ℝ
#align counterexample.sorgenfrey_line.to_real Counterexample.SorgenfreyLine.toReal

instance : TopologicalSpace ℝₗ :=
  TopologicalSpace.generateFrom {s : Set ℝₗ | ∃ a b : ℝₗ, Ico a b = s}

theorem isOpen_Ico (a b : ℝₗ) : IsOpen (Ico a b) :=
  TopologicalSpace.GenerateOpen.basic _ ⟨a, b, rfl⟩
#align counterexample.sorgenfrey_line.is_open_Ico Counterexample.SorgenfreyLine.isOpen_Ico

theorem isOpen_Ici (a : ℝₗ) : IsOpen (Ici a) :=
  iUnion_Ico_right a ▸ isOpen_iUnion (isOpen_Ico a)
#align counterexample.sorgenfrey_line.is_open_Ici Counterexample.SorgenfreyLine.isOpen_Ici

theorem nhds_basis_Ico (a : ℝₗ) : (𝓝 a).HasBasis (fun b => a < b) fun b => Ico a b :=
  by
  rw [TopologicalSpace.nhds_generateFrom]
  haveI : Nonempty { x // x ≤ a } := Set.nonempty_Iic_subtype
  have : (⨅ x : { i // i ≤ a }, 𝓟 (Ici ↑x)) = 𝓟 (Ici a) :=
    by
    refine' (IsLeast.isGLB _).iInf_eq
    exact ⟨⟨⟨a, le_rfl⟩, rfl⟩, forall_range_iff.2 fun b => principal_mono.2 <| Ici_subset_Ici.2 b.2⟩
  simp only [mem_set_of_eq, iInf_and, iInf_exists, @iInf_comm _ (_ ∈ _), @iInf_comm _ (Set ℝₗ),
    iInf_iInf_eq_right]
  simp_rw [@iInf_comm _ ℝₗ (_ ≤ _), iInf_subtype', ← Ici_inter_Iio, ← inf_principal, ← inf_iInf, ←
    iInf_inf, this, iInf_subtype]
  suffices : (⨅ x ∈ Ioi a, 𝓟 (Iio x)).HasBasis ((· < ·) a) Iio; exact this.principal_inf _
  refine' has_basis_binfi_principal _ nonempty_Ioi
  exact directedOn_iff_directed.2 (directed_of_inf fun x y hxy => Iio_subset_Iio hxy)
#align counterexample.sorgenfrey_line.nhds_basis_Ico Counterexample.SorgenfreyLine.nhds_basis_Ico

theorem nhds_basis_Ico_rat (a : ℝₗ) :
    (𝓝 a).HasCountableBasis (fun r : ℚ => a < r) fun r => Ico a r :=
  by
  refine'
    ⟨(nhds_basis_Ico a).to_hasBasis (fun b hb => _) fun r hr => ⟨_, hr, subset.rfl⟩,
      Set.to_countable _⟩
  rcases exists_rat_btwn hb with ⟨r, har, hrb⟩
  exact ⟨r, har, Ico_subset_Ico_right hrb.le⟩
#align counterexample.sorgenfrey_line.nhds_basis_Ico_rat Counterexample.SorgenfreyLine.nhds_basis_Ico_rat

theorem nhds_basis_Ico_inv_pNat (a : ℝₗ) :
    (𝓝 a).HasBasis (fun n : ℕ+ => True) fun n => Ico a (a + n⁻¹) :=
  by
  refine'
    (nhds_basis_Ico a).to_hasBasis (fun b hb => _) fun n hn =>
      ⟨_, lt_add_of_pos_right _ (inv_pos.2 <| Nat.cast_pos.2 n.Pos), subset.rfl⟩
  rcases exists_nat_one_div_lt (sub_pos.2 hb) with ⟨k, hk⟩
  rw [one_div] at hk 
  rw [← Nat.cast_add_one] at hk 
  exact ⟨k.succ_pnat, trivial, Ico_subset_Ico_right (le_sub_iff_add_le'.1 hk.le)⟩
#align counterexample.sorgenfrey_line.nhds_basis_Ico_inv_pnat Counterexample.SorgenfreyLine.nhds_basis_Ico_inv_pNat

theorem nhds_countable_basis_Ico_inv_pNat (a : ℝₗ) :
    (𝓝 a).HasCountableBasis (fun n : ℕ+ => True) fun n => Ico a (a + n⁻¹) :=
  ⟨nhds_basis_Ico_inv_pNat a, Set.to_countable _⟩
#align counterexample.sorgenfrey_line.nhds_countable_basis_Ico_inv_pnat Counterexample.SorgenfreyLine.nhds_countable_basis_Ico_inv_pNat

theorem nhds_antitone_basis_Ico_inv_pNat (a : ℝₗ) :
    (𝓝 a).HasAntitoneBasis fun n : ℕ+ => Ico a (a + n⁻¹) :=
  ⟨nhds_basis_Ico_inv_pNat a,
    monotone_const.Ico <|
      Antitone.const_add
        (fun k l hkl => inv_le_inv_of_le (Nat.cast_pos.2 k.Pos) (Nat.mono_cast hkl)) _⟩
#align counterexample.sorgenfrey_line.nhds_antitone_basis_Ico_inv_pnat Counterexample.SorgenfreyLine.nhds_antitone_basis_Ico_inv_pNat

theorem isOpen_iff {s : Set ℝₗ} : IsOpen s ↔ ∀ x ∈ s, ∃ y > x, Ico x y ⊆ s :=
  isOpen_iff_mem_nhds.trans <| forall₂_congr fun x hx => (nhds_basis_Ico x).mem_iff
#align counterexample.sorgenfrey_line.is_open_iff Counterexample.SorgenfreyLine.isOpen_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » s) -/
theorem isClosed_iff {s : Set ℝₗ} : IsClosed s ↔ ∀ (x) (_ : x ∉ s), ∃ y > x, Disjoint (Ico x y) s :=
  by simp only [← isOpen_compl_iff, is_open_iff, mem_compl_iff, subset_compl_iff_disjoint_right]
#align counterexample.sorgenfrey_line.is_closed_iff Counterexample.SorgenfreyLine.isClosed_iff

theorem exists_Ico_disjoint_closed {a : ℝₗ} {s : Set ℝₗ} (hs : IsClosed s) (ha : a ∉ s) :
    ∃ b > a, Disjoint (Ico a b) s :=
  isClosed_iff.1 hs a ha
#align counterexample.sorgenfrey_line.exists_Ico_disjoint_closed Counterexample.SorgenfreyLine.exists_Ico_disjoint_closed

@[simp]
theorem map_toReal_nhds (a : ℝₗ) : map toReal (𝓝 a) = 𝓝[≥] toReal a :=
  by
  refine' ((nhds_basis_Ico a).map _).eq_of_same_basis _
  simpa only [to_real.image_eq_preimage] using nhdsWithin_Ici_basis_Ico (to_real a)
#align counterexample.sorgenfrey_line.map_to_real_nhds Counterexample.SorgenfreyLine.map_toReal_nhds

theorem nhds_eq_map (a : ℝₗ) : 𝓝 a = map toReal.symm (𝓝[≥] a.toReal) := by
  simp_rw [← map_to_real_nhds, map_map, (· ∘ ·), to_real.symm_apply_apply, map_id']
#align counterexample.sorgenfrey_line.nhds_eq_map Counterexample.SorgenfreyLine.nhds_eq_map

theorem nhds_eq_comap (a : ℝₗ) : 𝓝 a = comap toReal (𝓝[≥] a.toReal) := by
  rw [← map_to_real_nhds, comap_map to_real.injective]
#align counterexample.sorgenfrey_line.nhds_eq_comap Counterexample.SorgenfreyLine.nhds_eq_comap

@[continuity]
theorem continuous_toReal : Continuous toReal :=
  continuous_iff_continuousAt.2 fun x => by rw [ContinuousAt, tendsto, map_to_real_nhds];
    exact inf_le_left
#align counterexample.sorgenfrey_line.continuous_to_real Counterexample.SorgenfreyLine.continuous_toReal

instance : OrderClosedTopology ℝₗ :=
  ⟨isClosed_le_prod.Preimage (continuous_toReal.Prod_map continuous_toReal)⟩

instance : ContinuousAdd ℝₗ :=
  by
  refine' ⟨continuous_iff_continuousAt.2 _⟩
  rintro ⟨x, y⟩
  simp only [ContinuousAt, nhds_prod_eq, nhds_eq_map, nhds_eq_comap (x + y), prod_map_map_eq,
    tendsto_comap_iff, tendsto_map'_iff, (· ∘ ·), ← nhdsWithin_prod_eq]
  exact (continuous_add.tendsto _).inf (maps_to.tendsto fun x hx => add_le_add hx.1 hx.2)

theorem isClopen_Ici (a : ℝₗ) : IsClopen (Ici a) :=
  ⟨isOpen_Ici a, isClosed_Ici⟩
#align counterexample.sorgenfrey_line.is_clopen_Ici Counterexample.SorgenfreyLine.isClopen_Ici

theorem isClopen_Iio (a : ℝₗ) : IsClopen (Iio a) := by
  simpa only [compl_Ici] using (is_clopen_Ici a).compl
#align counterexample.sorgenfrey_line.is_clopen_Iio Counterexample.SorgenfreyLine.isClopen_Iio

theorem isClopen_Ico (a b : ℝₗ) : IsClopen (Ico a b) :=
  (isClopen_Ici a).inter (isClopen_Iio b)
#align counterexample.sorgenfrey_line.is_clopen_Ico Counterexample.SorgenfreyLine.isClopen_Ico

instance : TotallyDisconnectedSpace ℝₗ :=
  ⟨fun s hs' hs x hx y hy =>
    le_antisymm (hs.subset_clopen (isClopen_Ici x) ⟨x, hx, le_rfl⟩ hy)
      (hs.subset_clopen (isClopen_Ici y) ⟨y, hy, le_rfl⟩ hx)⟩

instance : FirstCountableTopology ℝₗ :=
  ⟨fun x => (nhds_basis_Ico_rat x).IsCountablyGenerated⟩

/-- Sorgenfrey line is a completely normal Hausdorff topological space. -/
instance : T5Space ℝₗ :=
  by
  /- Let `s` and `t` be disjoint closed sets. For each `x ∈ s` we choose `X x` such that
    `set.Ico x (X x)` is disjoint with `t`. Similarly, for each `y ∈ t` we choose `Y y` such that
    `set.Ico y (Y y)` is disjoint with `s`. Then `⋃ x ∈ s, Ico x (X x)` and `⋃ y ∈ t, Ico y (Y y)` are
    disjoint open sets that include `s` and `t`. -/
  refine' ⟨fun s t hd₁ hd₂ => _⟩
  choose! X hX hXd using fun x (hx : x ∈ s) =>
    exists_Ico_disjoint_closed isClosed_closure (disjoint_left.1 hd₂ hx)
  choose! Y hY hYd using fun y (hy : y ∈ t) =>
    exists_Ico_disjoint_closed isClosed_closure (disjoint_right.1 hd₁ hy)
  refine'
    disjoint_of_disjoint_of_mem _
      (bUnion_mem_nhdsSet fun x hx => (is_open_Ico x (X x)).mem_nhds <| left_mem_Ico.2 (hX x hx))
      (bUnion_mem_nhdsSet fun y hy => (is_open_Ico y (Y y)).mem_nhds <| left_mem_Ico.2 (hY y hy))
  simp only [disjoint_Union_left, disjoint_Union_right, Ico_disjoint_Ico]
  intro y hy x hx
  cases' le_total x y with hle hle
  ·
    calc
      min (X x) (Y y) ≤ X x := min_le_left _ _
      _ ≤ y := (not_lt.1 fun hyx => (hXd x hx).le_bot ⟨⟨hle, hyx⟩, subset_closure hy⟩)
      _ ≤ max x y := le_max_right _ _
  ·
    calc
      min (X x) (Y y) ≤ Y y := min_le_right _ _
      _ ≤ x := (not_lt.1 fun hxy => (hYd y hy).le_bot ⟨⟨hle, hxy⟩, subset_closure hx⟩)
      _ ≤ max x y := le_max_left _ _

theorem denseRange_coe_rat : DenseRange (coe : ℚ → ℝₗ) :=
  by
  refine' dense_iff_inter_open.2 _
  rintro U Uo ⟨x, hx⟩
  rcases is_open_iff.1 Uo _ hx with ⟨y, hxy, hU⟩
  rcases exists_rat_btwn hxy with ⟨z, hxz, hzy⟩
  exact ⟨z, hU ⟨hxz.le, hzy⟩, mem_range_self _⟩
#align counterexample.sorgenfrey_line.dense_range_coe_rat Counterexample.SorgenfreyLine.denseRange_coe_rat

instance : SeparableSpace ℝₗ :=
  ⟨⟨_, countable_range _, denseRange_coe_rat⟩⟩

theorem isClosed_antidiagonal (c : ℝₗ) : IsClosed {x : ℝₗ × ℝₗ | x.1 + x.2 = c} :=
  isClosed_singleton.Preimage continuous_add
#align counterexample.sorgenfrey_line.is_closed_antidiagonal Counterexample.SorgenfreyLine.isClosed_antidiagonal

theorem isClopen_Ici_prod (x : ℝₗ × ℝₗ) : IsClopen (Ici x) :=
  (Ici_prod_eq x).symm ▸ (isClopen_Ici _).Prod (isClopen_Ici _)
#align counterexample.sorgenfrey_line.is_clopen_Ici_prod Counterexample.SorgenfreyLine.isClopen_Ici_prod

/-- Any subset of an antidiagonal `{(x, y) : ℝₗ × ℝₗ| x + y = c}` is a closed set. -/
theorem isClosed_of_subset_antidiagonal {s : Set (ℝₗ × ℝₗ)} {c : ℝₗ}
    (hs : ∀ x : ℝₗ × ℝₗ, x ∈ s → x.1 + x.2 = c) : IsClosed s :=
  by
  rw [← closure_subset_iff_isClosed]
  rintro ⟨x, y⟩ H
  obtain rfl : x + y = c := by
    change (x, y) ∈ {p : ℝₗ × ℝₗ | p.1 + p.2 = c}
    exact closure_minimal (hs : s ⊆ {x | x.1 + x.2 = c}) (is_closed_antidiagonal c) H
  rcases mem_closure_iff.1 H (Ici (x, y)) (is_clopen_Ici_prod _).1 le_rfl with
    ⟨⟨x', y'⟩, ⟨hx : x ≤ x', hy : y ≤ y'⟩, H⟩
  convert H
  · refine' hx.antisymm _
    rwa [← add_le_add_iff_right, hs _ H, add_le_add_iff_left]
  · refine' hy.antisymm _
    rwa [← add_le_add_iff_left, hs _ H, add_le_add_iff_right]
#align counterexample.sorgenfrey_line.is_closed_of_subset_antidiagonal Counterexample.SorgenfreyLine.isClosed_of_subset_antidiagonal

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem nhds_prod_antitone_basis_inv_pNat (x y : ℝₗ) :
    (𝓝 (x, y)).HasAntitoneBasis fun n : ℕ+ => Ico x (x + n⁻¹) ×ˢ Ico y (y + n⁻¹) :=
  by
  rw [nhds_prod_eq]
  exact (nhds_antitone_basis_Ico_inv_pnat x).Prod (nhds_antitone_basis_Ico_inv_pnat y)
#align counterexample.sorgenfrey_line.nhds_prod_antitone_basis_inv_pnat Counterexample.SorgenfreyLine.nhds_prod_antitone_basis_inv_pNat

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of the Sorgenfrey line and itself is not a normal topological space. -/
theorem not_normalSpace_prod : ¬NormalSpace (ℝₗ × ℝₗ) :=
  by
  have h₀ : ∀ {n : ℕ+}, (0 : ℝ) < n⁻¹ := fun n => inv_pos.2 (Nat.cast_pos.2 n.Pos)
  have h₀' : ∀ {n : ℕ+} {x : ℝ}, x < x + n⁻¹ := fun n x => lt_add_of_pos_right _ h₀
  intro
  /- Let `S` be the set of points `(x, y)` on the line `x + y = 0` such that `x` is rational.
    Let `T` be the set of points `(x, y)` on the line `x + y = 0` such that `x` is irrational.
    These sets are closed, see `sorgenfrey_line.is_closed_of_subset_antidiagonal`, and disjoint. -/
  set S := {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ ∃ r : ℚ, ↑r = x.1}
  set T := {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ Irrational x.1.toReal}
  have hSc : IsClosed S := is_closed_of_subset_antidiagonal fun x hx => hx.1
  have hTc : IsClosed T := is_closed_of_subset_antidiagonal fun x hx => hx.1
  have hd : Disjoint S T := by
    rw [disjoint_iff_inf_le]
    rintro ⟨x, y⟩ ⟨⟨-, r, rfl : _ = x⟩, -, hr⟩
    exact r.not_irrational hr
  -- Consider disjoint open sets `U ⊇ S` and `V ⊇ T`.
  rcases normal_separation hSc hTc hd with ⟨U, V, Uo, Vo, SU, TV, UV⟩
  /- For each point `(x, -x) ∈ T`, choose a neighborhood
    `Ico x (x + k⁻¹) ×ˢ Ico (-x) (-x + k⁻¹) ⊆ V`. -/
  have : ∀ x : ℝₗ, Irrational x.toReal → ∃ k : ℕ+, Ico x (x + k⁻¹) ×ˢ Ico (-x) (-x + k⁻¹) ⊆ V :=
    by
    intro x hx
    have hV : V ∈ 𝓝 (x, -x) := Vo.mem_nhds (@TV (x, -x) ⟨add_neg_self x, hx⟩)
    exact (nhds_prod_antitone_basis_inv_pnat _ _).mem_iff.1 hV
  choose! k hkV
  /- Since the set of irrational numbers is a dense Gδ set in the usual topology of `ℝ`, there
    exists `N > 0` such that the set `C N = {x : ℝ | irrational x ∧ k x = N}` is dense in a nonempty
    interval. In other words, the closure of this set has a nonempty interior. -/
  set C : ℕ+ → Set ℝ := fun n => closure {x | Irrational x ∧ k (to_real.symm x) = n}
  have H : {x : ℝ | Irrational x} ⊆ ⋃ n, C n := fun x hx =>
    mem_Union.2 ⟨_, subset_closure ⟨hx, rfl⟩⟩
  have Hd : Dense (⋃ n, interior (C n)) :=
    is_Gδ_irrational.dense_Union_interior_of_closed dense_irrational (fun _ => isClosed_closure) H
  obtain ⟨N, hN⟩ : ∃ n : ℕ+, (interior <| C n).Nonempty; exact nonempty_Union.mp Hd.nonempty
  /- Choose a rational number `r` in the interior of the closure of `C N`, then choose `n ≥ N > 0`
    such that `Ico r (r + n⁻¹) × Ico (-r) (-r + n⁻¹) ⊆ U`. -/
  rcases rat.dense_range_cast.exists_mem_open isOpen_interior hN with ⟨r, hr⟩
  have hrU : ((r, -r) : ℝₗ × ℝₗ) ∈ U := @SU (r, -r) ⟨add_neg_self _, r, rfl⟩
  obtain ⟨n, hnN, hn⟩ :
    ∃ (n : _) (hnN : N ≤ n), Ico (r : ℝₗ) (r + n⁻¹) ×ˢ Ico (-r : ℝₗ) (-r + n⁻¹) ⊆ U
  exact ((nhds_prod_antitone_basis_inv_pnat _ _).hasBasis_ge N).mem_iff.1 (Uo.mem_nhds hrU)
  /- Finally, choose `x ∈ Ioo (r : ℝ) (r + n⁻¹) ∩ C N`. Then `(x, -r)` belongs both to `U` and `V`,
    so they are not disjoint. This contradiction completes the proof. -/
  obtain ⟨x, hxn, hx_irr, rfl⟩ :
    ∃ x : ℝ, x ∈ Ioo (r : ℝ) (r + n⁻¹) ∧ Irrational x ∧ k (to_real.symm x) = N :=
    by
    have : (r : ℝ) ∈ closure (Ioo (r : ℝ) (r + n⁻¹)) := by rw [closure_Ioo h₀'.ne, left_mem_Icc];
      exact h₀'.le
    rcases mem_closure_iff_nhds.1 this _ (mem_interior_iff_mem_nhds.1 hr) with ⟨x', hx', hx'ε⟩
    exact mem_closure_iff.1 hx' _ isOpen_Ioo hx'ε
  refine' UV.le_bot (_ : (to_real.symm x, -↑r) ∈ _)
  refine' ⟨hn ⟨_, _⟩, hkV (to_real.symm x) hx_irr ⟨_, _⟩⟩
  · exact Ioo_subset_Ico_self hxn
  · exact left_mem_Ico.2 h₀'
  · exact left_mem_Ico.2 h₀'
  · refine' (nhds_antitone_basis_Ico_inv_pnat (-x)).2 hnN ⟨neg_le_neg hxn.1.le, _⟩
    simp only [add_neg_lt_iff_le_add', lt_neg_add_iff_add_lt]
    exact hxn.2
#align counterexample.sorgenfrey_line.not_normal_space_prod Counterexample.SorgenfreyLine.not_normalSpace_prod

/-- Topology on the Sorgenfrey line is not metrizable. -/
theorem not_metrizableSpace : ¬MetrizableSpace ℝₗ :=
  by
  intro
  letI := metrizable_space_metric ℝₗ
  exact not_normal_space_prod inferInstance
#align counterexample.sorgenfrey_line.not_metrizable_space Counterexample.SorgenfreyLine.not_metrizableSpace

/-- Topology on the Sorgenfrey line is not second countable. -/
theorem not_secondCountableTopology : ¬SecondCountableTopology ℝₗ := by intro;
  exact not_metrizable_space (metrizable_space_of_t3_second_countable _)
#align counterexample.sorgenfrey_line.not_second_countable_topology Counterexample.SorgenfreyLine.not_secondCountableTopology

end SorgenfreyLine

end Counterexample

