/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes

! This file was ported from Lean 3 source module group_theory.abelianization
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.Finiteness

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `Algebra/Category/Group/Adjunctions`.

## Main definitions

* `commutator`: defines the commutator of a group `G` as a subgroup of `G`.
* `Abelianization`: defines the abelianization of a group `G` as the quotient of a group by its
  commutator subgroup.
* `Abelianization.map`: lifts a group homomorphism to a homomorphism between the abelianizations
* `MulEquiv.abelianizationCongr`: Equivalent groups have equivalent abelianizations

-/


universe u v w

-- Let G be a group.
variable (G : Type u) [Group G]

/-- The commutator subgroup of a group G is the normal subgroup
  generated by the commutators [p,q]=`p*q*p⁻¹*q⁻¹`. -/
def commutator : Subgroup G := ⁅(⊤ : Subgroup G), ⊤⁆
#align commutator commutator

-- Porting note: this instance should come from `deriving Subgroup.Normal`
instance : Subgroup.Normal (commutator G) := Subgroup.commutator_normal ⊤ ⊤

theorem commutator_def : commutator G = ⁅(⊤ : Subgroup G), ⊤⁆ :=
  rfl
#align commutator_def commutator_def

theorem commutator_eq_closure : commutator G = Subgroup.closure (commutatorSet G) := by
  simp [commutator, Subgroup.commutator_def, commutatorSet]
#align commutator_eq_closure commutator_eq_closure

theorem commutator_eq_normalClosure : commutator G = Subgroup.normalClosure (commutatorSet G) := by
  simp [commutator, Subgroup.commutator_def', commutatorSet]
#align commutator_eq_normal_closure commutator_eq_normalClosure

instance commutator_characteristic : (commutator G).Characteristic :=
  Subgroup.commutator_characteristic ⊤ ⊤
#align commutator_characteristic commutator_characteristic

instance [Finite (commutatorSet G)] : Group.FG (commutator G) := by
  rw [commutator_eq_closure]
  apply Group.closure_finite_fg

theorem rank_commutator_le_card [Finite (commutatorSet G)] :
    Group.rank (commutator G) ≤ Nat.card (commutatorSet G) := by
  rw [Subgroup.rank_congr (commutator_eq_closure G)]
  apply Subgroup.rank_closure_finite_le_nat_card
#align rank_commutator_le_card rank_commutator_le_card

theorem commutator_centralizer_commutator_le_center :
    ⁅(commutator G).centralizer, (commutator G).centralizer⁆ ≤ Subgroup.center G := by
  rw [← Subgroup.centralizer_top, ← Subgroup.commutator_eq_bot_iff_le_centralizer]
  suffices ⁅⁅⊤, (commutator G).centralizer⁆, (commutator G).centralizer⁆ = ⊥ by
    refine' Subgroup.commutator_commutator_eq_bot_of_rotate _ this
    rwa [Subgroup.commutator_comm (commutator G).centralizer]
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Set.centralizer_subset (Subgroup.commutator_mono le_top le_top)
#align commutator_centralizer_commutator_le_center commutator_centralizer_commutator_le_center

/-- The abelianization of G is the quotient of G by its commutator subgroup. -/
def Abelianization : Type u :=
  G ⧸ commutator G
#align abelianization Abelianization

namespace Abelianization

attribute [local instance] QuotientGroup.leftRel

instance commGroup : CommGroup (Abelianization G) :=
  { QuotientGroup.Quotient.group _ with
    mul_comm := fun x y =>
      Quotient.inductionOn₂' x y fun a b =>
        Quotient.sound' <|
          QuotientGroup.leftRel_apply.mpr <|
            Subgroup.subset_closure
              ⟨b⁻¹, Subgroup.mem_top b⁻¹, a⁻¹, Subgroup.mem_top a⁻¹, by group⟩ }

instance : Inhabited (Abelianization G) :=
  ⟨1⟩

instance [Fintype G] [DecidablePred (· ∈ commutator G)] : Fintype (Abelianization G) :=
  QuotientGroup.fintype (commutator G)

instance [Finite G] : Finite (Abelianization G) :=
  Quotient.finite _

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
def of : G →* Abelianization G where
  toFun := QuotientGroup.mk
  map_one' := rfl
  map_mul' _ _ := rfl
#align abelianization.of Abelianization.of

@[simp]
theorem mk_eq_of (a : G) : Quot.mk _ a = of a :=
  rfl
#align abelianization.mk_eq_of Abelianization.mk_eq_of

section lift

-- So far we have built Gᵃᵇ and proved it's an abelian group.
-- Furthermore we defined the canonical projection `of : G → Gᵃᵇ`
-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
variable {A : Type v} [CommGroup A] (f : G →* A)

theorem commutator_subset_ker : commutator G ≤ f.ker := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro x ⟨p, q, rfl⟩
  simp [MonoidHom.mem_ker, mul_right_comm (f p) (f q), commutatorElement_def]
#align abelianization.commutator_subset_ker Abelianization.commutator_subset_ker

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map
  from the abelianization of a `G` to `A` that factors through `f`. -/
def lift : (G →* A) ≃ (Abelianization G →* A) where
  toFun f := QuotientGroup.lift _ f fun _ h => f.mem_ker.2 <| commutator_subset_ker _ h
  invFun F := F.comp of
  left_inv _ := MonoidHom.ext fun _ => rfl
  right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl
#align abelianization.lift Abelianization.lift

@[simp]
theorem lift.of (x : G) : lift f (of x) = f x :=
  rfl
#align abelianization.lift.of Abelianization.lift.of

theorem lift.unique (φ : Abelianization G →* A)
    -- hφ : φ agrees with f on the image of G in Gᵃᵇ
    (hφ : ∀ x : G, φ (Abelianization.of x) = f x)
    {x : Abelianization G} : φ x = lift f x :=
  QuotientGroup.induction_on x hφ
#align abelianization.lift.unique Abelianization.lift.unique

@[simp]
theorem lift_of : lift of = MonoidHom.id (Abelianization G) :=
  lift.apply_symm_apply <| MonoidHom.id _
#align abelianization.lift_of Abelianization.lift_of

end lift

variable {A : Type v} [Monoid A]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext (φ ψ : Abelianization G →* A) (h : φ.comp of = ψ.comp of) : φ = ψ :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x <| FunLike.congr_fun h
#align abelianization.hom_ext Abelianization.hom_ext

section Map

variable {H : Type v} [Group H] (f : G →* H)

/-- The map operation of the `Abelianization` functor -/
def map : Abelianization G →* Abelianization H :=
  lift (of.comp f)
#align abelianization.map Abelianization.map

@[simp]
theorem map_of (x : G) : map f (of x) = of (f x) :=
  rfl
#align abelianization.map_of Abelianization.map_of

@[simp]
theorem map_id : map (MonoidHom.id G) = MonoidHom.id (Abelianization G) :=
  hom_ext _ _ rfl
#align abelianization.map_id Abelianization.map_id

@[simp]
theorem map_comp {I : Type w} [Group I] (g : H →* I) : (map g).comp (map f) = map (g.comp f) :=
  hom_ext _ _ rfl
#align abelianization.map_comp Abelianization.map_comp

@[simp]
theorem map_map_apply {I : Type w} [Group I] {g : H →* I} {x : Abelianization G} :
    map g (map f x) = map (g.comp f) x :=
  FunLike.congr_fun (map_comp _ _) x
#align abelianization.map_map_apply Abelianization.map_map_apply

end Map

end Abelianization

section AbelianizationCongr

-- Porting note: `[Group G]` should not be necessary here
variable {G} [Group G] {H : Type v} [Group H] (e : G ≃* H)

/-- Equivalent groups have equivalent abelianizations -/
def MulEquiv.abelianizationCongr : Abelianization G ≃* Abelianization H where
  toFun := Abelianization.map e.toMonoidHom
  invFun := Abelianization.map e.symm.toMonoidHom
  left_inv := by
    rintro ⟨a⟩
    simp
  right_inv := by
    rintro ⟨a⟩
    simp
  map_mul' := MonoidHom.map_mul _
#align mul_equiv.abelianization_congr MulEquiv.abelianizationCongr

@[simp]
theorem abelianizationCongr_of (x : G) :
    e.abelianizationCongr (Abelianization.of x) = Abelianization.of (e x) :=
  rfl
#align abelianization_congr_of abelianizationCongr_of

@[simp]
theorem abelianizationCongr_refl :
    (MulEquiv.refl G).abelianizationCongr = MulEquiv.refl (Abelianization G) :=
  MulEquiv.toMonoidHom_injective Abelianization.lift_of
#align abelianization_congr_refl abelianizationCongr_refl

@[simp]
theorem abelianizationCongr_symm : e.abelianizationCongr.symm = e.symm.abelianizationCongr :=
  rfl
#align abelianization_congr_symm abelianizationCongr_symm

@[simp]
theorem abelianizationCongr_trans {I : Type v} [Group I] (e₂ : H ≃* I) :
    e.abelianizationCongr.trans e₂.abelianizationCongr = (e.trans e₂).abelianizationCongr :=
  MulEquiv.toMonoidHom_injective (Abelianization.hom_ext _ _ rfl)
#align abelianization_congr_trans abelianizationCongr_trans

end AbelianizationCongr

/-- An Abelian group is equivalent to its own abelianization. -/
@[simps]
def Abelianization.equivOfComm {H : Type _} [CommGroup H] : H ≃* Abelianization H :=
  { Abelianization.of with
    toFun := Abelianization.of
    invFun := Abelianization.lift (MonoidHom.id H)
    left_inv := fun a => rfl
    right_inv := by
      rintro ⟨a⟩
      rfl }
#align abelianization.equiv_of_comm Abelianization.equivOfComm

section commutatorRepresentatives

open Subgroup

/-- Representatives `(g₁, g₂) : G × G` of commutators `⁅g₁, g₂⁆ ∈ G`. -/
def commutatorRepresentatives : Set (G × G) :=
  Set.range fun g : commutatorSet G => (g.2.choose, g.2.choose_spec.choose)
#align commutator_representatives commutatorRepresentatives

instance [Finite (commutatorSet G)] : Finite (commutatorRepresentatives G) :=
  Set.finite_coe_iff.mpr (Set.finite_range _)

/-- Subgroup generated by representatives `g₁ g₂ : G` of commutators `⁅g₁, g₂⁆ ∈ G`. -/
def closureCommutatorRepresentatives : Subgroup G :=
  closure (Prod.fst '' commutatorRepresentatives G ∪ Prod.snd '' commutatorRepresentatives G)
#align closure_commutator_representatives closureCommutatorRepresentatives

instance closureCommutatorRepresentatives_fg [Finite (commutatorSet G)] :
    Group.FG (closureCommutatorRepresentatives G) :=
  Group.closure_finite_fg _
#align closure_commutator_representatives_fg closureCommutatorRepresentatives_fg

theorem rank_closureCommutatorRepresentatives_le [Finite (commutatorSet G)] :
    Group.rank (closureCommutatorRepresentatives G) ≤ 2 * Nat.card (commutatorSet G) := by
  rw [two_mul]
  exact
    (Subgroup.rank_closure_finite_le_nat_card _).trans
      ((Set.card_union_le _ _).trans
        (add_le_add ((Finite.card_image_le _).trans (Finite.card_range_le _))
          ((Finite.card_image_le _).trans (Finite.card_range_le _))))
#align rank_closure_commutator_representations_le rank_closureCommutatorRepresentatives_le

theorem image_commutatorSet_closureCommutatorRepresentatives :
    (closureCommutatorRepresentatives G).subtype ''
        commutatorSet (closureCommutatorRepresentatives G) =
      commutatorSet G := by
  apply Set.Subset.antisymm
  · rintro - ⟨-, ⟨g₁, g₂, rfl⟩, rfl⟩
    exact ⟨g₁, g₂, rfl⟩
  · exact fun g hg =>
      ⟨_,
        ⟨⟨_, subset_closure (Or.inl ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩)⟩,
          ⟨_, subset_closure (Or.inr ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩)⟩, rfl⟩,
        hg.choose_spec.choose_spec⟩
#align image_commutator_set_closure_commutator_representatives image_commutatorSet_closureCommutatorRepresentatives

theorem card_commutatorSet_closureCommutatorRepresentatives :
    Nat.card (commutatorSet (closureCommutatorRepresentatives G)) = Nat.card (commutatorSet G) := by
  rw [← image_commutatorSet_closureCommutatorRepresentatives G]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))
#align card_commutator_set_closure_commutator_representatives card_commutatorSet_closureCommutatorRepresentatives

theorem card_commutator_closureCommutatorRepresentatives :
    Nat.card (commutator (closureCommutatorRepresentatives G)) = Nat.card (commutator G) := by
  rw [commutator_eq_closure G, ← image_commutatorSet_closureCommutatorRepresentatives, ←
    MonoidHom.map_closure, ← commutator_eq_closure]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))
#align card_commutator_closure_commutator_representatives card_commutator_closureCommutatorRepresentatives

instance [Finite (commutatorSet G)] :
    Finite (commutatorSet (closureCommutatorRepresentatives G)) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_commutatorSet_closureCommutatorRepresentatives]
  exact Finite.card_pos.ne'

end commutatorRepresentatives
