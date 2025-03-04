/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.filtered
! leanprover-community/mathlib commit e4ee4e30418efcb8cf304ba76ad653aeec04ba6e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Filtered
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Possession of filtered colimits
-/


universe w' w v u

noncomputable section

open CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Limits

section

variable (C)

/-- Class for having all cofiltered limits of a given size. -/
class HasCofilteredLimitsOfSize : Prop where
  /-- For all filtered types of size `w`, we have limits -/
  HasLimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsCofiltered I], HasLimitsOfShape I C
#align category_theory.limits.has_cofiltered_limits_of_size CategoryTheory.Limits.HasCofilteredLimitsOfSize

/-- Class for having all filtered colimits of a given size. -/
class HasFilteredColimitsOfSize : Prop where
  /-- For all filtered types of a size `w`, we have colimits -/
  HasColimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsFiltered I], HasColimitsOfShape I C
#align category_theory.limits.has_filtered_colimits_of_size CategoryTheory.Limits.HasFilteredColimitsOfSize

end

instance (priority := 100) hasLimitsOfShape_of_has_cofiltered_limits
    [HasCofilteredLimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsCofiltered I] :
    HasLimitsOfShape I C :=
  HasCofilteredLimitsOfSize.HasLimitsOfShape _
#align category_theory.limits.has_limits_of_shape_of_has_cofiltered_limits CategoryTheory.Limits.hasLimitsOfShape_of_has_cofiltered_limits

instance (priority := 100) hasColimitsOfShape_of_has_filtered_colimits
    [HasFilteredColimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsFiltered I] :
    HasColimitsOfShape I C :=
  HasFilteredColimitsOfSize.HasColimitsOfShape _
#align category_theory.limits.has_colimits_of_shape_of_has_filtered_colimits CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits

end CategoryTheory.Limits

