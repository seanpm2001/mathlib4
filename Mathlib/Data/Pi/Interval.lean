/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.pi.interval
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Fintype.BigOperators

/-!
# Intervals in a pi type

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/


open Finset Fintype

open scoped BigOperators

variable {ι : Type _} {α : ι → Type _}

namespace Pi

section LocallyFinite

variable [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (α i)] [∀ i, PartialOrder (α i)]
  [∀ i, LocallyFiniteOrder (α i)]

instance : LocallyFiniteOrder (∀ i, α i) :=
  LocallyFiniteOrder.ofIcc _ (fun a b => piFinset fun i => Icc (a i) (b i)) fun a b x => by
    simp_rw [mem_piFinset, mem_Icc, le_def, forall_and]

variable (a b : ∀ i, α i)

theorem Icc_eq : Icc a b = piFinset fun i => Icc (a i) (b i) :=
  rfl
#align pi.Icc_eq Pi.Icc_eq

theorem card_Icc : (Icc a b).card = ∏ i, (Icc (a i) (b i)).card :=
  card_piFinset _
#align pi.card_Icc Pi.card_Icc

theorem card_Ico : (Ico a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
#align pi.card_Ico Pi.card_Ico

theorem card_Ioc : (Ioc a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align pi.card_Ioc Pi.card_Ioc

theorem card_Ioo : (Ioo a b).card = (∏ i, (Icc (a i) (b i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align pi.card_Ioo Pi.card_Ioo

end LocallyFinite

section Bounded

variable [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (α i)] [∀ i, PartialOrder (α i)]

section Bot

variable [∀ i, LocallyFiniteOrderBot (α i)] (b : ∀ i, α i)

instance : LocallyFiniteOrderBot (∀ i, α i) :=
  LocallyFiniteOrderTop.ofIic _ (fun b => piFinset fun i => Iic (b i)) fun b x => by
    simp_rw [mem_piFinset, mem_Iic, le_def]

theorem card_Iic : (Iic b).card = ∏ i, (Iic (b i)).card :=
  card_piFinset _
#align pi.card_Iic Pi.card_Iic

theorem card_Iio : (Iio b).card = (∏ i, (Iic (b i)).card) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
#align pi.card_Iio Pi.card_Iio

end Bot

section Top

variable [∀ i, LocallyFiniteOrderTop (α i)] (a : ∀ i, α i)

instance : LocallyFiniteOrderTop (∀ i, α i) :=
  LocallyFiniteOrderTop.ofIci _ (fun a => piFinset fun i => Ici (a i)) fun a x => by
    simp_rw [mem_piFinset, mem_Ici, le_def]

theorem card_Ici : (Ici a).card = ∏ i, (Ici (a i)).card :=
  card_piFinset _
#align pi.card_Ici Pi.card_Ici

theorem card_Ioi : (Ioi a).card = (∏ i, (Ici (a i)).card) - 1 := by
  rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]
#align pi.card_Ioi Pi.card_Ioi

end Top

end Bounded

end Pi
