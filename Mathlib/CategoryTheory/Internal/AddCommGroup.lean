import Mathlib.CategoryTheory.Internal.Basic
import Mathlib.CategoryTheory.Internal.ObjOperation

namespace CategoryTheory

open Limits

namespace Internal

open ConcreteCategory

variable {C : Type _} [Category C]

def addCommGroup (G : Internal AddCommGroupCat C) (X : C) :
    AddCommGroup (X ⟶ G.obj) :=
{ zero := (addCommGroupCat_zero.onInternal G).app X PUnit.unit
  add := fun a b => (addCommGroupCat_add.onInternal G).app X ⟨a, b⟩
  add_zero := congr_fun (congr_app (addCommGroupCat_add_zero.onInternal G) (Opposite.op X))
  zero_add := congr_fun (congr_app (addCommGroupCat_zero_add.onInternal G) (Opposite.op X))
  add_assoc := fun a b c =>
    congr_fun (congr_app (addCommGroupCat_add_assoc.onInternal G) X) ⟨a, ⟨b, c⟩⟩
  neg := (addCommGroupCat_neg.onInternal G).app (Opposite.op X)
  add_left_neg := congr_fun (congr_app (addCommGroupCat_add_left_neg.onInternal G) (Opposite.op X))
  add_comm := fun a b =>
    congr_fun (congr_app (addCommGroupCat_add_comm.onInternal G) (Opposite.op X)) ⟨a, b⟩ }

@[simp]
def addCommGroup_addMonoidHom (G : Internal AddCommGroupCat C) {X Y : C} (f : X ⟶ Y) :
    letI := addCommGroup G X
    letI := addCommGroup G Y
    (Y ⟶ G.obj) →+ (X ⟶ G.obj) :=
  letI := addCommGroup G X
  letI := addCommGroup G Y
  AddMonoidHom.mk' (fun φ => f ≫ φ) (fun a b =>
    (congr_fun ((addCommGroupCat_add.onInternal G).naturality f) ⟨a, b⟩).symm)

@[simp]
def addCommGroup_addMonoidHom' {G₁ G₂ : Internal AddCommGroupCat C} (f : G₁ ⟶ G₂) (f_obj : G₁.obj ⟶ G₂.obj)
  (h : f_obj = (Internal.objFunctor _ _).map f) (X : C) :
    letI := addCommGroup G₁ X
    letI := addCommGroup G₂ X
    (X ⟶ G₁.obj) →+ (X ⟶ G₂.obj) :=
  letI := addCommGroup G₁ X
  letI := addCommGroup G₂ X
  AddMonoidHom.mk' (fun φ => φ ≫ f_obj)
    (fun a b => (congr_fun (congr_app
      (addCommGroupCat_add.onInternal_naturality f f_obj h) X) ⟨a, b⟩).symm)

structure AddCommGroupCatObjOperations (G : C)
    [HasTerminal C] [HasBinaryProduct G G] [HasBinaryProduct G (G ⨯ G)] :=
  zero : ObjOperation₀ G
  neg : ObjOperation₁ G
  add : ObjOperation₂ G
  add_assoc : add.assoc
  add_zero : add.add_zero zero
  zero_add : add.zero_add zero
  add_comm : add.comm
  add_left_neg : add.add_left_neg neg zero

namespace AddCommGroupCatObjOperations

variable {G : C} [HasTerminal C] [HasBinaryProduct G G] [HasBinaryProduct G (G ⨯ G)]
  (h : AddCommGroupCatObjOperations G)

noncomputable def presheaf_obj (Y : C) : AddCommGroup (Y ⟶ G) where
  zero := ((ObjOperation₀.yonedaEquiv G) h.zero).app (Opposite.op Y) PUnit.unit
  neg := ((ObjOperation₁.yonedaEquiv G) h.neg).app (Opposite.op Y)
  add a b := ((ObjOperation₂.yonedaEquiv G) h.add).app (Opposite.op Y) ⟨a, b⟩
  add_assoc a b c := congr_fun (congr_app ((ObjOperation₂.assoc_iff h.add).1 h.add_assoc) (Opposite.op Y)) ⟨a, b, c⟩
  add_zero a := congr_fun (congr_app ((ObjOperation₂.add_zero_iff h.add h.zero).1 h.add_zero) (Opposite.op Y)) a
  zero_add a := congr_fun (congr_app ((ObjOperation₂.zero_add_iff h.add h.zero).1 h.zero_add) (Opposite.op Y)) a
  add_left_neg a := congr_fun (congr_app ((ObjOperation₂.add_left_neg_iff h.add h.neg h.zero).1 h.add_left_neg) (Opposite.op Y)) a
  add_comm a b := congr_fun (congr_app ((ObjOperation₂.comm_iff h.add).1 h.add_comm) (Opposite.op Y)) ⟨a, b⟩

@[simp]
noncomputable def presheaf_map {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    letI := h.presheaf_obj Y₁
    letI := h.presheaf_obj Y₂
    AddCommGroupCat.of (Y₂ ⟶ G) ⟶ AddCommGroupCat.of (Y₁ ⟶ G) := by
  letI := h.presheaf_obj Y₁
  letI := h.presheaf_obj Y₂
  refine' AddCommGroupCat.ofHom (AddMonoidHom.mk' (fun g => f ≫ g)
    (fun a b => (congr_fun (((ObjOperation₂.yonedaEquiv G) h.add).naturality f.op) ⟨a, b⟩).symm))

noncomputable def presheaf : Cᵒᵖ ⥤ AddCommGroupCat := by
  letI := fun (Y : C) => h.presheaf_obj Y
  exact
  { obj := fun Y => AddCommGroupCat.of (Y.unop ⟶ G)
    map := fun f => h.presheaf_map f.unop }

noncomputable def internal :
  Internal AddCommGroupCat C where
  obj := G
  presheaf := h.presheaf
  iso := Iso.refl _

end AddCommGroupCatObjOperations

end Internal

end CategoryTheory
