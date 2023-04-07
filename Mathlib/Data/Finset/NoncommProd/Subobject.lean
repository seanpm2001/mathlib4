import Mathlib.Data.Finset.NoncommProd.Basic
import Mathlib.Algebra.Group.Commute.Submonoid
import Mathlib.Algebra.Group.Commute.Subgroup
import Mathlib.Algebra.Group.Commute.Subsemiring
import Mathlib.Algebra.Group.Commute.Subring

variable {α β : Type _ }
namespace Multiset

@[to_additive]
theorem noncommProd_eq_prod_pmap [Monoid α] [CommMonoid β] (s : Multiset α)
    (f : β →* α) (comm : {x | x ∈ s}.Pairwise Commute)
    {p : α → Prop} (inv : ∀ a, p a → β) (p_imp : ∀ a, a ∈ s → p a)
    (f_inv : ∀ a (h : p a), f (inv a h) = a) :
    noncommProd s comm = f (s.pmap inv p_imp).prod :=
 calc noncommProd s comm = noncommProd ((s.pmap inv p_imp).map f)
        (by simp only [Function.comp, map_pmap, f_inv]
            simpa using comm) :=
        by congr; simp only [map_map, map_pmap, Function.comp, f_inv]; simp [pmap_eq_map]
  _ = _ := by rw [← noncommProd_map, noncommProd_eq_prod]

@[to_additive]
theorem noncommProd_eq_prod_submonoid_commClosure [Monoid α] (s : Multiset α)
    (comm : {x | x ∈ s}.Pairwise Commute) :
    noncommProd s comm =
      (s.pmap (fun a (ha : a ∈ Submonoid.commClosure {x | x ∈ s} comm) =>
        (⟨a, ha⟩ : Submonoid.commClosure {x | x ∈ s} comm))
        Submonoid.subset_closure).prod :=
  noncommProd_eq_prod_pmap s
    (Submonoid.subtype (Submonoid.commClosure {x | x ∈ s} comm))
    (p := fun a => a ∈ Submonoid.commClosure {x | x ∈ s} comm)
    comm _ _ (by simp)

@[to_additive]
theorem noncommProd_eq_prod_subgroup_commClosure [Group α] (s : Multiset α)
    (comm : {x | x ∈ s}.Pairwise Commute) :
    noncommProd s comm =
      (s.pmap (fun a (ha : a ∈ Subgroup.commClosure {x | x ∈ s} comm) =>
        (⟨a, ha⟩ : Subgroup.commClosure {x | x ∈ s} comm))
        Subgroup.subset_closure).prod :=
  noncommProd_eq_prod_pmap s
    (Subgroup.subtype (Subgroup.commClosure {x | x ∈ s} comm))
    (p := fun a => a ∈ Subgroup.commClosure {x | x ∈ s} comm)
    comm _ _ (by simp)

theorem noncommProd_eq_prod_subsemiring_commClosure [Semiring α] (s : Multiset α)
    (comm : {x | x ∈ s}.Pairwise Commute) :
    noncommProd s comm =
      (s.pmap (fun a (ha : a ∈ Subsemiring.commClosure {x | x ∈ s} comm) =>
        (⟨a, ha⟩ : Subsemiring.commClosure {x | x ∈ s} comm))
        Subsemiring.subset_closure).prod :=
  noncommProd_eq_prod_pmap s
    (Subsemiring.subtype (Subsemiring.commClosure {x | x ∈ s} comm)).toMonoidHom
    (p := fun a => a ∈ Subsemiring.commClosure {x | x ∈ s} comm)
    comm _ _ (by simp)

theorem noncommProd_eq_prod_subring_commClosure [Ring α] (s : Multiset α)
    (comm : {x | x ∈ s}.Pairwise Commute) :
    noncommProd s comm =
      (s.pmap (fun a (ha : a ∈ Subring.commClosure {x | x ∈ s} comm) =>
        (⟨a, ha⟩ : Subring.commClosure {x | x ∈ s} comm))
        Subring.subset_closure).prod :=
  noncommProd_eq_prod_pmap s
    (Subring.subtype (Subring.commClosure {x | x ∈ s} comm)).toMonoidHom
    (p := fun a => a ∈ Subring.commClosure {x | x ∈ s} comm)
    comm _ _ (by simp)

end Multiset

namespace Finset

variable {ι : Type _}

set_option synthInstance.etaExperiment true
@[to_additive]
theorem noncommProd_eq_prod_attach [Monoid α] [CommMonoid β] (s : Finset ι)
    (x : ι → α) (f : β →* α) (comm : {x | x ∈ s}.Pairwise (fun a b => Commute (x a) (x b)))
    (inv : {i // i ∈ s } → β)
    (f_inv : ∀ i, f (inv i) = x i) :
    noncommProd s x comm = f (s.attach.prod inv) := by
  rw [← noncommProd_eq_prod, noncommProd_map]

theorem noncommProd_eq_prod_subgroup_commClosure

end Finset
