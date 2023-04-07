import Mathlib.Data.Finset.NoncommProd.Basic
import Mathlib.Algebra.Group.Commute.Submonoid
import Mathlib.Algebra.Group.Commute.Subgroup
import Mathlib.Algebra.Group.Commute.Subsemiring
import Mathlib.Algebra.Group.Commute.Subring

namespace Multiset

variable {α: Type _ }

@[to_additive]
theorem noncommProd_eq_prod_submonoid_commClosure [Monoid α] (s : Multiset α)
  (comm : {x | x ∈ s}.Pairwise Commute) :
    noncommProd s comm =
      (s.pmap (fun a (ha : a ∈ Submonoid.commClosure {x | x ∈ s} comm) =>
        (⟨a, ha⟩ : Submonoid.commClosure {x | x ∈ s} comm))
        Submonoid.subset_closure).prod :=
  calc noncommProd s comm =
      noncommProd ((s.pmap (fun a (ha : a ∈ Submonoid.commClosure {x | x ∈ s} comm) =>
        (⟨a, ha⟩ : Submonoid.commClosure {x | x ∈ s} comm))
          Submonoid.subset_closure).map (Submonoid.subtype _))
        (by simp only [Function.comp, map_pmap]
            simpa using comm) :=
        by congr; simp only [map_map, map_pmap, Function.comp]; simp [pmap_eq_map]
  _ = _ := by rw [← noncommProd_map, noncommProd_eq_prod]; simp

end Multiset
