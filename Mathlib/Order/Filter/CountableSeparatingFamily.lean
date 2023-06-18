/-
Copyright (c) 2023 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Filter.CountableInter

/-!
# Filters with countable intersections and countable separating families

In this file we prove some facts about a filter with countable intersections property on a type with
a countable family of sets that separates points of the space. The main use case is the
`MeasureTheory.Measure.ae` filter and a space with countably generated σ-algebra but lemmas apply,
e.g., to the `residual` filter and a T₀ topological space with second countable topology.

To avoid repetition of lemmas for different families of separating sets (measurable sets, open sets,
closed sets), all theorems in this file take a predicate `p : Set α → Prop` as an argument and prove
existence of a countable separating family satisfying this predicate by searching for a
`HasCountableSeparatingOn` typeclass instance.

## Main definitions

- `HasCountableSeparatingOn α p t`: a typeclass saying that there exists a countable set family
  `S : Set (Set α)` such that all `s ∈ S` satisfy the predicate `p` and any two distinct points
  `x y ∈ t`, `x ≠ y`, can be separated by a set `s ∈ S`.

This typeclass is used in all lemmas in this file to avoid repeating them for open sets, closed
sets, and measurable sets.

### Main results

#### Filters supported on a (sub)singleton

Let `l : Filter α` be a filter with countable intersections property. Let `p : Set α → Prop` be a
property such that there exists a countable family of sets satisfying `p` and separating points of
`α`. Then there `l` is supported on a subsingleton: there exists a subsingleton `t` such that
`t ∈ l`.

We formalize various versions of this theorem in
`Filter.exists_subset_subsingleton_mem_of_forall_separating`,
`Filter.exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating`,
`Filter.exists_singleton_mem_of_mem_of_forall_separating`,
`Filter.exists_subsingleton_mem_of_forall_separating`, and
`Filter.exists_singleton_mem_of_forall_separating`.

#### Eventually constant functions

Consider a function `f : α → β`, a filter `l` with countable intersections property, and a countable
separating family of sets of `β̀`. Suppose that for every `U` from the family, either
`∀ᶠ x in l, f x ∈ U` or `∀ᶠ x in l, f x ∉ U`. Then `f`` is eventually constant along `l`.

We formalize three versions of this theorem in
`Filter.exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating`,
`Filter.exists_eventuallyEq_const_of_eventually_mem_of_forall_separating`, and
`Filer.exists_eventuallyEq_const_of_forall_separating`.

#### Eventually equal functions

Two functions are equal along a filter with countable intersections property if the preimages of all
sets from a countable separating family of sets are equal along the filter.

We formalize several versions of this theorem in
`Filter.of_eventually_mem_of_forall_separating_mem_iff`, `Filter.of_forall_separating_mem_iff`,
`Filter.of_eventually_mem_of_forall_separating_preimage`, and
`Filter.of_forall_separating_preimage`.

## Keywords

filter, countable
-/

open Function Set Filter

/-- We say that a type `α` has a *countable separating family of sets* satisfying a predicate
`p : Set α → Prop` on a set `t` if there exists a countable family of sets `S : Set (Set α)` such
that all sets `s ∈ S` satisfy `p` and any two distinct points `x y ∈ t`, `x ≠ y`, can be separated
by `s ∈ S`.

E.g., if `α` is a `T₀` topological space with second countable topology, then it has a countable
separating family of open sets and a separating family of closed sets.
-/
class HasCountableSeparatingOn (α : Type _) (p : Set α → Prop) (t : Set α) : Prop where
  exists_countable_separating : ∃ S : Set (Set α), S.Countable ∧ (∀ s ∈ S, p s) ∧
    t.Pairwise fun x y ↦ ∃ s ∈ S, Xor' (x ∈ s) (y ∈ s)

namespace Filter

variable {l : Filter α} [CountableInterFilter l] {f g : α → β}

/-!
### Filters supported on a (sub)singleton

In this section we prove several versions of the following theorem. Let `l : Filter α` be a filter
with countable intersections property. Let `p : Set α → Prop` be a property such that there exists a
countable family of sets satisfying `p` and separating points of `α`. Then there `l` is supported on
a subsingleton: there exists a subsingleton `t` such that `t ∈ l`.

With extra `Nonempty`/`Set.Nonempty` assumptions one can assume that `t` is a singleton `{x}`. If
`s ∈ l`, then it suffices to assume that the countable family separates only points of `s`.
-/

theorem exists_subset_subsingleton_mem_of_forall_separating (p : Set α → Prop)
    {s : Set α} [h : HasCountableSeparatingOn α p s] (hs : s ∈ l)
    (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) : ∃ t, t ⊆ s ∧ t.Subsingleton ∧ t ∈ l := by
  rcases h.1 with ⟨S, hSc, hSp, hS⟩
  refine ⟨s ∩ ⋂₀ (S ∩ l.sets) ∩ ⋂ (U ∈ S) (_ : Uᶜ ∈ l), Uᶜ, ?_, ?_, ?_⟩
  · exact fun _ h ↦ h.1.1
  · intro x hx y hy
    simp only [mem_sInter, mem_inter_iff, mem_iInter, mem_compl_iff] at hx hy
    by_contra hne
    rcases hS hx.1.1 hy.1.1 hne with ⟨s, hsS, hs⟩
    cases hl s (hSp s hsS) with
    | inl hsl => simp only [hx.1.2 s ⟨hsS, hsl⟩, hy.1.2 s ⟨hsS, hsl⟩] at hs
    | inr hsl => simp only [hx.2 s hsS hsl, hy.2 s hsS hsl] at hs
  · exact inter_mem
      (inter_mem hs ((countable_sInter_mem (hSc.mono (inter_subset_left _ _))).2 fun _ h ↦ h.2))
      ((countable_bInter_mem hSc).2 fun U hU ↦ iInter_mem.2 id)

theorem exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating (p : Set α → Prop)
    {s : Set α} [HasCountableSeparatingOn α p s] (hs : s ∈ l) (hne : s.Nonempty)
    (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) : ∃ a ∈ s, {a} ∈ l := by
  rcases exists_subset_subsingleton_mem_of_forall_separating p hs hl with ⟨t, hts, ht, htl⟩
  rcases ht.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact hne.imp fun a ha ↦ ⟨ha, mem_of_superset htl (empty_subset _)⟩
  · exact ⟨x, hts rfl, htl⟩

theorem exists_singleton_mem_of_mem_of_forall_separating [Nonempty α] (p : Set α → Prop)
    {s : Set α} [HasCountableSeparatingOn α p s] (hs : s ∈ l) (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ a, {a} ∈ l := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ‹Nonempty α›.elim fun a ↦ ⟨a, mem_of_superset hs (empty_subset _)⟩
  · exact (exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p hs hne hl).imp fun _ ↦
      And.right

theorem exists_subsingleton_mem_of_forall_separating (p : Set α → Prop)
    [HasCountableSeparatingOn α p univ] (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ s : Set α, s.Subsingleton ∧ s ∈ l :=
  let ⟨t, _, hts, htl⟩ := exists_subset_subsingleton_mem_of_forall_separating p univ_mem hl
  ⟨t, hts, htl⟩

theorem exists_singleton_mem_of_forall_separating [Nonempty α] (p : Set α → Prop)
    [HasCountableSeparatingOn α p univ] (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ x : α, {x} ∈ l :=
  exists_singleton_mem_of_mem_of_forall_separating p univ_mem hl

/-!
### Eventually constant functions

In this section we apply theorems from the previous section to the filter `Filter.map f l` to show
that `f : α → β`` is eventually constant along `l` if for every `U` from the separating family,
either `∀ᶠ x in l, f x ∈ U` or `∀ᶠ x in l, f x ∉ U`.
-/

theorem exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating (p : Set β → Prop)
    {s : Set β} [HasCountableSeparatingOn β p s] (hs : ∀ᶠ x in l, f x ∈ s) (hne : s.Nonempty)
    (h : ∀ U, p U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a ∈ s, f =ᶠ[l] const α a :=
  exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p (l := map f l) hs hne h

theorem exists_eventuallyEq_const_of_eventually_mem_of_forall_separating [Nonempty β]
    (p : Set β → Prop) {s : Set β} [HasCountableSeparatingOn β p s] (hs : ∀ᶠ x in l, f x ∈ s)
    (h : ∀ U, p U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_mem_of_forall_separating (l := map f l) p hs h

theorem exists_eventuallyEq_const_of_forall_separating [Nonempty β] (p : Set β → Prop)
    [HasCountableSeparatingOn β p univ]
    (h : ∀ U, p U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_forall_separating (l := map f l) p h

namespace EventuallyEq

/-!
### Eventually equal functions

In this section we show that two functions are equal along a filter with countable intersections
property if the preimages of all sets from a countable separating family of sets are equal along
the filter.
-/

theorem of_eventually_mem_of_forall_separating_mem_iff (p : Set β → Prop) {s : Set β}
    [h' : HasCountableSeparatingOn β p s] (hf : ∀ᶠ x in l, f x ∈ s) (hg : ∀ᶠ x in l, g x ∈ s)
    (h : ∀ U : Set β, p U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U) : f =ᶠ[l] g := by
  rcases h'.1 with ⟨S, hSc, hSp, hS⟩
  have H : ∀ᶠ x in l, ∀ s ∈ S, f x ∈ s ↔ g x ∈ s :=
    (eventually_countable_ball hSc).2 fun s hs ↦ (h _ (hSp _ hs))
  filter_upwards [H, hf, hg] with x hx hxf hxg
  contrapose! hx
  rcases hS hxf hxg hx with ⟨s, hsS, h⟩
  exact ⟨s, hsS, (xor_iff_not_iff _ _).1 h⟩

theorem of_forall_separating_mem_iff (p : Set β → Prop)
    [HasCountableSeparatingOn β p univ] (h : ∀ U : Set β, p U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U) :
    f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_mem_iff p (s := univ) univ_mem univ_mem h

theorem of_eventually_mem_of_forall_separating_preimage (p : Set β → Prop) {s : Set β}
    [HasCountableSeparatingOn β p s] (hf : ∀ᶠ x in l, f x ∈ s) (hg : ∀ᶠ x in l, g x ∈ s)
    (h : ∀ U : Set β, p U → f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_mem_iff p hf hg fun U hU ↦ (h U hU).mem_iff

theorem of_forall_separating_preimage (p : Set β → Prop) [HasCountableSeparatingOn β p univ]
    (h : ∀ U : Set β, p U → f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_preimage p (s := univ) univ_mem univ_mem h
