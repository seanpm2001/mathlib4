import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Set.Pairwise.Basic

namespace Subgroup

variable {G : Type _} [Group G]

/-- `commClosure s hs` is just the `closure` of `s`. It takes a proof of
`s.Pairwise Commute` explicitly, so that we can put a `CommGroup` instance on
`commClosure s hs` -/
@[to_additive "`commClosure s hs` is just the `closure` of `s`. It takes a proof of
`s.Pairwise AddCommute` explicitly, so that we can put an `AddCommGroup` instance on
`commClosure s hs`", nolint unusedArguments]
def commClosure (s : Set G) (_hs : s.Pairwise Commute) : Subgroup G :=
  closure s

@[to_additive]
theorem commClosure_eq_closure (s : Set G) (hs : s.Pairwise Commute) :
    commClosure s hs = closure s :=
  rfl

@[to_additive]
theorem commute_of_mem_closure {s : Set G} (hs : s.Pairwise Commute)
    {x y : G} (hx : x ∈ closure s) (hy : y ∈ closure s) : Commute x y :=
  closure_induction₂ hx hy
    (fun x hx y hy => show Commute x y by
      classical by_cases hxy : x = y
      . subst hxy; exact Commute.refl _
      . exact hs hx hy hxy)
    Commute.one_left
    Commute.one_right
    (fun _ _ _ => Commute.mul_left)
    (fun _ _ _ => Commute.mul_right)
    (fun _ _ => Commute.inv_left)
    (fun _ _ => Commute.inv_right)

@[to_additive]
instance commClosure.commGroup
    (s : Set G) (hs : s.Pairwise Commute) : CommGroup (commClosure s hs) :=
  { inferInstanceAs (Group (commClosure s hs)) with
    mul_comm := fun x y => Subtype.ext <| commute_of_mem_closure hs x.2 y.2 }

end Subgroup
