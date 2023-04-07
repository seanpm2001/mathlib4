import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.GroupTheory.Submonoid.Operations
import Mathlib.Data.Set.Pairwise.Basic

namespace Submonoid

variable {M : Type _} [Monoid M]

/-- `commClosure s hs` is just the `closure` of `s`. It takes a proof of
`s.Pairwise Commute` explicitly, so that we can put a `CommMonoid` instance on
`commClosure s hs` -/
@[nolint unusedArguments]
def commClosure (s : Set M) (_hs : s.Pairwise Commute) : Submonoid M :=
  closure s

theorem commClosure_eq_closure (s : Set M) (hs : s.Pairwise Commute) :
    commClosure s hs = closure s :=
  rfl

theorem commute_of_mem_closure {s : Set M} (hs : s.Pairwise Commute)
    {x y : M} (hx : x ∈ closure s) (hy : y ∈ closure s) : Commute x y :=
  closure_induction₂ hx hy
    (fun x hx y hy => show Commute x y by
      classical by_cases hxy : x = y
      . subst hxy; exact Commute.refl _
      . exact hs hx hy hxy)
    Commute.one_left
    Commute.one_right
    (fun _ _ _ => Commute.mul_left)
    (fun _ _ _ => Commute.mul_right)

instance commClosure.commMonoid
    (s : Set M) (hs : s.Pairwise Commute) : CommMonoid (commClosure s hs) :=
  { inferInstanceAs (Monoid (commClosure s hs)) with
    mul_comm := fun x y => Subtype.ext <| commute_of_mem_closure hs x.2 y.2 }

end Submonoid
