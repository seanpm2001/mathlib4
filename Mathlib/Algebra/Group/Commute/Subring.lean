import Mathlib.Algebra.Group.Commute.Submonoid
import Mathlib.RingTheory.Subring.Basic
import Mathlib.Data.Set.Pairwise.Basic

namespace Subring

variable {R : Type _} [Ring R]

/-- `commClosure s hs` is just the `closure` of `s`. It takes a proof of
`s.Pairwise Commute` explicitly, so that we can put a `CommMonoid` instance on
`commClosure s hs` -/
@[nolint unusedArguments]
def commClosure (s : Set R) (_hs : s.Pairwise Commute) : Subring R :=
  closure s

theorem commClosure_eq_closure (s : Set R) (hs : s.Pairwise Commute) :
    commClosure s hs = closure s :=
  rfl

theorem commute_of_mem_closure {s : Set R} (hs : s.Pairwise Commute)
    {x y : R} (hx : x ∈ closure s) (hy : y ∈ closure s) : Commute x y :=
  closure_induction₂ hx hy
    (fun x hx y hy => show Commute x y by
      classical by_cases hxy : x = y
      . subst hxy; exact Commute.refl _
      . exact hs hx hy hxy)
    Commute.zero_left
    Commute.zero_right
    Commute.one_left
    Commute.one_right
    (fun _ _ => Commute.neg_left)
    (fun _ _ => Commute.neg_right)
    (fun _ _ _ => Commute.add_left)
    (fun _ _ _ => Commute.add_right)
    (fun _ _ _ => Commute.mul_left)
    (fun _ _ _ => Commute.mul_right)

instance commClosure.commRing
    (s : Set R) (hs : s.Pairwise Commute) : CommSemiring (commClosure s hs) :=
  { inferInstanceAs (Ring (commClosure s hs)) with
    mul_comm := fun x y => Subtype.ext <| commute_of_mem_closure hs x.2 y.2 }

end Subring
