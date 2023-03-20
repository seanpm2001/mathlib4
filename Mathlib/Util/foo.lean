import Lean
import Mathlib.Data.ListM.DepthFirst

open Lean Elab Tactic

structure Goals where
  active : List MVarId
  suspended : List MVarId

def lift (t : MVarId → MetaM (List MVarId)) : Goals → MetaM Goals :=
fun G => do match G.active with
| [] => failure
| g :: gs => pure { G with active := (← t g) ++ gs, }

unsafe def lift2 (t : MVarId → MetaM (List (MetaM (List MVarId)))) : Goals → ListM MetaM Goals := sorry

unsafe abbrev NDTactic (α β : Type _) := α → ListM MetaM β

namespace NDTactic

unsafe def fail : NDTactic α β := fun _ => ListM.nil
unsafe def or (t₁ t₂ : NDTactic α β) : NDTactic α β := fun G => (t₁ G).append (t₂ G)
unsafe def and (t₁ : NDTactic α β) (t₂ : NDTactic β γ) : NDTactic α γ := fun G => (t₁ G).bind t₂

unsafe def depthFirst (t : NDTactic α α) : NDTactic α α := ListM.depthFirst t

end NDTactic
