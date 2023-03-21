import Lean
import Mathlib.Data.ListM.DepthFirst
import Mathlib.Init.ZeroOne

open Lean Elab Tactic

structure Goals where
  active : List MVarId
  suspended : List MVarId

namespace Goals

def singleton (g : MVarId) : Goals := { active := [g], suspended := [] }

def done (G : Goals) : Bool := G.active.isEmpty

def liftTactic (t : MVarId → MetaM (List MVarId)) : Goals → MetaM Goals :=
fun G => do match G.active with
| [] => failure
| g :: gs => pure { G with active := (← t g) ++ gs }

end Goals

def kleisli (m : Type v → Type v) (α : Type u) (β : Type v) :=
α → m β

namespace kleisli

def of [Pure m] (f : α → β) : kleisli m α β := fun a => pure (f a)

instance [Alternative m] : Zero (kleisli m α β) := ⟨fun _ => failure⟩
instance [Alternative m] : Add (kleisli m α β) := ⟨fun f g a => f a <|> g a⟩
instance [Monad m] : HAndThen (kleisli m α β) (kleisli m β γ) (kleisli m α γ) :=
  ⟨fun f g a => f a >>= g ()⟩

def total [Alternative m] [Monad m] (f : kleisli m α (List β)) : kleisli m α β :=
fun a => do (← f a).firstM pure

end kleisli

unsafe abbrev ndFunction (α : Type) (β : Type) := kleisli (ListM MetaM) α β
-- unsafe abbrev ndFunction (α : Type) (β : Type) := α → ListM MetaM β

namespace ndFunction

unsafe def joinList (f : ndFunction α (List β)) : ndFunction α β := fun a => do (← f a).firstM pure
unsafe def joinMetaM (f : ndFunction α (MetaM β)) : ndFunction α β := fun a => ((f a).map .monadLift).join

unsafe instance : Coe (α → β) (ndFunction α β) := ⟨fun f a => pure (f a)⟩
unsafe instance : Coe (α → MetaM β) (ndFunction α β) := ⟨fun f => joinMetaM f⟩
unsafe instance : Coe (α → MetaM (List (MetaM β))) (ndFunction α β) := ⟨fun f => joinMetaM (joinList (joinMetaM f))⟩
unsafe instance : Coe (ndFunction α (List β)) (ndFunction α β) := ⟨joinList⟩
unsafe instance : Coe (ndFunction α (MetaM β)) (ndFunction α β) := ⟨joinMetaM⟩

unsafe example (f : α → β) : ndFunction α β := f
unsafe example (f : α → List β) : ndFunction α β := f
unsafe example (f : α → MetaM β) : ndFunction α β := f
unsafe example (f : α → MetaM (List β)) : ndFunction α β := f
unsafe example (f : α → MetaM (List (MetaM β))) : ndFunction α β := f

unsafe def depthFirst (t : ndFunction α α) : ndFunction α α := ListM.depthFirst t

end ndFunction

unsafe abbrev ndTactic := ndFunction Goals Goals

unsafe def ListM.squish (L : MetaM (List (MetaM α))) : ListM MetaM α :=
.squash do pure <| .ofListM (← L)

namespace ndTactic

unsafe def of (t : MVarId → MetaM (List (MetaM (List MVarId)))) : ndTactic :=
fun G => do match G.active with
| [] => failure
| g :: gs =>
  ListM.squish (t g) |>.map fun hs => { G with active := hs ++ gs }

/--
Move the main goal to the suspended list if it satisfies the predicate,
and otherwise do nothing.
-/
unsafe def suspending (p : MVarId → MetaM Bool) : ndTactic :=
fun G => do match G.active with
| [] => failure
| g :: gs =>
  if ← p g then
    pure { G with active := gs, suspended := g :: G.suspended }
  else
    pure G

/--
Run a nondeterministic tactic:
find the first choice with no active goals, returning the suspended goals,
or fail.
-/
unsafe def run (t : ndTactic) : MVarId → MetaM (List MVarId) :=
fun g => (t (.singleton g) |>.filter Goals.done |>.head) <&> Goals.suspended

end ndTactic

def depthFirst (t : MVarId → MetaM (List (MetaM (List MVarId)))) (s : MVarId → MetaM Bool) :
    MVarId → MetaM (List MVarId) :=
unsafe fun g => ndTactic.run (ListM.depthFirst (ndTactic.suspending s >> ndTactic.of t)) g
