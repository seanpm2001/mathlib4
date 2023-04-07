import Lean
import Mathlib.Data.ListM.DepthFirst

open Lean Elab Tactic

structure Goals where
  active : List MVarId
  suspended : List MVarId := []

namespace Goals

def done (G : Goals) : Bool := G.active.isEmpty

def liftTactic (t : MVarId → MetaM (List MVarId)) : Goals → MetaM Goals :=
fun G => do match G.active with
| [] => failure
| g :: gs => pure { G with active := (← t g) ++ gs }

end Goals

unsafe def ListM.squish (L : MetaM (List (MetaM α))) : ListM MetaM α :=
  .squash do pure <| .ofListM (← L)

/-- If `L` is empty, return a default value `M`, otherwise bind a function `f` over each element. -/
unsafe def ListM.bindOrElse [Monad m] (L : ListM m α) (f : α → ListM m β) (M : ListM m β) :
    ListM m β := squash do
  match ← uncons L with
  | none => return M
  | some (x, xs) => match ← uncons (f x) with
    | none => return xs.bind f
    | some (y, ys) => return cons <| pure (some y, append ys (xs.bind f))

unsafe abbrev Nondet (σ : Type _) (m : Type _ → Type _) := StateT σ (ListM m)
/-- `NDTactic α := Goals → ListM MetaM (α × Goals)` -/
unsafe abbrev NDTactic := Nondet Goals MetaM

namespace NDTactic

unsafe def isDone : NDTactic Bool := do
  pure (← get).done

/--
Interpret a tactic which returns a list of alternative lists of new goals as an `NDTactic`,
by having it act on the first goal.
-/
unsafe def of' (t : MVarId → MetaM (List (MetaM (α × List MVarId)))) : NDTactic α :=
  fun G => do match G.active with
  | [] => failure
  | g :: gs =>
    ListM.squish (t g) |>.map fun (a, hs) => (a, { G with active := hs ++ gs })

unsafe def of (t : MVarId → MetaM (List (MetaM (List MVarId)))) : NDTactic Unit :=
  of' fun g => do
    return (← t g).map fun s => do pure ((), ← s)

/--
If `tac` succeeds (i.e. produces at least one alternative),
run `fold tac` again on those alternatives.
Otherwise, do nothing (i.e. return the input goal as the single alternative.)
Returns the whether `tac` succeeded at least once, and the final value.
-/
unsafe def fold (a : α) (tac : α → NDTactic α) : NDTactic (Bool × α) :=
  fun g => (tac a g).bindOrElse
    (fun (a', g') => (do pure (true, (← fold a' tac).2)) g')
    (pure ((false, a), g))

/--
If `tac` succeeds (i.e. produces at least one alternative),
run `fold tac` again on those alternatives.
Otherwise, do nothing (i.e. return the input goal as the single alternative.)
Returns the whether `tac` succeeded at least once.
-/
unsafe def repeat' (tac : NDTactic Unit) : NDTactic Bool := do
  return (← fold () fun _ => tac).1

/--
Move the main goal to the suspended list if it satisfies the predicate,
and otherwise fail.
-/
unsafe def suspendOrFail (p : MVarId → MetaM Bool) : NDTactic Unit :=
  fun G => do match G.active with
  | [] => failure
  | g :: gs =>
    if ← p g then
      pure ((), { G with active := gs, suspended := g :: G.suspended })
    else
      failure

unsafe def suspending (p : MVarId → MetaM Bool) : NDTactic Bool :=
  repeat' <| suspendOrFail p

/--
Takes a procedure which inspects the list of active goals and either
* fails, signalling no outcomes
* returns `none`, signalling the goals should not be changed, or
* returns `some (A, B)`, signalling the active goals should be replaced with `A` and
  `B` should be added to the suspended goals.

Returns a non-deterministic tactic,
with either 0 (in the case of failure) or 1 (otherwise) outcomes.
In the case of 1 outcome, the return value is `true` if the goals were modified.
-/
unsafe def proc' (f : List MVarId → MetaM (Option (List MVarId × List MVarId))) : NDTactic Bool :=
  fun G => do match ← f G.active with
  | none => pure (false, G)
  | some (A, B) => pure (True, { active := A, suspended := B ++ G.suspended })

/--
Repeatedly run the procedure using `proc'`.
* Gives no outcomes if the procedure eventually fails.
* Otherwise gives one outcome, and return `true` if the goals were modified at least once.
-/
unsafe def repeatingProc' (f : List MVarId → MetaM (Option (List MVarId × List MVarId))) :
    NDTactic Bool := do
  if ← proc' f then
    discard <| repeatingProc' f
    return true
  else
    return false

/--
Takes a procedure which inspects the main goal, and either
* fails, signalling no outcomes
* returns `none`, signalling it should be passed through unchanged, or
* returns `some (A, B)`, signalling it should be replaced by the subgoals `A`,
  and the goals `B` should be added to the suspended goals.

Returns true if it modified the goals.
-/
unsafe def discharge (f : MVarId → MetaM (Option (List MVarId × List MVarId))) : NDTactic Bool :=
  proc' fun gs => match gs with
    | [] => return none
    | g :: gs => do match ← f g with
      | none => return none
      | some (A, B) => return some (A ++ gs, B)

/--
Given a nondeterministic tactic `t`,
construct the nondeterministic tactic which considers every possible iteration of `t`.
-/
unsafe def depthFirst (t : NDTactic Unit) : NDTactic Unit :=
  fun g => (_root_.depthFirst fun (_, g) => t g) ((), g)

/--
Run a nondeterministic tactic:
find the first choice with no active goals, returning the suspended goals,
or fail.
-/
unsafe def run' (t : NDTactic α) : MVarId → MetaM (α × List MVarId) :=
  fun g => (t { active := [g] } |>.filter (Goals.done ·.2) |>.head) <&> fun (a, g) => (a, g.suspended)

unsafe def run (t : NDTactic Unit) (g : MVarId) : MetaM (List MVarId) := do pure (←run' t g).2

end NDTactic

open NDTactic

/--
Run a "non-deterministic" tactic `choices : MVarId → MetaM (List (MetaM (List MVarId)))`
exploring all branches until finding one with no "active" goals,
possibly modified by running a procedure
`proc : List MVarId → MetaM (Option (List MVarId × List MVarId))` at each step on the active goals,
which may:
* fail, indicating this branch should not be explored further
* return `none`, indicating that the branch should be explored as is
* return `some (A, B)`, indicating the the active goals should be replaced with `A`,
  and the goals in `B` should be added to the list of "suspended" goals, and then explored further.

If a successful branch is found (i.e. one with no active goals),
then the suspended goals from that branch are returned.
-/
def Lean.MVarId.nondeterministic
    (choices : MVarId → MetaM (List (MetaM (List MVarId))))
    (proc : List MVarId → MetaM (Option (List MVarId × List MVarId)) := fun _ => pure none) :
    MVarId → MetaM (List MVarId) := unsafe
  let t : NDTactic Unit := do
    discard <| proc' proc
    unless ← isDone do of choices
  (t.depthFirst).run
