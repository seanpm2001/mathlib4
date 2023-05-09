/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
Ported by: Heather Macbeth
-/
import Mathlib.Lean.Meta
import Mathlib.Control.Basic
import Mathlib.Data.Array.MinMax
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.Relation.Rfl

/-! # Monotonicity tactic

The tactic `mono` applies monotonicity rules (collected through the library by being tagged
`@[mono]`).
-/

open Lean Elab Meta Tactic Parser Qq Mathlib.Tactic SolveByElim BacktrackOptimize

namespace Mathlib.Tactic.Monotonicity

open Attr

/-- Match each registered `mono` extension against `t`, returning an array of matching extensions.
-/
def getMatchingMonos (t : Expr) (side := Side.both) : MetaM (Array MonoExt) := do
  profileitM Exception "mono" (← getOptions) do --!! what does profileit do?
    let monos := monoExt.getState (← getEnv)
    let arr ← monos.tree.getMatch t
    -- For debugging, when needed:
    -- let showTypes : MetaM (Array Expr) := do
    --   return (← arr.map (·.name) |>.mapM getConstInfo).map (·.type)
    -- trace[Tactic.mono] "matched {← showTypes}"
    let arr := match side with
    | .both  => arr
    | .left  => arr.filter isLeft
    | .right => arr.filter isRight
    return arr

/-- Apply a mono extension to an already fully-telescoped (and in whnf) `t`. Returns any remaining
subgoals. -/
private def applyMono (t : Expr) (m : MonoExt) : MetaM (Expr × List MVarId) := do
  let (expr, goals) ← applyMatchReducing m.name t
  trace[Tactic.mono] "Applied {m.name} to {t}"
  let goals := goals.toList
  let cfg : SolveByElim.Config := { discharge := fun _ => pure none }
  let goals ← accumulateGoals goals fun g => do
    let (lemmas, ctx) ← mkAssumptionSet false false [] [] #[]
    let goals ← solveByElim cfg lemmas ctx [g]
    accumulateGoals goals (·.rfl)
  return (expr, goals)

private def applyMonos (t : Expr) (side : Side) (failIfAmbiguousMatch : Bool) :
    MetaM (Expr × List MVarId) := do
  let monos ← getMatchingMonos t side
  trace[Tactic.mono] "matched:\n{monos.map (·.name) |>.toList}"
  if monos.isEmpty then throwError "no monos apply"
  let mut results : Array (Meta.SavedState × Expr × List MVarId) := #[]
  let s ← saveState
  for m in monos do
    match ← optional (applyMono t m) with
    | some (e, []) => return (e, []) -- Finish immediately if we find one that proves `t`
    | some (e, l)  => do results := results.push (← saveState, e, l)
    | none         => pure ()
    s.restore
  trace[Tactic.mono] "got potential proof terms with the following subgoals:\n{results.map (·.2)}"
  let bestMatches := results.argmins (·.2.2.length)
  let some (s, e, l) := bestMatches[0]? | throwError "no monos apply"
  if bestMatches.size == 1 || ! failIfAmbiguousMatch then
    s.restore
    return (e, l)
  else
    let (bestMatchTypes : MessageData) ← do
      let a ← bestMatches.mapM fun (s,_,l) => do
        s.restore; l.mapM fun g => do addMessageContextFull (← g.getType)
      pure <| toMessageList (a.map toMessageData)
    throwError m!"Found multiple good matches which each produced the same number of subgoals. "
      ++ m!"Write `mono with ...` and include the types of one or more of the subgoals in one of "
      ++ m!"the following lists to encourage `mono` to use that list.\n{bestMatchTypes}"

private def applyMonosAlternatives (side : Side) (goal : MVarId) :
    MetaM (List (MetaM (List MVarId))) := withReducible do
  trace[Tactic.mono] "running applyMonosAlternatives on {goal}"
  let goal? ← dsimpGoal goal Monos.SimpContext false
  let goal ← match goal? with
  | (some goal, _) => pure goal
  | (none, _) => return []
  let (_, goal) ← goal.introsP!
  let t ← whnfR <|← instantiateMVars <|← goal.getType
  let monos ← getMatchingMonos t side
  trace[Tactic.mono] "matched:\n{monos.map (·.name) |>.toList}"
  if monos.isEmpty then throwError "no monos apply"
  return monos.toList.map fun m => goal.withContext do
    let (e, gs) ← applyMono t m; goal.assign e; pure gs

def _root_.Lean.MVarId.mono (goal : MVarId) (side : Side := .both)
    (simpUsing : Option Simp.Context := none) (recurse : Bool := false)
    (failIfAmbiguousMatch : Bool := false) :
    MetaM (List MVarId) := goal.withContext <| withReducible do
  if ! recurse then
    let goal ← match ← dsimpGoal goal Monos.SimpContext false with
  | (some goal, _) => pure goal
  | (none, _) => return []
    let goal ←
      if let some ctx := simpUsing then
        match ← simpGoal goal ctx with
        | (some (_, goal), _) => pure goal
        | (none, _) => return []
      else
        pure goal
  let (_, goal) ← goal.introsP!
  let t ← whnfR <|← instantiateMVars <|← goal.getType
  trace[Tactic.mono] "Applying monos to {t}"
    let (expr, goals) ← goal.withContext <| applyMonos t side failIfAmbiguousMatch
  goal.assign expr
  return goals
  else
    let cfg : MinimizeSubgoalsConfig :=
      if let some ctx := simpUsing then
        let simpProc (goals : List MVarId) : MetaM (Option (List MVarId)) := optional do
          let goals := (← goals.mapM
            (fun g ↦ do let (a,_) ← simpGoal g ctx; return a.map (·.2))).reduceOption
          return goals
        { proc := fun _ curr ↦ simpProc curr, trace := `Tactic.mono }
      else
        { trace := `Tactic.mono }
    let some goals ← optional <| minimizeSubgoals [goal] (applyMonosAlternatives side) cfg
      | throwError "backtracking in mono* failed"
    if ! (← goal.isAssigned) then
      throwError "mono* could not make progress on the goal"
    else
      return goals

open Parser.Tactic in
/--
`mono` needs its documentation string written.
-/
syntax (name := mono) "mono" "*"? (ppSpace mono.side)?
  (" with " (colGt term),+)? (" using " (colGt simpArg),+)? : tactic

elab_rules : tactic
| `(tactic| mono $[*%$r]? $[$s:mono.side]? $[ with%$w $a:term,*]? $[ using%$u $l,*]? ) =>
  withMainContext do
    let goal ← getMainGoal
    let side ← parseSide s
    -- Handle 'with' by asserting all hypotheses provided
    let (assertedMVarIds, goal) ←
      if let some a := a then
        let as ← a.getElems.mapM (fun a => withRef a <| Tactic.elabTermEnsuringType a q(Prop))
        trace[Tactic.mono] "asserting {as}"
        let assertedMVars ← as.mapM (fun t => mkFreshExprMVar (some t) .syntheticOpaque)
        let hs : Array Hypothesis :=
          if as.size == 1 then
            #[⟨`mono_with, as[0]!, assertedMVars[0]!⟩]
          else
            as.zipWithIndex.zipWith assertedMVars fun (a,n) mvar =>
              ⟨`mono_with |>.appendIndexAfter (n+1), a, mvar⟩
        let (_, goal) ← goal.assertHypotheses hs
        pure (assertedMVars.map (·.mvarId!), goal)
      else
        pure (#[], goal)
    -- Change the context to that of the new goal
    goal.withContext do
      -- Handle 'using'
      let ctx? : Option Simp.Context ← l.mapM fun l => do
        pure (← Tactic.mkSimpContext (←`(tactic| simp only [$l,*])) false).ctx
      -- Run `mono`.
      let newGoals ← goal.mono side ctx? r.isSome true
      -- Cleanup:
      -- Replace all internal goal usernames with appropriate user-friendly ones.
      let _ ← liftMetaM <| newGoals.foldlM (init := 1) fun n g => do
        if (← g.getTag).isInternal' then
          g.setUserName <| (`mono).appendIndexAfter n
          pure (n+1)
    else
          pure n
      -- Name all `assertedMVarIds` `mono_with_<n>`, or just `mono_with` if there's only one.
      if assertedMVarIds.size == 1 then
        assertedMVarIds[0]!.setUserName `mono_with
      else
        let _ ← liftMetaM <| assertedMVarIds.foldlM (init := 1)
          fun n g => do g.setUserName <| (`mono_with).appendIndexAfter n; pure (n+1)
      -- Change all (possibly natural) goals to syntheticOpaque.
        for goal in newGoals do goal.setKind .syntheticOpaque
        replaceMainGoal (newGoals ++ assertedMVarIds.toList)
