import Mathlib.SynthZero.ToAdditive

section Mathlib.Tactic.Alias

namespace Tactic
namespace Alias

open Lean Elab Parser.Command

/-- Adds some copies of a theorem or definition. -/
syntax (name := alias) (docComment)? "alias " ident " ← " ident* : command

/-- Adds one-way implication declarations. -/
syntax (name := aliasLR) (docComment)? "alias " ident " ↔ " binderIdent binderIdent : command

/-- Like `++`, except that if the right argument starts with `_root_` the namespace will be
ignored.
```
appendNamespace `a.b `c.d = `a.b.c.d
appendNamespace `a.b `_root_.c.d = `c.d
```

TODO: Move this declaration to a more central location.
-/
def appendNamespace (ns : Name) : Name → Name
| .str .anonymous s => if s = "_root_" then Name.anonymous else Name.mkStr ns s
| .str p s          => Name.mkStr (appendNamespace ns p) s
| .num p n          => Name.mkNum (appendNamespace ns p) n
| .anonymous        => ns

/-- An alias can be in one of three forms -/
inductive Target
| plain : Name → Target
| forward : Name → Target
| backwards : Name → Target

/-- The docstring for an alias. -/
def Target.toString : Target → String
| Target.plain n => s!"**Alias** of `{n}`."
| Target.forward n => s!"**Alias** of the forward direction of `{n}`."
| Target.backwards n => s!"**Alias** of the reverse direction of `{n}`."

/-- Elaborates an `alias ←` command. -/
@[command_elab «alias»] def elabAlias : Command.CommandElab
| `($[$doc]? alias $name:ident ← $aliases:ident*) => do
  let resolved ← resolveGlobalConstNoOverloadWithInfo name
  let constant ← getConstInfo resolved
  let ns ← getCurrNamespace
  for a in aliases do withRef a do
    let declName := appendNamespace ns a.getId
    let decl ← match constant with
    | Lean.ConstantInfo.defnInfo d =>
      pure $ .defnDecl {
        d with name := declName
               value := mkConst resolved (d.levelParams.map mkLevelParam)
      }
    | Lean.ConstantInfo.thmInfo t =>
      pure $ .thmDecl {
        t with name := declName
               value := mkConst resolved (t.levelParams.map mkLevelParam)
      }
    | _ => throwError "alias only works with def or theorem"
    checkNotAlreadyDeclared declName
    addDeclarationRanges declName {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange a
    }
    -- TODO add @alias attribute
    Command.liftTermElabM do
      if isNoncomputable (← getEnv) resolved then
        addDecl decl
        setEnv $ addNoncomputable (← getEnv) declName
      else
        addAndCompile decl
      Term.addTermInfo' a (← mkConstWithLevelParams declName) (isBinder := true)
      let target := Target.plain resolved
      let docString := match doc with | none => target.toString
                                      | some d => d.getDocString
      addDocString declName docString
| _ => throwUnsupportedSyntax

/--
  Given a possibly forall-quantified iff expression `prf`, produce a value for one
  of the implication directions (determined by `mp`).
-/
def mkIffMpApp (mp : Bool) (ty prf : Expr) : MetaM Expr := do
  Meta.forallTelescope ty fun xs ty ↦ do
    let some (lhs, rhs) := ty.iff?
      | throwError "Target theorem must have the form `∀ x y z, a ↔ b`"
    Meta.mkLambdaFVars xs <|
      mkApp3 (mkConst (if mp then ``Iff.mp else ``Iff.mpr)) lhs rhs (mkAppN prf xs)

/--
  Given a constant representing an iff decl, adds a decl for one of the implication
  directions.
-/
def aliasIff (doc : Option (TSyntax `Lean.Parser.Command.docComment)) (ci : ConstantInfo)
  (ref : Syntax) (al : Name) (isForward : Bool) :
  TermElabM Unit := do
  let ls := ci.levelParams
  let v ← mkIffMpApp isForward ci.type ci.value!
  let t' ← Meta.inferType v
  -- TODO add @alias attribute
  addDeclarationRanges al {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange ref
  }
  addDecl $ .thmDecl {
    name := al
    value := v
    type := t'
    levelParams := ls
  }
  Term.addTermInfo' ref (← mkConstWithLevelParams al) (isBinder := true)
  let target := if isForward then Target.forward ci.name else Target.backwards ci.name
  let docString := match doc with | none => target.toString
                                  | some d => d.getDocString
  addDocString al docString

/-- Elaborates an `alias ↔` command. -/
@[command_elab aliasLR] def elabAliasLR : Command.CommandElab
| `($[$doc]? alias $name:ident ↔ $left:binderIdent $right:binderIdent) => do
  let resolved ← resolveGlobalConstNoOverloadWithInfo name
  let constant ← getConstInfo resolved
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    if let `(binderIdent| $x:ident) := left then
      aliasIff doc constant x (appendNamespace ns x.getId) true
    if let `(binderIdent| $x:ident) := right then
      aliasIff doc constant x (appendNamespace ns x.getId) false
| _ => throwUnsupportedSyntax



end Alias
end Tactic


end Mathlib.Tactic.Alias

section Std.Data.Nat.Lemmas

namespace Nat

@[simp] protected theorem not_le {a b : Nat} : ¬ a ≤ b ↔ b < a :=
  ⟨Nat.gt_of_not_le, Nat.not_le_of_gt⟩

protected theorem lt_of_add_lt_add_left {k n m : Nat} (h : k + n < k + m) : n < m :=
  Nat.lt_of_le_of_ne (Nat.le_of_add_le_add_left (Nat.le_of_lt h)) fun heq =>
    Nat.lt_irrefl (k + m) <| by rwa [heq] at h

protected theorem lt_of_add_lt_add_right {a b c : Nat} (h : a + b < c + b) : a < c :=
  Nat.lt_of_add_lt_add_left ((by rwa [Nat.add_comm b a, Nat.add_comm b c]): b + a < b + c)


theorem succ_pred_eq_of_pos : ∀ {n : Nat}, 0 < n → succ (pred n) = n
  | succ _, _ => rfl

protected theorem le_of_sub_eq_zero : ∀ {n m : Nat}, n - m = 0 → n ≤ m
  | n, 0, H => by rw [Nat.sub_zero] at H; simp [H]
  | 0, m+1, _ => Nat.zero_le (m + 1)
  | n+1, m+1, H => Nat.add_le_add_right
    (Nat.le_of_sub_eq_zero (by simp [Nat.add_sub_add_right] at H; exact H)) _

protected theorem sub_eq_iff_eq_add {a b c : Nat} (ab : b ≤ a) : a - b = c ↔ a = c + b :=
  ⟨fun c_eq => by rw [c_eq.symm, Nat.sub_add_cancel ab],
   fun a_eq => by rw [a_eq, Nat.add_sub_cancel]⟩

protected theorem lt_of_sub_eq_succ (H : m - n = succ l) : n < m :=
  Nat.not_le.1 fun H' => by simp [Nat.sub_eq_zero_of_le H'] at H

theorem succ_sub {m n : Nat} (h : n ≤ m) : succ m - n = succ (m - n) := by
  let ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, Nat.add_sub_cancel_left, ← add_succ, Nat.add_sub_cancel_left]

protected theorem sub_pos_of_lt (h : m < n) : 0 < n - m := by
  apply Nat.lt_of_add_lt_add_right (b := m)
  rwa [Nat.zero_add, Nat.sub_add_cancel (Nat.le_of_lt h)]

end Nat

end Std.Data.Nat.Lemmas

section Std.Data.Nat.Gcd

namespace Nat

/-- `m` and `n` are coprime, or relatively prime, if their `gcd` is 1. -/
@[reducible] def coprime (m n : Nat) : Prop := gcd m n = 1

end Nat

end Std.Data.Nat.Gcd

section Std.Classes.Cast

/-- Type class for the canonical homomorphism `Nat → R`. -/
class NatCast (R : Type u) where
  /-- The canonical map `Nat → R`. -/
  protected natCast : Nat → R

instance : NatCast Int where natCast n := Int.ofNat n

/-- Canonical homomorphism from `Nat` to a additive monoid `R` with a `1`.
This is just the bare function in order to aid in creating instances of `AddMonoidWithOne`. -/
@[reducible, match_pattern] protected def Nat.cast {R : Type u} [NatCast R] : Nat → R :=
  NatCast.natCast

-- see note [coercion into rings]
instance [NatCast R] : CoeHTCT Nat R where coe := Nat.cast

/-- Type class for the canonical homomorphism `Int → R`. -/
class IntCast (R : Type u) where
  /-- The canonical map `Int → R`. -/
  protected intCast : Int → R

/-- Canonical homomorphism from `Int` to a additive group `R` with a `1`.
This is just the bare function in order to aid in creating instances of `AddGroupWithOne`. -/
@[reducible, match_pattern] protected def Int.cast {R : Type u} [IntCast R] : Int → R :=
  IntCast.intCast

-- see note [coercion into rings]
instance [IntCast R] : CoeTail Int R where coe := Int.cast

end Std.Classes.Cast

section Std.Data.Int.Basic

namespace Int

scoped notation "-[" n "+1]" => negSucc n

end Int

end Std.Data.Int.Basic

section Std.Data.Int.Lemmas

open Nat

namespace Int

@[simp] theorem ofNat_eq_coe : ofNat n = Nat.cast n := rfl

@[simp] theorem ofNat_zero : ((0 : Nat) : Int) = 0 := rfl

/- ## Definitions of basic functions -/

theorem subNatNat_of_sub_eq_zero {m n : Nat} (h : n - m = 0) : subNatNat m n = ↑(m - n) := by
  rw [subNatNat, h, ofNat_eq_coe]

theorem subNatNat_of_sub_eq_succ {m n k : Nat} (h : n - m = succ k) : subNatNat m n = -[k+1] := by
  rw [subNatNat, h]

theorem ofNat_succ (n : Nat) : (succ n : Int) = n + 1 := rfl

@[local simp] theorem neg_ofNat_succ (n : Nat) : -(succ n : Int) = -[n+1] := rfl
@[local simp] theorem neg_negSucc (n : Nat) : -(-[n+1]) = succ n := rfl

theorem negSucc_coe (n : Nat) : -[n+1] = -↑(n + 1) := rfl

/- ## These are only for internal use -/

@[simp] theorem ofNat_add_ofNat (m n : Nat) : (↑m + ↑n : Int) = ↑(m + n) := rfl
@[simp] theorem ofNat_add_negSucc (m n : Nat) : ↑m + -[n+1] = subNatNat m (succ n) := rfl
@[simp] theorem negSucc_add_ofNat (m n : Nat) : -[m+1] + ↑n = subNatNat n (succ m) := rfl
@[simp] theorem negSucc_add_negSucc (m n : Nat) : -[m+1] + -[n+1] = -[succ (m + n) +1] := rfl

@[local simp] theorem ofNat_mul_ofNat (m n : Nat) : (↑m * ↑n : Int) = ↑(m * n) := rfl
@[local simp] theorem ofNat_mul_negSucc' (m n : Nat) : ↑m * -[n+1] = negOfNat (m * succ n) := rfl
@[local simp] theorem negSucc_mul_ofNat' (m n : Nat) : -[m+1] * ↑n = negOfNat (succ m * n) := rfl
@[local simp] theorem negSucc_mul_negSucc' (m n : Nat) :
    -[m+1] * -[n+1] = ofNat (succ m * succ n) := rfl

/- ## neg -/

protected theorem sub_eq_add_neg {a b : Int} : a - b = a + -b := rfl

/- ## basic properties of subNatNat -/

-- @[elabAsElim] -- TODO(Mario): unexpected eliminator resulting type
theorem subNatNat_elim (m n : Nat) (motive : Nat → Nat → Int → Prop)
    (hp : ∀ i n, motive (n + i) n i)
    (hn : ∀ i m, motive m (m + i + 1) -[i+1]) :
    motive m n (subNatNat m n) := by
  unfold subNatNat
  match h : n - m with
  | 0 =>
    have ⟨k, h⟩ := Nat.le.dest (Nat.le_of_sub_eq_zero h)
    rw [h.symm, Nat.add_sub_cancel_left]; apply hp
  | succ k =>
    rw [Nat.sub_eq_iff_eq_add (Nat.le_of_lt (Nat.lt_of_sub_eq_succ h))] at h
    rw [h, Nat.add_comm]; apply hn

theorem subNatNat_add_left : subNatNat (m + n) m = n := by
  unfold subNatNat
  rw [Nat.sub_eq_zero_of_le (Nat.le_add_right ..), Nat.add_sub_cancel_left, ofNat_eq_coe]

theorem subNatNat_add_right : subNatNat m (m + n + 1) = negSucc n := by
  simp [subNatNat, Nat.add_assoc, Nat.add_sub_cancel_left]

theorem subNatNat_add_add (m n k : Nat) : subNatNat (m + k) (n + k) = subNatNat m n := by
  apply subNatNat_elim m n (fun m n i => subNatNat (m + k) (n + k) = i)
  · intro i j
    rw [Nat.add_assoc, Nat.add_comm i k, ← Nat.add_assoc]
    exact subNatNat_add_left
  · intro i j
    rw [Nat.add_assoc j i 1, Nat.add_comm j (i+1), Nat.add_assoc, Nat.add_comm (i+1) (j+k)]
    exact subNatNat_add_right

theorem subNatNat_of_le {m n : Nat} (h : n ≤ m) : subNatNat m n = ↑(m - n) :=
  subNatNat_of_sub_eq_zero (Nat.sub_eq_zero_of_le h)

theorem subNatNat_of_lt {m n : Nat} (h : m < n) : subNatNat m n = -[pred (n - m) +1] :=
  subNatNat_of_sub_eq_succ <| (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)).symm



/- # ring properties -/

/- addition -/

protected theorem add_comm : ∀ a b : Int, a + b = b + a
  | ofNat n, ofNat m => by simp [Nat.add_comm]
  | ofNat _, -[_+1]  => rfl
  | -[_+1],  ofNat _ => rfl
  | -[_+1],  -[_+1]  => by simp [Nat.add_comm]

@[local simp] protected theorem add_zero : ∀ a : Int, a + 0 = a
  | ofNat _ => rfl
  | -[_+1]  => rfl

@[local simp] protected theorem zero_add (a : Int) : 0 + a = a := Int.add_comm .. ▸ a.add_zero


theorem subNatNat_sub (h : n ≤ m) (k : Nat) : subNatNat (m - n) k = subNatNat m (k + n) := by
  rwa [← subNatNat_add_add _ _ n, Nat.sub_add_cancel]

theorem subNatNat_add (m n k : Nat) : subNatNat (m + n) k = m + subNatNat n k := by
  cases n.lt_or_ge k with
  | inl h' =>
    simp [subNatNat_of_lt h', succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]
    conv => lhs; rw [← Nat.sub_add_cancel (Nat.le_of_lt h')]
    apply subNatNat_add_add
  | inr h' => simp [subNatNat_of_le h',
      subNatNat_of_le (Nat.le_trans h' (le_add_left ..)), Nat.add_sub_assoc h']

theorem subNatNat_add_negSucc (m n k : Nat) :
    subNatNat m n + -[k+1] = subNatNat m (n + succ k) := by
  have h := Nat.lt_or_ge m n
  cases h with
  | inr h' =>
    rw [subNatNat_of_le h']
    simp
    rw [subNatNat_sub h', Nat.add_comm]
  | inl h' =>
    have h₂ : m < n + succ k := Nat.lt_of_lt_of_le h' (le_add_right _ _)
    have h₃ : m ≤ n + k := le_of_succ_le_succ h₂
    rw [subNatNat_of_lt h', subNatNat_of_lt h₂]
    simp [Nat.add_comm]
    rw [← add_succ, succ_pred_eq_of_pos (Nat.sub_pos_of_lt h'), add_succ, succ_sub h₃, Nat.pred_succ]
    rw [Nat.add_comm n, Nat.add_sub_assoc (Nat.le_of_lt h')]

protected theorem add_assoc : ∀ a b c : Int, a + b + c = a + (b + c)
  | (m:Nat), (n:Nat), c => aux1 ..
  | Nat.cast m, b, Nat.cast k => by
    rw [Int.add_comm, ← aux1, Int.add_comm k, aux1, Int.add_comm b]
  | a, (n:Nat), (k:Nat) => by
    rw [Int.add_comm, Int.add_comm a, ← aux1, Int.add_comm a, Int.add_comm k]
  | -[m+1], -[n+1], (k:Nat) => aux2 ..
  | -[m+1], (n:Nat), -[k+1] => by
    rw [Int.add_comm, ← aux2, Int.add_comm n, ← aux2, Int.add_comm -[m+1]]
  | (m:Nat), -[n+1], -[k+1] => by
    rw [Int.add_comm, Int.add_comm m, Int.add_comm m, ← aux2, Int.add_comm -[k+1]]
  | -[m+1], -[n+1], -[k+1] => by
    simp [add_succ, Nat.add_comm, Nat.add_left_comm, neg_ofNat_succ]
where
  aux1 (m n : Nat) : ∀ c : Int, m + n + c = m + (n + c)
    | (k:Nat) => by simp [Nat.add_assoc]
    | -[k+1]  => by simp [subNatNat_add]
  aux2 (m n k : Nat) : -[m+1] + -[n+1] + k = -[m+1] + (-[n+1] + k) := by
    simp [add_succ]
    rw [Int.add_comm, subNatNat_add_negSucc]
    simp [add_succ, succ_add, Nat.add_comm]

/- ## negation -/

theorem subNatNat_self : ∀ n, subNatNat n n = 0
  | 0      => rfl
  | succ m => by rw [subNatNat_of_sub_eq_zero (Nat.sub_self ..), Nat.sub_self, ofNat_zero]

attribute [local simp] subNatNat_self

@[local simp] protected theorem add_left_neg : ∀ a : Int, -a + a = 0
  | 0      => rfl
  | succ m => by simp
  | -[m+1] => by simp

@[local simp] protected theorem add_right_neg (a : Int) : a + -a = 0 := by
  rw [Int.add_comm, Int.add_left_neg]

@[simp] protected theorem neg_eq_of_add_eq_zero {a b : Int} (h : a + b = 0) : -a = b := by
  rw [← Int.add_zero (-a), ← h, ← Int.add_assoc, Int.add_left_neg, Int.zero_add]

/- ## multiplication -/

@[simp] theorem negSucc_mul_ofNat (m n : Nat) : -[m+1] * n = -↑(succ m * n) := rfl

protected theorem mul_comm (a b : Int) : a * b = b * a := by
  cases a <;> cases b <;> simp [Nat.mul_comm]

theorem ofNat_mul_negOfNat (m n : Nat) : (m : Nat) * negOfNat n = negOfNat (m * n) := by
  cases n <;> rfl

theorem negOfNat_mul_ofNat (m n : Nat) : negOfNat m * (n : Nat) = negOfNat (m * n) := by
  rw [Int.mul_comm]; simp [ofNat_mul_negOfNat, Nat.mul_comm]

theorem negSucc_mul_negOfNat (m n : Nat) : -[m+1] * negOfNat n = ofNat (succ m * n) := by
  cases n <;> rfl

theorem negOfNat_mul_negSucc (m n : Nat) : negOfNat n * -[m+1] = ofNat (n * succ m) := by
  rw [Int.mul_comm, negSucc_mul_negOfNat, Nat.mul_comm]

attribute [local simp] ofNat_mul_negOfNat negOfNat_mul_ofNat
  negSucc_mul_negOfNat negOfNat_mul_negSucc

protected theorem mul_assoc (a b c : Int) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [Nat.mul_assoc]

@[simp] protected theorem mul_zero (a : Int) : a * 0 = 0 := by cases a <;> rfl

@[simp] protected theorem zero_mul (a : Int) : 0 * a = 0 := Int.mul_comm .. ▸ a.mul_zero

theorem negOfNat_eq_subNatNat_zero (n) : negOfNat n = subNatNat 0 n := by cases n <;> rfl

theorem ofNat_mul_subNatNat (m n k : Nat) :
    m * subNatNat n k = subNatNat (m * n) (m * k) := by
  cases m with
  | zero => simp [ofNat_zero, Int.zero_mul, Nat.zero_mul]
  | succ m => cases n.lt_or_ge k with
    | inl h =>
      have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
      simp [subNatNat_of_lt h, subNatNat_of_lt h']
      rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), ← neg_ofNat_succ, Nat.mul_sub_left_distrib,
        ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]; rfl
    | inr h =>
      have h' : succ m * k ≤ succ m * n := Nat.mul_le_mul_left _ h
      simp [subNatNat_of_le h, subNatNat_of_le h', Nat.mul_sub_left_distrib]

theorem negOfNat_add (m n : Nat) : negOfNat m + negOfNat n = negOfNat (m + n) := by
  cases m <;> cases n <;> simp [Nat.succ_add] <;> rfl

theorem negSucc_mul_subNatNat (m n k : Nat) :
    -[m+1] * subNatNat n k = subNatNat (succ m * k) (succ m * n) := by
  cases n.lt_or_ge k with
  | inl h =>
    have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
    rw [subNatNat_of_lt h, subNatNat_of_le (Nat.le_of_lt h')]
    simp [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), Nat.mul_sub_left_distrib]
  | inr h => cases Nat.lt_or_ge k n with
    | inl h' =>
      have h₁ : succ m * n > succ m * k := Nat.mul_lt_mul_of_pos_left h' (Nat.succ_pos m)
      rw [subNatNat_of_le h, subNatNat_of_lt h₁, negSucc_mul_ofNat,
        Nat.mul_sub_left_distrib, ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁)]; rfl
    | inr h' => rw [Nat.le_antisymm h h', subNatNat_self, subNatNat_self, Int.mul_zero]

attribute [local simp] ofNat_mul_subNatNat negOfNat_add negSucc_mul_subNatNat

protected theorem mul_add : ∀ a b c : Int, a * (b + c) = a * b + a * c
  | (m:Nat), (n:Nat), (k:Nat) => by simp [Nat.left_distrib]
  | (m:Nat), (n:Nat), -[k+1]  => by
    simp [negOfNat_eq_subNatNat_zero]; rw [← subNatNat_add]; rfl
  | (m:Nat), -[n+1],  (k:Nat) => by
    simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ← subNatNat_add]; rfl
  | (m:Nat), -[n+1],  -[k+1]  => by simp; rw [← Nat.left_distrib, succ_add]; rfl
  | -[m+1],  (n:Nat), (k:Nat) => by simp [Nat.mul_comm]; rw [← Nat.right_distrib, Nat.mul_comm]
  | -[m+1],  (n:Nat), -[k+1]  => by
    simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ← subNatNat_add]; rfl
  | -[m+1],  -[n+1],  (k:Nat) => by simp [negOfNat_eq_subNatNat_zero]; rw [← subNatNat_add]; rfl
  | -[m+1],  -[n+1],  -[k+1]  => by simp; rw [← Nat.left_distrib, succ_add]; rfl

protected theorem add_mul (a b c : Int) : (a + b) * c = a * c + b * c := by
  simp [Int.mul_comm, Int.mul_add]

protected theorem neg_mul_eq_neg_mul (a b : Int) : -(a * b) = -a * b :=
  Int.neg_eq_of_add_eq_zero <| by rw [← Int.add_mul, Int.add_right_neg, Int.zero_mul]

@[local simp] protected theorem neg_mul (a b : Int) : -a * b = -(a * b) :=
  (Int.neg_mul_eq_neg_mul a b).symm

@[simp] protected theorem one_mul : ∀ a : Int, 1 * a = a
  | ofNat n => show ofNat (1 * n) = ofNat n by rw [Nat.one_mul]
  | -[n+1]  => show -[1 * n +1] = -[n+1] by rw [Nat.one_mul]

@[simp] protected theorem mul_one (a : Int) : a * 1 = a := by rw [Int.mul_comm, Int.one_mul]

end Int

end Std.Data.Int.Lemmas

section Std.Data.Rat.Basic

/--
Rational numbers, implemented as a pair of integers `num / den` such that the
denominator is positive and the numerator and denominator are coprime.
-/
structure Rat where
  /-- Constructs a rational number from components.
  We rename the constructor to `mk'` to avoid a clash with the smart constructor. -/
  mk' ::
  /-- The numerator of the rational number is an integer. -/
  num : Int
  /-- The denominator of the rational number is a natural number. -/
  den : Nat := 1
  /-- The denominator is nonzero. -/
  den_nz : den ≠ 0 := by decide
  /-- The numerator and denominator are coprime: it is in "reduced form". -/
  reduced : num.natAbs.coprime den := by decide
  deriving DecidableEq

end Std.Data.Rat.Basic

section Std.Classes.RatCast

/-- Type class for the canonical homomorphism `Rat → K`. -/
class RatCast (K : Type u) where
  /-- The canonical homomorphism `Rat → K`. -/
  protected ratCast : Rat → K

/-- Canonical homomorphism from `Rat` to a division ring `K`.
This is just the bare function in order to aid in creating instances of `DivisionRing`. -/
@[reducible, match_pattern] protected def Rat.cast {K : Type u} [RatCast K] : Rat → K :=
  RatCast.ratCast

end Std.Classes.RatCast

section Mathlib.Init.ZeroOne

/-! ## Classes for `Zero` and `One` -/

class Zero.{u} (α : Type u) where
  zero : α

instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

@[to_additive]
class One (α : Type u) where
  one : α

@[to_additive existing Zero.toOfNat0]
instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

attribute [to_additive_change_numeral 2] OfNat OfNat.ofNat

end Mathlib.Init.ZeroOne

section Mathlib.Init.Data.Int.Basic

notation "ℤ" => Int

end Mathlib.Init.Data.Int.Basic

section Mathlib.Init.Function

namespace Function

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

/-- `LeftInverse g f` means that g is a left inverse to f. That is, `g ∘ f = id`. -/
def LeftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x

theorem LeftInverse.injective {g : β → α} {f : α → β} : LeftInverse g f → Injective f :=
λ h a b hf => h a ▸ h b ▸ hf ▸ rfl

end Function


end Mathlib.Init.Function

section Mathlib.Logic.Basic

attribute [local instance 10] Classical.propDecidable

theorem or_iff_not_imp_left : a ∨ b ↔ ¬a → b := Decidable.or_iff_not_imp_left

end Mathlib.Logic.Basic

section Mathlib.Logic.Function.Basic

namespace Function

/-- A function is involutive, if `f ∘ f = id`. -/
def Involutive {α} (f : α → α) : Prop :=
  ∀ x, f (f x) = x

namespace Involutive

variable {α : Sort u} {f : α → α} (h : Involutive f)

protected theorem leftInverse : LeftInverse f f := h

protected theorem injective : Injective f := h.leftInverse.injective

end Involutive

end Function


end Mathlib.Logic.Function.Basic

section Mathlib.Algebra.Group.Defs

attribute [to_additive existing] Mul Div HMul instHMul HDiv instHDiv

/-- Class of types that have an inversion operation. -/
@[to_additive, notation_class]
class Inv (α : Type u) where
  /-- Invert an element of α. -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

section Mul

variable [Mul G]

/-- A mixin for left cancellative multiplication. -/
class IsLeftCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is left cancellative. -/
  protected mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c
/-- A mixin for right cancellative multiplication. -/
class IsRightCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is right cancellative. -/
  protected mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c
/-- A mixin for cancellative multiplication. -/
class IsCancelMul (G : Type u) [Mul G] extends IsLeftCancelMul G, IsRightCancelMul G : Prop

/-- A mixin for left cancellative addition. -/
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is left cancellative. -/
  protected add_left_cancel : ∀ a b c : G, a + b = a + c → b = c

attribute [to_additive IsLeftCancelAdd] IsLeftCancelMul

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  IsLeftCancelMul.mul_left_cancel a b c

end IsLeftCancelMul

end Mul

/-- A semigroup is a type with an associative `(*)`. -/
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

/-- An additive semigroup is a type with an associative `(+)`. -/
class AddSemigroup (G : Type u) extends Add G where
  /-- Addition is associative -/
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

attribute [to_additive] Semigroup

section Semigroup

variable [Semigroup G]

@[to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc

end Semigroup

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
class CommSemigroup (G : Type u) extends Semigroup G where
  /-- Multiplication is commutative in a commutative semigroup. -/
  mul_comm : ∀ a b : G, a * b = b * a

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
class AddCommSemigroup (G : Type u) extends AddSemigroup G where
  /-- Addition is commutative in an additive commutative semigroup. -/
  add_comm : ∀ a b : G, a + b = b + a

attribute [to_additive] CommSemigroup

/-- A `LeftCancelSemigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c

/-- An `AddLeftCancelSemigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_left_cancel : ∀ a b c : G, a + b = a + c → b = c

attribute [to_additive] LeftCancelSemigroup

/-- Any `LeftCancelSemigroup` satisfies `IsLeftCancelMul`. -/
@[to_additive AddLeftCancelSemigroup.toIsLeftCancelAdd "Any `AddLeftCancelSemigroup` satisfies
`IsLeftCancelAdd`."]
instance (priority := 100) LeftCancelSemigroup.toIsLeftCancelMul (G : Type u)
    [LeftCancelSemigroup G] : IsLeftCancelMul G :=
  { mul_left_cancel := LeftCancelSemigroup.mul_left_cancel }

/-- A `RightCancelSemigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
class RightCancelSemigroup (G : Type u) extends Semigroup G where
  mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c

/-- An `AddRightCancelSemigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

attribute [to_additive] RightCancelSemigroup


/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  /-- One is a left neutral element for multiplication -/
  one_mul : ∀ a : M, 1 * a = a
  /-- One is a right neutral element for multiplication -/
  mul_one : ∀ a : M, a * 1 = a

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (M : Type u) extends Zero M, Add M where
  /-- Zero is a left neutral element for addition -/
  zero_add : ∀ a : M, 0 + a = a
  /-- Zero is a right neutral element for addition -/
  add_zero : ∀ a : M, a + 0 = a

attribute [to_additive] MulOneClass

section MulOneClass

variable {M : Type u} [MulOneClass M]

@[to_additive (attr := simp)]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul

@[to_additive (attr := simp)]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one

end MulOneClass

section

variable {M : Type u}

-- use `x * npowRec n x` and not `npowRec n x * x` in the definition to make sure that
-- definitional unfolding of `npowRec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `npowRec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => a * npowRec n a

/-- The fundamental scalar multiplication in an additive monoid. `nsmulRec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmulRec n a

attribute [to_additive existing] npowRec

end


/-- An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmulRec
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl


/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  /-- Raising to the power of a natural number. -/
  npow : ℕ → M → M := npowRec
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = x * npow n x := by intros; rfl


-- Bug #660
attribute [to_additive existing] Monoid.toMulOneClass

section Monoid

variable {M : Type u} [Monoid M]

@[to_additive]
theorem left_inv_eq_right_inv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

end Monoid

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[to_additive]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

attribute [to_additive existing] CommMonoid.toCommSemigroup

section LeftCancelMonoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddLeftCancelSemigroup` is not enough. -/
class AddLeftCancelMonoid (M : Type u) extends AddLeftCancelSemigroup M, AddMonoid M

/-- A monoid in which multiplication is left-cancellative. -/
@[to_additive]
class LeftCancelMonoid (M : Type u) extends LeftCancelSemigroup M, Monoid M

attribute [to_additive existing] LeftCancelMonoid.toMonoid

end LeftCancelMonoid

section RightCancelMonoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelSemigroup` is not enough. -/
class AddRightCancelMonoid (M : Type u) extends AddRightCancelSemigroup M, AddMonoid M

/-- A monoid in which multiplication is right-cancellative. -/
@[to_additive]
class RightCancelMonoid (M : Type u) extends RightCancelSemigroup M, Monoid M

attribute [to_additive existing] RightCancelMonoid.toMonoid

end RightCancelMonoid

section CancelMonoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelMonoid` is not enough. -/
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

/-- A monoid in which multiplication is cancellative. -/
@[to_additive]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M

attribute [to_additive existing] CancelMonoid.toRightCancelMonoid

end CancelMonoid

/-- The fundamental power operation in a group. `zpowRec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`,  which has better definitional behavior. -/
def zpowRec {M : Type _} [One M] [Mul M] [Inv M] : ℤ → M → M
  | Int.ofNat n, a => npowRec n a
  | Int.negSucc n, a => (npowRec n.succ a)⁻¹

/-- The fundamental scalar multiplication in an additive group. `zpowRec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmulRec {M : Type _} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmulRec n a
  | Int.negSucc n, a => -nsmulRec n.succ a

attribute [to_additive existing] zpowRec

section InvolutiveInv

/-- Auxiliary typeclass for types with an involutive `Neg`. -/
class InvolutiveNeg (A : Type _) extends Neg A where
  neg_neg : ∀ x : A, - -x = x


/-- Auxiliary typeclass for types with an involutive `Inv`. -/
@[to_additive]
class InvolutiveInv (G : Type _) extends Inv G where
  inv_inv : ∀ x : G, x⁻¹⁻¹ = x


variable [InvolutiveInv G]

@[to_additive (attr := simp)]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  InvolutiveInv.inv_inv _

end InvolutiveInv

/-!
### Design note on `DivInvMonoid`/`SubNegMonoid` and `DivisionMonoid`/`SubtractionMonoid`

Those two pairs of made-up classes fulfill slightly different roles.

`DivInvMonoid`/`SubNegMonoid` provides the minimum amount of information to define the
`ℤ` action (`zpow` or `zsmul`). Further, it provides a `div` field, matching the forgetful
inheritance pattern. This is useful to shorten extension clauses of stronger structures (`Group`,
`GroupWithZero`, `DivisionRing`, `Field`) and for a few structures with a rather weak
pseudo-inverse (`matrix`).

`DivisionMonoid`/`SubtractionMonoid` is targeted at structures with stronger pseudo-inverses. It
is an ad hoc collection of axioms that are mainly respected by three things:
* Groups
* Groups with zero
* The pointwise monoids `Set α`, `Finset α`, `Filter α`

It acts as a middle ground for structures with an inversion operator that plays well with
multiplication, except for the fact that it might not be a true inverse (`a / a ≠ 1` in general).
The axioms are pretty arbitrary (many other combinations are equivalent to it), but they are
independent:
* Without `DivisionMonoid.div_eq_mul_inv`, you can define `/` arbitrarily.
* Without `DivisionMonoid.inv_inv`, you can consider `WithTop unit` with `a⁻¹ = ⊤` for all `a`.
* Without `DivisionMonoid.mul_inv_rev`, you can consider `WithTop α` with `a⁻¹ = a` for all `a`
  where `α` non commutative.
* Without `DivisionMonoid.inv_eq_of_mul`, you can consider any `CommMonoid` with `a⁻¹ = a` for all
  `a`.

As a consequence, a few natural structures do not fit in this framework. For example, `ENNReal`
respects everything except for the fact that `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0 * ∞ = 0`.
-/

/-- In a class equipped with instances of both `Monoid` and `Inv`, this definition records what the
default definition for `Div` would be: `a * b⁻¹`.  This is later provided as the default value for
the `Div` instance in `DivInvMonoid`.

We keep it as a separate definition rather than inlining it in `DivInvMonoid` so that the `Div`
field of individual `DivInvMonoid`s constructed using that default value will not be unfolded at
`.instance` transparency. -/
def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹

/-- A `DivInvMonoid` is a `Monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `Foo X` be a type with a `∀ X, Div (Foo X)` instance but no
`∀ X, Inv (Foo X)`, e.g. when `Foo X` is a `EuclideanDomain`. Suppose we
also have an instance `∀ X [Cromulent X], GroupWithZero (Foo X)`. Then the
`(/)` coming from `GroupWithZero.div` cannot be definitionally equal to
the `(/)` coming from `Foo.Div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `Monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  div := DivInvMonoid.div'
  /-- `a / b := a * b⁻¹` -/
  div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  /-- The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
  zpow : ℤ → G → G := zpowRec
  /-- `a ^ 0 = 1` -/
  zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a * a ^ n` -/
  zpow_succ' (n : ℕ) (a : G) : zpow (Int.ofNat n.succ) a = a * zpow (Int.ofNat n) a := by
    intros; rfl
  /-- `a ^ -(n + 1) = (a ^ (n + 1))⁻¹` -/
  zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl

/-- In a class equipped with instances of both `AddMonoid` and `Neg`, this definition records what
the default definition for `Sub` would be: `a + -b`.  This is later provided as the default value
for the `Sub` instance in `SubNegMonoid`.

We keep it as a separate definition rather than inlining it in `SubNegMonoid` so that the `Sub`
field of individual `SubNegMonoid`s constructed using that default value will not be unfolded at
`.instance` transparency. -/
def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b

attribute [to_additive existing SubNegMonoid.sub'] DivInvMonoid.div'

/-- A `SubNegMonoid` is an `AddMonoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, Sub (Foo X)` instance but no
`∀ X, Neg (Foo X)`. Suppose we also have an instance
`∀ X [Cromulent X], AddGroup (Foo X)`. Then the `(-)` coming from
`AddGroup.sub` cannot be definitionally equal to the `(-)` coming from
`Foo.Sub`.

In the same way, adding a `zsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `AddMonoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  sub := SubNegMonoid.sub'
  sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  zsmul : ℤ → G → G := zsmulRec
  zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  zsmul_succ' (n : ℕ) (a : G) : zsmul (Int.ofNat n.succ) a = a + zsmul (Int.ofNat n) a := by
    intros; rfl
  zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by intros; rfl

attribute [to_additive SubNegMonoid] DivInvMonoid

section DivInvMonoid

variable [DivInvMonoid G] {a b : G}

/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `DivInvMonoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive "Subtracting an element is the same as adding by its negative.
This is a duplicate of `SubNegMonoid.sub_eq_mul_neg` ensuring that the types unfold better."]
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _

end DivInvMonoid


/-- A `SubtractionMonoid` is a `SubNegMonoid` with involutive negation and such that
`-(a + b) = -b + -a` and `a + b = 0 → -a = b`. -/
class SubtractionMonoid (G : Type u) extends SubNegMonoid G, InvolutiveNeg G where
  neg_add_rev (a b : G) : -(a + b) = -b + -a
  /- Despite the asymmetry of `neg_eq_of_add`, the symmetric version is true thanks to the
  involutivity of negation. -/
  neg_eq_of_add (a b : G) : a + b = 0 → -a = b

/-- A `DivisionMonoid` is a `DivInvMonoid` with involutive inversion and such that
`(a * b)⁻¹ = b⁻¹ * a⁻¹` and `a * b = 1 → a⁻¹ = b`.

This is the immediate common ancestor of `Group` and `GroupWithZero`. -/
@[to_additive SubtractionMonoid]
class DivisionMonoid (G : Type u) extends DivInvMonoid G, InvolutiveInv G where
  mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  /- Despite the asymmetry of `inv_eq_of_mul`, the symmetric version is true thanks to the
  involutivity of inversion. -/
  inv_eq_of_mul (a b : G) : a * b = 1 → a⁻¹ = b

attribute [to_additive existing] DivisionMonoid.toInvolutiveInv

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive (attr := simp) neg_add_rev]
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  DivisionMonoid.mul_inv_rev _ _

@[to_additive]
theorem inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b :=
  DivisionMonoid.inv_eq_of_mul _ _

end DivisionMonoid



/-- A `Group` is a `Monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.
-/
class Group (G : Type u) extends DivInvMonoid G where
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1

/-- An `AddGroup` is an `AddMonoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.
-/
class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg : ∀ a : A, -a + a = 0

attribute [to_additive] Group

section Group

variable [Group G] {a b c : G}

@[to_additive (attr := simp)]
theorem mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
  Group.mul_left_inv

@[to_additive]
theorem inv_mul_self (a : G) : a⁻¹ * a = 1 :=
  mul_left_inv a

@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_self a) h

@[to_additive (attr := simp)]
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
  by rw [← mul_left_inv a⁻¹, inv_eq_of_mul (mul_left_inv a)]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
  by rw [← mul_assoc, mul_left_inv, one_mul]

@[to_additive (attr := simp)]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
  by rw [← mul_assoc, mul_right_inv, one_mul]

@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a :=
  by rw [mul_assoc, mul_right_inv, mul_one]

@[to_additive AddGroup.toSubtractionMonoid]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G :=
  { inv_inv := fun a ↦ inv_eq_of_mul (mul_left_inv a)
    mul_inv_rev :=
      fun a b ↦ inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_right_inv]
    inv_eq_of_mul := fun _ _ ↦ inv_eq_of_mul }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G :=
  { ‹Group G› with
    mul_right_cancel := fun a b c h ↦ by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]
    mul_left_cancel := fun a b c h ↦ by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left] }

end Group

/-- An additive commutative group is an additive group with commutative `(+)`. -/
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

end Mathlib.Algebra.Group.Defs

section Mathlib.Algebra.Group.Basic

section InvolutiveInv

variable [InvolutiveInv G] {a b : G}

@[to_additive (attr := simp)]
theorem inv_involutive : Function.Involutive (Inv.inv : G → G) :=
  inv_inv

@[to_additive]
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.injective

end InvolutiveInv

section DivisionMonoid

variable [DivisionMonoid α] {a b c : α}

@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a :=
  by rw [← inv_eq_of_mul_eq_one_right h, inv_inv]

@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm

@[to_additive]
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]

end DivisionMonoid

section Group

variable [Group G] {a b c d : G}

@[to_additive (attr := simp) sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_right_inv a]

@[to_additive]
theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h ↦ by rw [h, div_self']⟩

alias div_eq_one ↔ _ div_eq_one_of_eq

alias sub_eq_zero ↔ _ sub_eq_zero_of_eq

end Group

end Mathlib.Algebra.Group.Basic

section Mathlib.Logic.Nontrivial

/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
class Nontrivial (α : Type _) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : ∃ x y : α, x ≠ y

theorem exists_pair_ne (α : Type _) [Nontrivial α] : ∃ x y : α, x ≠ y :=
  Nontrivial.exists_pair_ne

end Mathlib.Logic.Nontrivial

section Mathlib.Algebra.NeZero

/-- A type-class version of `n ≠ 0`.  -/
class NeZero {R} [Zero R] (n : R) : Prop where
  /-- The proposition that `n` is not zero. -/
  out : n ≠ 0

theorem NeZero.ne' {R} [Zero R] (n : R) [h : NeZero n] : 0 ≠ n :=
  h.out.symm

section
variable {α : Type _} [Zero α]

@[simp] theorem zero_ne_one [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := NeZero.ne' (1 : α)

end

end Mathlib.Algebra.NeZero

section Mathlib.Algebra.GroupWithZero.Defs

universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `GroupWithZero.div'` cannot contain a universe metavariable.
variable {G₀ : Type u} {M₀ M₀' G₀' : Type _}

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ a : M₀, 0 * a = 0
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ a : M₀, a * 0 = 0

/-- A mixin for left cancellative multiplication by nonzero elements. -/
class IsLeftCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplicatin by a nonzero element is left cancellative. -/
  protected mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c

section IsLeftCancelMulZero

variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h

end IsLeftCancelMulZero

/-- A mixin for right cancellative multiplication by nonzero elements. -/
class IsRightCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplicatin by a nonzero element is right cancellative. -/
  protected mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c

/-- A mixin for cancellative multiplication by nonzero elements. -/
class IsCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀]
  extends IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀ : Prop

export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `G₀`. -/
class NoZeroDivisors (M₀ : Type _) [Mul M₀] [Zero M₀] : Prop where
  /-- For all `a` and `b` of `G₀`, `a * b = 0` implies `a = 0` or `b = 0`. -/
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0

/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀

/-- A typeclass for non-associative monoids with zero elements. -/
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

/-- A type `M` is a `CancelMonoidWithZero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
class CancelMonoidWithZero (M₀ : Type _) extends MonoidWithZero M₀, IsCancelMulZero M₀

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
class CommMonoidWithZero (M₀ : Type _) extends CommMonoid M₀, MonoidWithZero M₀

/-- A type `M` is a `CancelCommMonoidWithZero` if it is a commutative monoid with zero element,
 `0` is left and right absorbing,
  and left/right multiplication by a non-zero element is injective. -/
class CancelCommMonoidWithZero (M₀ : Type _) extends CommMonoidWithZero M₀, IsLeftCancelMulZero M₀

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.-/
class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀ where
  /-- The inverse of `0` in a group with zero is `0`. -/
  inv_zero : (0 : G₀)⁻¹ = 0
  /-- Every nonzero element of a group with zero is invertible. -/
  mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1

@[simp] theorem mul_inv_cancel [GroupWithZero G₀] {a : G₀} (h : a ≠ 0) : a * a⁻¹ = 1 :=
GroupWithZero.mul_inv_cancel a h

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class CommGroupWithZero (G₀ : Type _) extends CommMonoidWithZero G₀, GroupWithZero G₀

section NeZero

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

variable (M₀)

/-- In a nontrivial monoid with zero, zero and one are different. -/
instance NeZero.one : NeZero (1 : M₀) := ⟨by
  intro h
  cases exists_pair_ne M₀ with
  | intro x yh => cases yh with
    | intro y hx =>
        apply hx
        calc
          x = 1 * x := by rw [one_mul]
          _ = 0 := by rw [h, zero_mul]
          _ = 1 * y := by rw [h, zero_mul]
          _ = y := by rw [one_mul]⟩

end NeZero

end Mathlib.Algebra.GroupWithZero.Defs

section Mathlib.Data.Nat.Cast.Defs

/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast {R : Type u} [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1



/-! ### Additive monoids with one -/

/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
class AddMonoidWithOne (R : Type u) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  /-- The canonical map `ℕ → R` sends `0 : ℕ` to `0 : R`. -/
  natCast_zero : natCast 0 = 0 := by intros; rfl
  /-- The canonical map `ℕ → R` is a homomorphism. -/
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl

/-- An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`.  -/
class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOne R, AddCommMonoid R

end Mathlib.Data.Nat.Cast.Defs

section Mathlib.Data.Int.Cast.Defs

/-- Default value for `IntCast.intCast` in an `AddGroupWithOne`. -/
protected def Int.castDef {R : Type u} [NatCast R] [Neg R] : ℤ → R
  | (n : ℕ) => n
  | Int.negSucc n => -(n + 1 : ℕ)


/-! ### Additive groups with one -/

/-- An `AddGroupWithOne` is an `AddGroup` with a 1. It also contains data for the unique
homomorphisms `ℕ → R` and `ℤ → R`. -/
class AddGroupWithOne (R : Type u) extends IntCast R, AddMonoidWithOne R, AddGroup R where
  /-- The canonical homorphism `ℤ → R`. -/
  intCast := Int.castDef
  /-- The canonical homorphism `ℤ → R` agrees with the one from `ℕ → R` on `ℕ`. -/
  intCast_ofNat : ∀ n : ℕ, intCast (n : ℕ) = Nat.cast n := by intros; rfl
  /-- The canonical homorphism `ℤ → R` for negative values is just the negation of the values
  of the canonical homomorphism `ℕ → R`. -/
  intCast_negSucc : ∀ n : ℕ, intCast (Int.negSucc n) = - Nat.cast (n + 1) := by intros; rfl

/-- An `AddCommGroupWithOne` is an `AddGroupWithOne` satisfying `a + b = b + a`. -/
class AddCommGroupWithOne (R : Type u)
  extends AddCommGroup R, AddGroupWithOne R, AddCommMonoidWithOne R

end Mathlib.Data.Int.Cast.Defs

section Mathlib.Tactic.Spread

open Lean Parser.Term Macro

/-
This adds support for structure instance spread syntax.

```lean
instance : Foo α where
  __ := instSomething -- include fields from `instSomething`

example : Foo α := {
  __ := instSomething -- include fields from `instSomething`
}
```
-/

macro_rules
| `({ $[$srcs,* with]? $[$fields],* $[: $ty?]? }) => do
    let mut spreads := #[]
    let mut newFields := #[]

    for field in fields do
      match field.1 with
        | `(structInstField| $name:ident := $arg) =>
          if name.getId.eraseMacroScopes == `__ then do
            spreads := spreads.push arg
          else
            newFields := newFields.push field
        | `(structInstFieldAbbrev| $_:ident) =>
          newFields := newFields.push field
        | _ =>
          throwUnsupported

    if spreads.isEmpty then throwUnsupported

    let srcs := (srcs.map (·.getElems)).getD {} ++ spreads
    `({ $srcs,* with $[$newFields],* $[: $ty?]? })

end Mathlib.Tactic.Spread

section Mathlib.Algebra.Ring.Defs

/-!
### `distrib` class
-/

/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
class Distrib (R : Type _) extends Mul R, Add R where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- A typeclass stating that multiplication is left distributive over addition. -/
class LeftDistribClass (R : Type _) [Mul R] [Add R] where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c

/-- A typeclass stating that multiplication is right distributive over addition. -/
class RightDistribClass (R : Type _) [Mul R] [Add R] where
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

-- see Note [lower instance priority]
instance (priority := 100) Distrib.leftDistribClass (R : Type _) [Distrib R] : LeftDistribClass R :=
  ⟨Distrib.left_distrib⟩

-- see Note [lower instance priority]
instance (priority := 100) Distrib.rightDistribClass (R : Type _) [Distrib R] :
    RightDistribClass R :=
  ⟨Distrib.right_distrib⟩

theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) :
    a * (b + c) = a * b + a * c :=
  LeftDistribClass.left_distrib a b c

alias left_distrib ← mul_add

theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c

alias right_distrib ← add_mul

/-!
### Classes of semirings and rings

We make sure that the canonical path from `NonAssocSemiring` to `Ring` passes through `Semiring`,
as this is a path which is followed all the time in linear algebra where the defining semilinear map
`σ : R →+* S` depends on the `NonAssocSemiring` structure of `R` and `S` while the module
definition depends on the `Semiring` structure.

It is not currently possible to adjust priorities by hand (see lean4#2115). Instead, the last
declared instance is used, so we make sure that `Semiring` is declared after `NonAssocRing`, so
that `Semiring -> NonAssocSemiring` is tried before `NonAssocRing -> NonAssocSemiring`.
TODO: clean this once lean4#2115 is fixed
-/

/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

/-- An associative but not-necessarily unital semiring. -/
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

/-- A unital but not-necessarily-associative semiring. -/
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

/-- A not-necessarily-unital, not-necessarily-associative ring. -/
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

-- We defer the instance `NonUnitalNonAssocRing.toHasDistribNeg` to `Algebra.Ring.Basic`
-- as it relies on the lemma `eq_neg_of_add_eq_zero_left`.
/-- An associative but not-necessarily unital ring. -/
class NonUnitalRing (α : Type _) extends NonUnitalNonAssocRing α, NonUnitalSemiring α

/-- A unital but not-necessarily-associative ring. -/
class NonAssocRing (α : Type _) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
    AddCommGroupWithOne α

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R

class CommSemiring (R : Type u) extends Semiring R, CommMonoid R

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toCommMonoidWithZero [CommSemiring α] :
    CommMonoidWithZero α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }

section HasDistribNeg

/-- Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without having to duplicate
lemmas. -/
class HasDistribNeg (α : Type _) [Mul α] extends InvolutiveNeg α where
  /-- Negation is left distributive over multiplication -/
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  /-- Negation is right distributive over multiplication -/
  mul_neg : ∀ x y : α, x * -y = -(x * y)

section Mul

variable [Mul α] [HasDistribNeg α]

@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _

@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _

theorem neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
  (neg_mul _ _).symm

theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
  (mul_neg _ _).symm

end Mul

end HasDistribNeg



section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α where
  neg := Neg.neg
  neg_neg := neg_neg
  neg_mul a b := eq_neg_of_add_eq_zero_left <| by rw [← right_distrib, add_left_neg, zero_mul]
  mul_neg a b := eq_neg_of_add_eq_zero_left <| by rw [← left_distrib, add_left_neg, mul_zero]

theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simp only [sub_eq_add_neg, neg_mul_eq_mul_neg]
  exact mul_add a b (-c)

alias mul_sub_left_distrib ← mul_sub

theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simp only [sub_eq_add_neg, neg_mul_eq_neg_mul]
  exact add_mul a (-b) c

alias mul_sub_right_distrib ← sub_mul

end NonUnitalNonAssocRing


section Ring

variable [Ring α] {a b c d e : α}

-- A (unital, associative) ring is a not-necessarily-unital ring
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonUnitalRing : NonUnitalRing α where
  __ := ‹Ring α›
  zero_mul := fun a => add_left_cancel (a := 0 * a) <| by rw [← add_mul, zero_add, add_zero]
  mul_zero := fun a => add_left_cancel (a := a * 0) <| by rw [← mul_add, add_zero, add_zero]

end Ring

class CommRing (α : Type u) extends Ring α, CommMonoid α

instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }


/-- A domain is a nontrivial semiring such multiplication by a non zero element is cancellative,
  on both sides. In other words, a nontrivial semiring `R` satisfying
  `∀ {a b c : R}, a ≠ 0 → a * b = a * c → b = c` and
  `∀ {a b c : R}, b ≠ 0 → a * b = c * b → a = c`.

  This is implemented as a mixin for `Semiring α`.
  To obtain an integral domain use `[CommRing α] [IsDomain α]`. -/
class IsDomain (α : Type u) [Semiring α] extends IsCancelMulZero α, Nontrivial α : Prop


end Mathlib.Algebra.Ring.Defs

section Mathlib.Algebra.Ring.Basic

section NoZeroDivisors

variable (α)

instance (priority := 100) NoZeroDivisors.to_isCancelMulZero [Ring α] [NoZeroDivisors α] :
    IsCancelMulZero α :=
{ mul_left_cancel_of_ne_zero := fun ha h ↦ by
    rw [← sub_eq_zero, ← mul_sub] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha)
  mul_right_cancel_of_ne_zero := fun hb h ↦ by
    rw [← sub_eq_zero, ← sub_mul] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb) }

theorem NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] :
  IsDomain α :=
{ NoZeroDivisors.to_isCancelMulZero α, h with .. }

end NoZeroDivisors

end Mathlib.Algebra.Ring.Basic

section Mathlib.Data.Int.Basic

namespace Int

instance : CommRing ℤ where
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := by rw [Int.mul_comm]; rfl
  mul_assoc := Int.mul_assoc
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : ℤ) * x = x + n * x
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul := (·*·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [ofNat_eq_coe, ofNat_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [negSucc_coe, ofNat_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast := (·)
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

end Int

end Mathlib.Data.Int.Basic

section Mathlib.Algebra.GroupWithZero.Basic

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

-- see Note [lower instance priority]
instance (priority := 10) CancelMonoidWithZero.to_noZeroDivisors : NoZeroDivisors M₀ :=
  ⟨fun ab0 => or_iff_not_imp_left.mpr <| fun ha => mul_left_cancel₀ ha <|
    ab0.trans (mul_zero _).symm⟩

end CancelMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

@[simp]
theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]

-- Porting note: used `simpa` to prove `False` in lean3
theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
  have := mul_inv_cancel h
  simp [a_eq_0] at this

@[simp]
theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]

@[simp]
theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.toCancelMonoidWithZero : CancelMonoidWithZero G₀ :=
  { (‹_› : GroupWithZero G₀) with
    mul_left_cancel_of_ne_zero := @fun x y z hx h => by
      rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z],
    mul_right_cancel_of_ne_zero := @fun x y z hy h => by
      rw [← mul_inv_cancel_right₀ hy x, h, mul_inv_cancel_right₀ hy z] }

end GroupWithZero

end Mathlib.Algebra.GroupWithZero.Basic

section Mathlib.Algebra.Ring.Regular

section IsDomain

variable [CommSemiring α] [IsDomain α]

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelCommMonoidWithZero : CancelCommMonoidWithZero α :=
  { mul_left_cancel_of_ne_zero := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero }

end IsDomain

end Mathlib.Algebra.Ring.Regular

section Mathlib.Data.Init.Rat

@[inherit_doc] notation "ℚ" => Rat

end Mathlib.Data.Init.Rat

section Mathlib.Algebra.Field.Defs

open Function

universe u

variable {α β K : Type _}

/-- The default definition of the coercion `(↑(a : ℚ) : K)` for a division ring `K`
is defined as `(a / b : K) = (a : K) * (b : K)⁻¹`.
Use `coe` instead of `Rat.castRec` for better definitional behaviour.
-/
def Rat.castRec [NatCast K] [IntCast K] [Mul K] [Inv K] : ℚ → K
  | ⟨a, b, _, _⟩ => ↑a * (↑b)⁻¹

/-- The default definition of the scalar multiplication `(a : ℚ) • (x : K)` for a division ring `K`
is given by `a • x = (↑ a) * x`.
Use `(a : ℚ) • (x : K)` instead of `qsmulRec` for better definitional behaviour.
-/
def qsmulRec (coe : ℚ → K) [Mul K] (a : ℚ) (x : K) : K :=
  coe a * x

/-- A `DivisionSemiring` is a `Semiring` with multiplicative inverses for nonzero elements. -/
class DivisionSemiring (α : Type _) extends Semiring α, GroupWithZero α

class DivisionRing (K : Type u) extends Ring K, DivInvMonoid K, Nontrivial K, RatCast K where
  /-- For a nonzero `a`, `a⁻¹` is a right multiplicative inverse. -/
  protected mul_inv_cancel : ∀ (a : K), a ≠ 0 → a * a⁻¹ = 1
  /-- We define the inverse of `0` to be `0`. -/
  protected inv_zero : (0 : K)⁻¹ = 0
  protected ratCast := Rat.castRec
  /-- However `ratCast` is defined, propositionally it must be equal to `a * b⁻¹`. -/
  protected ratCast_mk : ∀ (a : ℤ) (b : ℕ) (h1 h2), Rat.cast ⟨a, b, h1, h2⟩ = a * (b : K)⁻¹ := by
    intros
    rfl
  /-- Multiplication by a rational number. -/
  protected qsmul : ℚ → K → K := qsmulRec Rat.cast
  /-- However `qsmul` is defined,
  propositionally it must be equal to multiplication by `ratCast`. -/
  protected qsmul_eq_mul' : ∀ (a : ℚ) (x : K), qsmul a x = Rat.cast a * x := by
    intros
    rfl

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing α] : DivisionSemiring α :=
  { ‹DivisionRing α›, (inferInstance : Semiring α) with }

/-- A `Semifield` is a `CommSemiring` with multiplicative inverses for nonzero elements. -/
class Semifield (α : Type _) extends CommSemiring α, DivisionSemiring α, CommGroupWithZero α

class Field (K : Type u) extends CommRing K, DivisionRing K

section Field

variable [Field K]

-- see Note [lower instance priority]
instance (priority := 100) Field.toSemifield : Semifield K :=
  { ‹Field K›, (inferInstance : Semiring K) with }

end Field

end Mathlib.Algebra.Field.Defs

section Mathlib.Algebra.Field.Basic

section DivisionRing

variable [DivisionRing K] {a b c d : K}

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.isDomain : IsDomain K :=
  NoZeroDivisors.to_isDomain _

end DivisionRing

variable [Field K]

-- see Note [lower instance priority]
instance (priority := 100) Field.isDomain : IsDomain K :=
  { DivisionRing.isDomain with }

end Mathlib.Algebra.Field.Basic


-- The example:

#synth Zero ℤ -- works fine

set_option synthInstance.etaExperiment true in
#synth Zero ℤ -- but times out under `etaExperiment`.

set_option synthInstance.etaExperiment true in
set_option synthInstance.maxHeartbeats 60000 in -- usual limit is 20000
#synth Zero ℤ -- still works with a higher timelimit.
