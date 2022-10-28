/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Std.Classes.SetNotation
import Std.Tactic.Lint.Basic
import Mathlib.Data.Option.Defs
import Mathlib.Logic.Basic
import Mathlib.Logic.Nonempty
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Function
import Mathlib.Init.Set
import Mathlib.Tactic.Set

universe u v w

namespace Function

section
variable {α β γ : Sort _} {f : α → β}

/-- Evaluate a function at an argument. Useful if you want to talk about the partially applied
  `Function.eval x : (∀ x, β x) → β x`. -/
@[reducible, simp] def eval {β : α → Sort _} (x : α) (f : ∀ x, β x) : β x := f x

lemma const_def {y : β} : (λ _x : α => y) = const α y := rfl

@[simp] lemma const_comp {f : α → β} {c : γ} : const β c ∘ f = const α c := rfl

@[simp] lemma comp_const {f : β → γ} {b : β} : f ∘ const α b = const α (f b) := rfl

lemma id_def : @id α = λ x => x := rfl

lemma hfunext {α α': Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀a, β a} {f' : ∀a, β' a}
  (hα : α = α') (h : ∀a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  subst hα
  have : ∀a, HEq (f a) (f' a) := λ a => h a a (HEq.refl a)
  have : β = β' := by funext a
                      exact type_eq_of_heq (this a)
  subst this
  apply heq_of_eq
  funext a
  exact eq_of_heq (this a)

lemma funext_iff {β : α → Sort _} {f₁ f₂ : ∀ (x : α), β x} : f₁ = f₂ ↔ (∀a, f₁ a = f₂ a) :=
Iff.intro (λ h _ => h ▸ rfl) funext

protected lemma Bijective.injective {f : α → β} (hf : Bijective f) : Injective f := hf.1
protected lemma Bijective.surjective {f : α → β} (hf : Bijective f) : Surjective f := hf.2

theorem Injective.eq_iff (I : Injective f) {a b : α} :
  f a = f b ↔ a = b :=
⟨@I _ _, congr_arg f⟩

theorem Injective.eq_iff' (I : Injective f) {a b : α} {c : β} (h : f b = c) :
  f a = c ↔ a = b :=
h ▸ I.eq_iff

lemma Injective.ne (hf : Injective f) {a₁ a₂ : α} : a₁ ≠ a₂ → f a₁ ≠ f a₂ :=
mt (λ h => hf h)

lemma Injective.ne_iff (hf : Injective f) {x y : α} : f x ≠ f y ↔ x ≠ y :=
⟨mt $ congr_arg f, hf.ne⟩

lemma Injective.ne_iff' (hf : Injective f) {x y : α} {z : β} (h : f y = z) :
  f x ≠ z ↔ x ≠ y :=
h ▸ hf.ne_iff

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
def Injective.decidable_eq [DecidableEq β] (I : Injective f) : DecidableEq α :=
λ _ _ => decidable_of_iff _ I.eq_iff

lemma Injective.of_comp {g : γ → α} (I : Injective (f ∘ g)) : Injective g :=
λ {x y} h => I $ show f (g x) = f (g y) from congr_arg f h

lemma Injective.of_comp_iff {f : α → β} (hf : Injective f) (g : γ → α) :
  Injective (f ∘ g) ↔ Injective g :=
⟨Injective.of_comp, hf.comp⟩

lemma Injective.of_comp_iff' (f : α → β) {g : γ → α} (hg : Bijective g) :
  Injective (f ∘ g) ↔ Injective f :=
⟨ λ h x y => let ⟨_, hx⟩ := hg.surjective x
             let ⟨_, hy⟩ := hg.surjective y
             hx ▸ hy ▸ λ hf => h hf ▸ rfl,
  λ h => h.comp hg.injective⟩

lemma injective_of_subsingleton [Subsingleton α] (f : α → β) :
  Injective f :=
λ _ _ _ => Subsingleton.elim _ _

lemma Injective.dite (p : α → Prop) [DecidablePred p]
  {f : {a : α // p a} → β} {f' : {a : α // ¬ p a} → β}
  (hf : Injective f) (hf' : Injective f')
  (im_disj : ∀ {x x' : α} {hx : p x} {hx' : ¬ p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) :
  Function.Injective (λ x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) :=
by intros x₁ x₂ h
   dsimp only at h
   by_cases h₁ : p x₁ <;> by_cases h₂ : p x₂
   · rw [dif_pos h₁, dif_pos h₂] at h; injection (hf h); assumption
   · rw [dif_pos h₁, dif_neg h₂] at h; exact (im_disj h).elim
   · rw [dif_neg h₁, dif_pos h₂] at h; exact (im_disj h.symm).elim
   · rw [dif_neg h₁, dif_neg h₂] at h; injection (hf' h); assumption

lemma Surjective.of_comp {g : γ → α} (S : Surjective (f ∘ g)) : Surjective f :=
λ y => let ⟨x, h⟩ := S y
       ⟨g x, h⟩

lemma Surjective.of_comp_iff (f : α → β) {g : γ → α} (hg : Surjective g) :
  Surjective (f ∘ g) ↔ Surjective f :=
⟨Surjective.of_comp, λ h => h.comp hg⟩

lemma Surjective.of_comp_iff' {f : α → β} (hf : Bijective f) (g : γ → α) :
  Surjective (f ∘ g) ↔ Surjective g :=
⟨λ h x => let ⟨x', hx'⟩ := h (f x)
          ⟨x', hf.injective hx'⟩, hf.surjective.comp⟩

instance decidable_eq_pfun (p : Prop) [Decidable p] (α : p → Type _)
  [∀ hp, DecidableEq (α hp)] : DecidableEq (∀hp, α hp)
| f, g => decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm

theorem Surjective.forall {f : α → β} (hf : Surjective f) {p : β → Prop} :
  (∀ y, p y) ↔ ∀ x, p (f x) :=
⟨λ h x => h (f x),
 λ h y => let ⟨x, hx⟩ := hf y
          hx ▸ h x⟩

theorem Surjective.forall₂ {f : α → β} (hf : Surjective f) {p : β → β → Prop} :
  (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=
hf.forall.trans $ forall_congr' fun _ => hf.forall

theorem Surjective.forall₃ {f : α → β} (hf : Surjective f) {p : β → β → β → Prop} :
  (∀ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∀ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.forall.trans $ forall_congr' fun _ => hf.forall₂

theorem Surjective.exists {f : α → β} (hf : Surjective f) {p : β → Prop} :
  (∃ y, p y) ↔ ∃ x, p (f x) :=
⟨fun ⟨y, hy⟩ => let ⟨x, hx⟩ := hf y; ⟨x, hx.symm ▸ hy⟩,
 fun ⟨x, hx⟩ => ⟨f x, hx⟩⟩

theorem Surjective.exists₂ {f : α → β} (hf : Surjective f) {p : β → β → Prop} :
  (∃ y₁ y₂, p y₁ y₂) ↔ ∃ x₁ x₂, p (f x₁) (f x₂) :=
hf.exists.trans $ exists_congr fun _ => hf.exists

theorem Surjective.exists₃ {f : α → β} (hf : Surjective f) {p : β → β → β → Prop} :
  (∃ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∃ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.exists.trans $ exists_congr fun _ => hf.exists₂

lemma bijective_iff_exists_unique (f : α → β) : Bijective f ↔
  ∀ b : β, ∃! (a : α), f a = b :=
⟨ fun hf b => let ⟨a, ha⟩ := hf.surjective b
              ⟨a, ha, fun _ ha' => hf.injective (ha'.trans ha.symm)⟩,
  fun he => ⟨fun {_a a'} h => (he (f a')).unique h rfl, fun b => (he b).exists⟩⟩

/-- Shorthand for using projection notation with `function.bijective_iff_exists_unique`. -/
lemma Bijective.exists_unique {f : α → β} (hf : Bijective f) (b : β) : ∃! (a : α), f a = b :=
(bijective_iff_exists_unique f).mp hf b

lemma Bijective.of_comp_iff (f : α → β) {g : γ → α} (hg : Bijective g) :
  Bijective (f ∘ g) ↔ Bijective f :=
and_congr (Injective.of_comp_iff' _ hg) (Surjective.of_comp_iff _ hg.surjective)

lemma Bijective.of_comp_iff' {f : α → β} (hf : Bijective f) (g : γ → α) :
  Bijective (f ∘ g) ↔ Bijective g :=
and_congr (Injective.of_comp_iff hf.injective _) (Surjective.of_comp_iff' hf _)

/-- Cantor's diagonal argument implies that there are no surjective functions from `α`
to `Set α`. -/
theorem cantor_surjective {α} (f : α → Set α) : ¬ Surjective f
| h => let ⟨D, e⟩ := h (λ a => ¬ f a a)
       (@iff_not_self (f D D)) $ iff_of_eq (congr_fun e D)

/-- Cantor's diagonal argument implies that there are no injective functions from `Set α` to `α`. -/
theorem cantor_injective {α : Type _} (f : (Set α) → α) :
  ¬ Injective f
| i => cantor_surjective (λ a b => ∀ U, a = f U → U b) $
       RightInverse.surjective
         (λ U => funext $ λ _a => propext ⟨λ h => h U rfl, λ h' _U e => i e ▸ h'⟩)

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
def is_partial_inv {α β} (f : α → β) (g : β → Option α) : Prop :=
∀ x y, g y = some x ↔ f x = y

theorem is_partial_inv_left {α β} {f : α → β} {g} (H : is_partial_inv f g) (x) : g (f x) = some x :=
(H _ _).2 rfl

theorem injective_of_partial_inv {α β} {f : α → β} {g} (H : is_partial_inv f g) : Injective f :=
λ _ _ h => Option.some.inj $ ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

theorem injective_of_partial_inv_right {α β} {f : α → β} {g} (H : is_partial_inv f g)
 (x y b) (h₁ : b ∈ g x) (h₂ : b ∈ g y) : x = y :=
((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

theorem LeftInverse.comp_eq_id {f : α → β} {g : β → α} (h : LeftInverse f g) : f ∘ g = id :=
funext h

theorem LeftInverse_iff_comp {f : α → β} {g : β → α} : LeftInverse f g ↔ f ∘ g = id :=
⟨LeftInverse.comp_eq_id, congr_fun⟩

theorem RightInverse.comp_eq_id {f : α → β} {g : β → α} (h : RightInverse f g) : g ∘ f = id :=
funext h

theorem RightInverse_iff_comp {f : α → β} {g : β → α} : RightInverse f g ↔ g ∘ f = id :=
⟨RightInverse.comp_eq_id, congr_fun⟩

theorem LeftInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : LeftInverse f g) (hh : LeftInverse h i) : LeftInverse (h ∘ f) (g ∘ i) :=
λ a => show h (f (g (i a))) = a by rw [hf (i a), hh a]

theorem RightInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : RightInverse f g) (hh : RightInverse h i) : RightInverse (h ∘ f) (g ∘ i) :=
LeftInverse.comp hh hf

theorem LeftInverse.RightInverse {f : α → β} {g : β → α} (h : LeftInverse g f) :
  RightInverse f g := h

theorem RightInverse.LeftInverse {f : α → β} {g : β → α} (h : RightInverse g f) :
  LeftInverse f g := h

theorem LeftInverse.surjective {f : α → β} {g : β → α} (h : LeftInverse f g) :
  Surjective f :=
h.RightInverse.surjective

theorem RightInverse.injective {f : α → β} {g : β → α} (h : RightInverse f g) :
  Injective f :=
h.LeftInverse.injective

theorem LeftInverse.eq_RightInverse {f : α → β} {g₁ g₂ : β → α} (h₁ : LeftInverse g₁ f)
  (h₂ : Function.RightInverse g₂ f) :
  g₁ = g₂ := by
  have h₃ : g₁ = g₁ ∘ f ∘ g₂ := by rw [h₂.comp_eq_id, comp.right_id]
  have h₄ : g₁ ∘ f ∘ g₂ = g₂ := by rw [← comp.assoc, h₁.comp_eq_id, comp.left_id]
  rwa [←h₄]

attribute [local instance] Classical.propDecidable

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
noncomputable def partial_inv {α β} (f : α → β) (b : β) : Option α :=
if h : ∃ a, f a = b then some (Classical.choose h) else none

theorem partial_inv_of_injective {α β} {f : α → β} (I : Injective f) :
  is_partial_inv f (partial_inv f)
| a, b =>
⟨λ h => have hpi : partial_inv f b = if h : ∃ a, f a = b then some (Classical.choose h) else none :=
          rfl
        if h' : ∃ a, f a = b
        then by rw [hpi, dif_pos h'] at h
                injection h with h
                subst h
                apply Classical.choose_spec h'
        else by rw [hpi, dif_neg h'] at h; contradiction,
 λ e => e ▸ have h : ∃ a', f a' = f a := ⟨_, rfl⟩
            (dif_pos h).trans (congr_arg _ (I $ Classical.choose_spec h))⟩

theorem partial_inv_left {α β} {f : α → β} (I : Injective f) : ∀ x, partial_inv f (f x) = some x :=
is_partial_inv_left (partial_inv_of_injective I)

end

section inv_fun
variable {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} {s : Set α} {a : α} {b : β}
attribute [local instance] Classical.propDecidable

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `Function.Injective.inv_of_mem_range`. -/
noncomputable def inv_fun_on (f : α → β) (s : Set α) (b : β) : α :=
if h : ∃a, a ∈ s ∧ f a = b then Classical.choose h else Classical.choice n

theorem inv_fun_on_pos (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s ∧ f (inv_fun_on f s b) = b :=
by have h1 : inv_fun_on f s b =
     if h : ∃a, a ∈ s ∧ f a = b then Classical.choose h else Classical.choice n := rfl
   rw [dif_pos h] at h1
   rw [h1]
   exact Classical.choose_spec h

theorem inv_fun_on_mem (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s := (inv_fun_on_pos h).left

theorem inv_fun_on_eq (h : ∃a∈s, f a = b) : f (inv_fun_on f s b) = b := (inv_fun_on_pos h).right

theorem inv_fun_on_eq' (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) (ha : a ∈ s) :
  inv_fun_on f s (f a) = a :=
have : ∃a'∈s, f a' = f a := ⟨a, ha, rfl⟩
h _ (inv_fun_on_mem this) _ ha (inv_fun_on_eq this)

theorem inv_fun_on_neg (h : ¬ ∃a∈s, f a = b) : inv_fun_on f s b = Classical.choice n :=
by have h1 : inv_fun_on f s b =
     if h : ∃a, a ∈ s ∧ f a = b then Classical.choose h else Classical.choice n := rfl
   rwa [dif_neg h] at h1

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
noncomputable def inv_fun (f : α → β) : β → α := inv_fun_on f Set.univ

theorem inv_fun_eq (h : ∃a, f a = b) : f (inv_fun f b) = b :=
inv_fun_on_eq $ let ⟨a, ha⟩ := h
                ⟨a, trivial, ha⟩

lemma inv_fun_neg (h : ¬ ∃ a, f a = b) : inv_fun f b = Classical.choice n :=
by refine inv_fun_on_neg (mt ?_ h); exact λ ⟨a, _, ha⟩ => ⟨a, ha⟩

theorem inv_fun_eq_of_injective_of_RightInverse {g : β → α}
  (hf : Injective f) (hg : RightInverse g f) : inv_fun f = g :=
funext $ λ b => hf (by rw [hg b]
                       exact inv_fun_eq ⟨g b, hg b⟩)

lemma RightInverse_inv_fun (hf : Surjective f) : RightInverse (inv_fun f) f :=
λ b => inv_fun_eq $ hf b

lemma LeftInverse_inv_fun (hf : Injective f) : LeftInverse (inv_fun f) f :=
λ b => have : f (inv_fun f (f b)) = f b := inv_fun_eq ⟨b, rfl⟩
       hf this

lemma inv_fun_surjective (hf : Injective f) : Surjective (inv_fun f) :=
(LeftInverse_inv_fun hf).surjective

lemma inv_fun_comp (hf : Injective f) : inv_fun f ∘ f = id := funext $ LeftInverse_inv_fun hf

end inv_fun

section inv_fun
variable {α : Type u} [i : Nonempty α] {β : Sort v} {f : α → β}

lemma Injective.has_LeftInverse (hf : Injective f) : has_LeftInverse f :=
⟨inv_fun f, LeftInverse_inv_fun hf⟩

lemma injective_iff_has_LeftInverse : Injective f ↔ has_LeftInverse f :=
⟨Injective.has_LeftInverse, has_LeftInverse.injective⟩

end inv_fun

section surj_inv
variable {α : Sort u} {β : Sort v} {f : α → β}

/-- The inverse of a surjective function. (Unlike `inv_fun`, this does not require
  `α` to be inhabited.) -/
noncomputable def surj_inv {f : α → β} (h : Surjective f) (b : β) : α := Classical.choose (h b)

lemma surj_inv_eq (h : Surjective f) (b) : f (surj_inv h b) = b := Classical.choose_spec (h b)

lemma RightInverse_surj_inv (hf : Surjective f) : RightInverse (surj_inv hf) f :=
surj_inv_eq hf

lemma LeftInverse_surj_inv (hf : Bijective f) : LeftInverse (surj_inv hf.2) f :=
RightInverse_of_injective_of_LeftInverse hf.1 (RightInverse_surj_inv hf.2)

lemma Surjective.has_RightInverse (hf : Surjective f) : has_RightInverse f :=
⟨_, RightInverse_surj_inv hf⟩

lemma surjective_iff_has_RightInverse : Surjective f ↔ has_RightInverse f :=
⟨Surjective.has_RightInverse, has_RightInverse.surjective⟩

lemma bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f :=
⟨λ hf =>  ⟨_, LeftInverse_surj_inv hf, RightInverse_surj_inv hf.2⟩,
 λ ⟨_, gl, gr⟩ => ⟨gl.injective,  gr.surjective⟩⟩

lemma injective_surj_inv (h : Surjective f) : Injective (surj_inv h) :=
(RightInverse_surj_inv h).injective

lemma surjective_to_subsingleton [na : Nonempty α] [Subsingleton β] (f : α → β) :
  Surjective f :=
λ _ => let ⟨a⟩ := na; ⟨a, Subsingleton.elim _ _⟩

end surj_inv

section update
variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α] [DecidableEq α']

/-- Replacing the value of a function at a given point by a given value. -/
def update (f : ∀a, β a) (a' : α) (v : β a') (a : α) : β a :=
if h : a = a' then Eq.rec (motive := λ a _ => β a) v h.symm else f a

/-- On non-dependent functions, `function.update` can be expressed as an `ite` -/
lemma update_apply {β : Sort _} (f : α → β) (a' : α) (b : β) (a : α) :
  update f a' b a = if a = a' then b else f a :=
by have h2 : (h : a = a') → Eq.rec (motive := λ _ _ => β) b h.symm = b :=
     by intro h
        rw [eq_rec_constant]
   have h3 : (λ h : a = a' => Eq.rec (motive := λ _ _ => β) b h.symm) =
             (λ _ : a = a' =>  b) := funext h2
   let f := λ x => dite (a = a') x (λ (_: ¬ a = a') => (f a))
   exact congrArg f h3

@[simp] lemma update_same (a : α) (v : β a) (f : ∀a, β a) : update f a v a = v :=
dif_pos rfl

lemma update_injective (f : ∀a, β a) (a' : α) : Injective (update f a') :=
by intros v v' h
   have h' := congrFun h a'
   rwa [update_same, update_same] at h'

@[simp] lemma update_noteq {a a' : α} (h : a ≠ a') (v : β a') (f : ∀a, β a) :
  update f a' v a = f a :=
dif_neg h

lemma forall_update_iff (f : ∀a, β a) {a : α} {b : β a} (p : ∀a, β a → Prop) :
  (∀ x, p x (update f a b x)) ↔ p a b ∧ ∀ x, x ≠ a → p x (f x) :=
Iff.intro
  (by intro h
      have h1 := h a
      have h2 : update f a b a = b := update_same _ _ _
      rw [h2] at h1
      refine ⟨h1, ?_⟩
      intro x hx
      have h3 := update_noteq hx b f
      rw [←h3]
      exact h x)
  (by intro ⟨hp,h⟩ x
      have h1 : x = a ∨ x ≠ a := Decidable.em _
      match h1 with
      | Or.inl he => rw [he, update_same]
                     exact hp
      | Or.inr hne => have h4 := update_noteq hne b f
                      rw [h4]
                      exact h x hne)

lemma update_eq_iff {a : α} {b : β a} {f g : ∀ a, β a} :
  update f a b = g ↔ b = g a ∧ ∀ x, x ≠ a -> f x = g x :=
funext_iff.trans $ forall_update_iff _ (λ x y => y = g x)

lemma eq_update_iff {a : α} {b : β a} {f g : ∀ a, β a} :
  g = update f a b ↔ g a = b ∧ ∀ x, x ≠ a -> g x = f x :=
funext_iff.trans $ forall_update_iff _ (λ x y => g x = y)

@[simp] lemma update_eq_self (a : α) (f : ∀a, β a) : update f a (f a) = f :=
update_eq_iff.2 ⟨rfl, λ _ _ => rfl⟩

lemma update_comp_eq_of_forall_ne' {α'} (g : ∀ a, β a) {f : α' → α} {i : α} (a : β i)
  (h : ∀ x, f x ≠ i) :
  (λ j => (update g i a) (f j)) = (λ j => g (f j)) :=
funext $ λ _ => update_noteq (h _) _ _

/-- Non-dependent version of `function.update_comp_eq_of_forall_ne'` -/
lemma update_comp_eq_of_forall_ne {α β : Sort _} (g : α' → β) {f : α → α'} {i : α'} (a : β)
  (h : ∀ x, f x ≠ i) :
  (update g i a) ∘ f = g ∘ f :=
update_comp_eq_of_forall_ne' g a h

lemma update_comp_eq_of_injective' (g : ∀a, β a) {f : α' → α} (hf : Injective f)
  (i : α') (a : β (f i)) :
  (λ j => update g (f i) a (f j)) = update (λ i => g (f i)) i a :=
eq_update_iff.2 ⟨update_same _ _ _, λ _ hj => update_noteq (hf.ne hj) _ _⟩

/-- Non-dependent version of `function.update_comp_eq_of_injective'` -/
lemma update_comp_eq_of_injective {β : Sort _} (g : α' → β) {f : α → α'}
  (hf : Injective f) (i : α) (a : β) :
  (Function.update g (f i) a) ∘ f = Function.update (g ∘ f) i a :=
update_comp_eq_of_injective' g hf i a

lemma apply_update {ι : Sort _} [DecidableEq ι] {α β : ι → Sort _}
  (f : ∀i, α i → β i) (g : ∀i, α i) (i : ι) (v : α i) (j : ι) :
  f j (update g i v j) = update (λ k => f k (g k)) i (f i v) j :=
by by_cases h : j = i
   subst j; simp
   simp[h]

lemma comp_update {α' : Sort _} {β : Sort _} (f : α' → β) (g : α → α') (i : α) (v : α') :
  f ∘ (update g i v) = update (f ∘ g) i (f v) :=
funext $ apply_update _ _ _ _

theorem update_comm {α} [DecidableEq α] {β : α → Sort _}
  {a b : α} (h : a ≠ b) (v : β a) (w : β b) (f : ∀a, β a) :
  update (update f a v) b w = update (update f b w) a v :=
by funext c
   simp only [update]
   by_cases h₁ : c = b <;> by_cases h₂ : c = a
   · rw [dif_pos h₁, dif_pos h₂]
     cases h (h₂.symm.trans h₁)
   · rw [dif_pos h₁, dif_pos h₁, dif_neg h₂]
   · rw [dif_neg h₁, dif_neg h₁, dif_pos h₂]
   · rw [dif_neg h₁, dif_neg h₁, dif_neg h₂]

@[simp] theorem update_idem {α} [DecidableEq α] {β : α → Sort _}
  {a : α} (v w : β a) (f : ∀a, β a) : update (update f a v) a w = update f a w :=
by funext b
   by_cases b = a <;> simp [update, h]

end update

section extend

attribute [local instance] Classical.propDecidable

variable {α β γ : Type _} {f : α → β}

/-- `extend f g e'` extends a function `g : α → γ`
along a function `f : α → β` to a function `β → γ`,
by using the values of `g` on the range of `f`
and the values of an auxiliary function `e' : β → γ` elsewhere.

Mostly useful when `f` is injective. -/
noncomputable def extend (f : α → β) (g : α → γ) (e' : β → γ) : β → γ :=
λ b => if h : ∃ a, f a = b then g (Classical.choose h) else e' b

lemma extend_def (f : α → β) (g : α → γ) (e' : β → γ) (b : β) [hd : Decidable (∃ a, f a = b)] :
  extend f g e' b = if h : ∃ a, f a = b then g (Classical.choose h) else e' b :=
  by rw [Subsingleton.elim hd] -- align the Decidable instances implicitly used by `dite`
     exact rfl

@[simp] lemma extend_apply (hf : Injective f) (g : α → γ) (e' : β → γ) (a : α) :
  extend f g e' (f a) = g a :=
by simp only [extend_def, dif_pos, exists_apply_eq_apply]
   exact congr_arg g (hf $ Classical.choose_spec (exists_apply_eq_apply f a))

@[simp]
theorem extend_apply' (g : α → γ) (e' : β → γ) (b : β) (hb : ¬∃ a, f a = b) :
  extend f g e' b = e' b := by
  simp [Function.extend_def, hb]

@[simp] lemma extend_comp (hf : Injective f) (g : α → γ) (e' : β → γ) :
  extend f g e' ∘ f = g :=
funext $ λ a => extend_apply hf g e' a

end extend

lemma uncurry_def {α β γ} (f : α → β → γ) : uncurry f = (λp => f p.1 p.2) :=
rfl

@[simp] lemma uncurry_apply_pair {α β γ} (f : α → β → γ) (x : α) (y : β) :
  uncurry f (x, y) = f x y :=
rfl

@[simp] lemma curry_apply {α β γ} (f : α × β → γ) (x : α) (y : β) :
  curry f x y = f (x, y) :=
rfl

section bicomp
variable {α β γ δ ε : Type _}

/-- Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f on g`. -/
def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a b) :=
f (g a) (h b)

/-- Compose an unary function `f` with a binary function `g`. -/
def bicompr (f : γ → δ) (g : α → β → γ) (a b) :=
f (g a b)

-- Suggested local notation:
local notation f  " ∘₂ " g => bicompr f g

lemma uncurry_bicompr (f : α → β → γ) (g : γ → δ) :
  uncurry (g ∘₂ f) = (g ∘ uncurry f) := rfl

lemma uncurry_bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) :
  uncurry (bicompl f g h) = (uncurry f) ∘ (Prod.map g h) :=
by ext ⟨x, y⟩; exact rfl

end bicomp

section uncurry

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. The most generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps. -/
class HasUncurry (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  uncurry : α → (β → γ)

/- Uncurrying operator. The most generic use is to recursively uncurry. For instance
`f : α → β → γ → δ` will be turned into `↿f : α × β × γ → δ`. One can also add instances
for bundled maps. -/
notation:max "↿" x:max => HasUncurry.uncurry x

instance HasUncurry_base : HasUncurry (α → β) α β := ⟨id⟩

instance HasUncurry_induction [HasUncurry β γ δ] : HasUncurry (α → β) (α × γ) δ :=
⟨λ f p => ↿(f p.1) p.2⟩

end uncurry

/-- A function is involutive, if `f ∘ f = id`. -/
def Involutive {α} (f : α → α) : Prop := ∀ x, f (f x) = x

lemma involutive_iff_iter_2_eq_id {α} {f : α → α} : Involutive f ↔ (f^[2] = id) :=
funext_iff.symm

namespace Involutive
variable {α : Sort u} {f : α → α} (h : Involutive f)

@[simp]
lemma comp_self : f ∘ f = id := funext h

protected lemma LeftInverse : LeftInverse f f := h
protected lemma RightInverse : RightInverse f f := h

protected lemma injective : Injective f := h.LeftInverse.injective
protected lemma surjective : Surjective f := λ x => ⟨f x, h x⟩
protected lemma bijective : Bijective f := ⟨h.injective, h.surjective⟩

/-- Involuting an `ite` of an involuted value `x : α` negates the `Prop` condition in the `ite`. -/
protected lemma ite_not (P : Prop) [Decidable P] (x : α) :
  f (ite P x (f x)) = ite (¬ P) x (f x) :=
by rw [apply_ite f, h, ite_not]

/-- An involution commutes across an equality. Compare to `function.injective.eq_iff`. -/
protected lemma eq_iff {x y : α} : f x = y ↔ x = f y :=
Injective.eq_iff' (Involutive.injective h) (h y)

end Involutive

/-- The property of a binary function `f : α → β → γ` being injective.
Mathematically this should be thought of as the corresponding function `α × β → γ` being injective.
-/
@[reducible] def Injective2 {α β γ} (f : α → β → γ) : Prop :=
∀ {a₁ a₂ b₁ b₂}, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

namespace Injective2
variable {α β γ : Type _} (f : α → β → γ)

protected lemma left (hf : Injective2 f) {a₁ a₂ b₁ b₂} (h : f a₁ b₁ = f a₂ b₂) : a₁ = a₂ :=
(hf h).1

protected lemma right (hf : Injective2 f) {a₁ a₂ b₁ b₂} (h : f a₁ b₁ = f a₂ b₂) : b₁ = b₂ :=
(hf h).2

lemma eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
⟨λ h => hf h, λ⟨h1, h2⟩ => congr_arg₂ f h1 h2⟩

end Injective2

section sometimes
attribute [local instance] Classical.propDecidable

/-- `sometimes f` evaluates to some value of `f`, if it exists. This function is especially
interesting in the case where `α` is a proposition, in which case `f` is necessarily a
constant function, so that `sometimes f = f a` for all `a`. -/
noncomputable def sometimes {α β} [Nonempty β] (f : α → β) : β :=
if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›

theorem sometimes_eq {p : Prop} {α} [Nonempty α] (f : p → α) (a : p) : sometimes f = f a :=
dif_pos ⟨a⟩

theorem sometimes_spec {p : Prop} {α} [Nonempty α]
  (P : α → Prop) (f : p → α) (a : p) (h : P (f a)) : P (sometimes f) :=
by rwa [sometimes_eq]

end sometimes

-- TODO: put the following two defs at the end of
end Function

/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
def set.piecewise {α : Type u} {β : α → Sort v} (s : Set α) (f g : ∀i, β i)
  [∀j, Decidable (j ∈ s)] :
  ∀i, β i :=
λi => if i ∈ s then f i else g i

-- TODO: eq_rec_on_bijective, eq_mp_bijective, eq_mpr_bijective, cast_biject, eq_rec_inj, cast_inj

/-- A set of functions "separates points"
if for each pair of distinct points there is a function taking different values on them. -/
def set.separates_points {α β : Type _} (A : Set (α → β)) : Prop :=
∀ {x y : α}, x ≠ y → ∃ f ∈ A, (f x : β) ≠ f y

-- TODO: is_symm_op.flip_eq

namespace Function

section

variable {α β γ : Sort _} {f : α → β}

@[simp]
theorem eval_apply {β : α → Sort _} (x : α) (f : ∀ x, β x) : eval x f = f x :=
  rfl

theorem const_injective [Nonempty α] : Injective (const α : β → α → β) := fun y₁ y₂ h =>
  let ⟨x⟩ := ‹Nonempty α›
  congr_fun h x

@[simp]
theorem const_inj [Nonempty α] {y₁ y₂ : β} : const α y₁ = const α y₂ ↔ y₁ = y₂ :=
  ⟨fun h => const_injective h, fun h => h ▸ rfl⟩

theorem ne_iff {β : α → Sort _} {f₁ f₂ : ∀ a, β a} : f₁ ≠ f₂ ↔ ∃ a, f₁ a ≠ f₂ a :=
  funext_iff.not.trans not_forall

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
protected def Injective.decidableEq [DecidableEq β] (I : Injective f) : DecidableEq α := fun _ _ =>
  decidable_of_iff _ I.eq_iff

/-- Composition by an injective function on the left is itself injective. -/
theorem Injective.comp_left {g : β → γ} (hg : Function.Injective g) :
    Function.Injective ((· ∘ ·) g : (α → β) → α → γ) :=
  fun _ _ hgf => funext fun i => hg <| (congr_fun hgf i : _)

instance decidableEqPfun (p : Prop) [Decidable p] (α : p → Type _) [∀ hp, DecidableEq (α hp)] : DecidableEq (∀ hp, α hp)
  | f, g => decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm

theorem Surjective.injective_comp_right (hf : Surjective f) : Injective fun g : β → γ => g ∘ f :=
  fun _ _ h => funext <| hf.forall.2 <| congr_fun h

protected theorem Surjective.right_cancellable (hf : Surjective f) {g₁ g₂ : β → γ} :
    g₁ ∘ f = g₂ ∘ f ↔ g₁ = g₂ :=
  hf.injective_comp_right.eq_iff

theorem surjective_of_right_cancellable_Prop (h : ∀ g₁ g₂ : β → Prop, g₁ ∘ f = g₂ ∘ f → g₁ = g₂) :
    Surjective f := by
  specialize h (fun _ => True) (fun y => ∃ x, f x = y) (funext fun x => _)
  · intro y
    have : True = ∃ x, f x = y := congr_fun h y
    rw [← this]
    exact trivial
  · simp only [(· ∘ ·), exists_apply_eq_apply]

theorem Bijective.exists_unique_iff {f : α → β} (hf : Bijective f) {p : β → Prop} :
    (∃! y, p y) ↔ ∃! x, p (f x) :=
  ⟨fun ⟨y, hpy, hy⟩ =>
    let ⟨x, hx⟩ := hf.surjective y
    ⟨x, by dsimp only <;> rwa [hx], fun z (hz : p (f z)) => hf.injective <| hx.symm ▸ hy _ hz⟩,
    fun ⟨x, hpx, hx⟩ =>
    ⟨f x, hpx, fun y hy =>
      let ⟨z, hz⟩ := hf.surjective y
      hz ▸ (congr_arg f <| hx _ <| by dsimp only <;> rwa [hz])⟩⟩

/-- There is no surjection from `α : Type u` into `Type u`. This theorem
  demonstrates why `Type : Type` would be inconsistent in Lean. -/
theorem not_surjective_Type {α : Type u} (f : α → Type max u v) : ¬Surjective f := by
  intro hf
  let T : Type max u v := Sigma f
  cases' hf (Set T) with U hU
  set g : Set T → T := fun s => ⟨U, cast hU.symm s⟩ with hg'
  have hg : Injective g := by
    intro s t h
    suffices cast hU (g s).2 = cast hU (g t).2 by
      simp only [cast_cast, cast_eq] at this
      assumption
    · have := congr (f₁ := @Sigma.snd α f)
      assumption

  exact cantor_injective g hg

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
def IsPartialInv {α β} (f : α → β) (g : β → Option α) : Prop :=
  ∀ x y, g y = some x ↔ f x = y

theorem left_inverse_iff_comp {f : α → β} {g : β → α} : LeftInverse f g ↔ f ∘ g = id :=
  ⟨LeftInverse.comp_eq_id, congr_fun⟩

theorem right_inverse_iff_comp {f : α → β} {g : β → α} : RightInverse f g ↔ g ∘ f = id :=
  ⟨RightInverse.comp_eq_id, congr_fun⟩

theorem LeftInverse.right_inverse_of_injective {f : α → β} {g : β → α} (h : LeftInverse f g) (hf : Injective f) :
    RightInverse f g := fun x => hf <| h (f x)

theorem LeftInverse.right_inverse_of_surjective {f : α → β} {g : β → α} (h : LeftInverse f g) (hg : Surjective g) :
    RightInverse f g := fun x =>
  let ⟨y, hy⟩ := hg x
  hy ▸ congr_arg g (h y)

theorem RightInverse.left_inverse_of_surjective {f : α → β} {g : β → α} :
    RightInverse f g → Surjective f → LeftInverse f g :=
  left_inverse.right_inverse_of_surjective

theorem RightInverse.left_inverse_of_injective {f : α → β} {g : β → α} :
    RightInverse f g → Injective g → LeftInverse f g :=
  left_inverse.right_inverse_of_injective

theorem LeftInverse.eq_right_inverse {f : α → β} {g₁ g₂ : β → α} (h₁ : LeftInverse g₁ f) (h₂ : RightInverse g₂ f) :
    g₁ = g₂ :=
  calc
    g₁ = g₁ ∘ f ∘ g₂ := by rw [h₂.comp_eq_id, comp.right_id]
    _ = g₂ := by rw [← comp.assoc, h₁.comp_eq_id, comp.left_id]


attribute [local instance] Classical.propDecidable

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
noncomputable def partialInv {α β} (f : α → β) (b : β) : Option α :=
  if h : ∃ a, f a = b then some (Classical.choose h) else none

end

section InvFun

variable {α β : Sort _} [Nonempty α] {f : α → β} {a : α} {b : β}

attribute [local instance] Classical.propDecidable

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
noncomputable def invFun (f : α → β) : β → α :=
  fun y => if h : ∃ x, f x = y then h.choose else Classical.arbitrary α

theorem inv_fun_eq_of_injective_of_right_inverse {g : β → α} (hf : Injective f)
    (hg : RightInverse g f) : invFun f = g :=
  funext fun b => hf (by rw [hg b])

theorem right_inverse_inv_fun (hf : Surjective f) : RightInverse (invFun f) f :=
  fun b => inv_fun_eq <| hf b

theorem left_inverse_inv_fun (hf : Injective f) : LeftInverse (invFun f) f :=
  fun b => hf <| inv_fun_eq ⟨b, rfl⟩

theorem Injective.has_left_inverse (hf : Injective f) : HasLeftInverse f :=
  ⟨invFun f, left_inverse_inv_fun hf⟩

theorem injective_iff_has_left_inverse : Injective f ↔ HasLeftInverse f :=
  ⟨Injective.has_left_inverse, HasLeftInverse.injective⟩

end InvFun

section SurjInv

variable {α : Sort u} {β : Sort v} {γ : Sort w} {f : α → β}

/-- The inverse of a surjective function. (Unlike `inv_fun`, this does not require
  `α` to be inhabited.) -/
noncomputable def surjInv {f : α → β} (h : Surjective f) (b : β) : α :=
  Classical.choose (h b)

theorem right_inverse_surj_inv (hf : Surjective f) : RightInverse (surjInv hf) f :=
  surj_inv_eq hf

theorem left_inverse_surj_inv (hf : Bijective f) : LeftInverse (surjInv hf.2) f :=
  right_inverse_of_injective_of_left_inverse hf.1 (right_inverse_surj_inv hf.2)

theorem Surjective.has_right_inverse (hf : Surjective f) : HasRightInverse f :=
  ⟨_, right_inverse_surj_inv hf⟩

theorem surjective_iff_has_right_inverse : Surjective f ↔ HasRightInverse f :=
  ⟨Surjective.has_right_inverse, HasRightInverse.surjective⟩

theorem bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f :=
  ⟨fun hf => ⟨_, left_inverse_surj_inv hf, right_inverse_surj_inv hf.2⟩, fun ⟨g, gl, gr⟩ =>
    ⟨gl.Injective, gr.Surjective⟩⟩

theorem injective_surj_inv (h : Surjective f) : Injective (surjInv h) :=
  (right_inverse_surj_inv h).Injective

theorem surjective_to_subsingleton [na : Nonempty α] [Subsingleton β] (f : α → β) : Surjective f := fun y =>
  let ⟨a⟩ := na
  ⟨a, Subsingleton.elim _ _⟩

/-- Composition by an surjective function on the left is itself surjective. -/
theorem Surjective.comp_left {g : β → γ} (hg : Surjective g) : Surjective ((· ∘ ·) g : (α → β) → α → γ) := fun f =>
  ⟨surjInv hg ∘ f, funext fun x => right_inverse_surj_inv _ _⟩

/-- Composition by an bijective function on the left is itself bijective. -/
theorem Bijective.comp_left {g : β → γ} (hg : Bijective g) : Bijective ((· ∘ ·) g : (α → β) → α → γ) :=
  ⟨hg.Injective.compLeft, hg.Surjective.compLeft⟩

end SurjInv

section Update

variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α] [DecidableEq α']

/- warning: function.update_apply -> Function.update_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u}} [_inst_1 : DecidableEq.{u} α] {β : Sort.{u_1}} (f : α -> β) (a' : α) (b : β) (a : α), Eq.{u_1} β (Function.update.{u u_1} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_1 a b) f a' b a) (ite.{u_1} β (Eq.{u} α a a') (_inst_1 a a') b (f a))
but is expected to have type
  forall {α : Sort.{u}} [inst._@.Mathlib.Logic.Function.Basic._hyg.4838 : DecidableEq.{u} α] {β : Sort.{u_1}} (f : α -> β) (a' : α) (b : β) (a : α), Eq.{u_1} β (Function.update.{u u_1} α (fun (a : α) => β) (fun (a : α) (b : α) => inst._@.Mathlib.Logic.Function.Basic._hyg.4838 a b) f a' b a) (ite.{u_1} β (Eq.{u} α a a') (inst._@.Mathlib.Logic.Function.Basic._hyg.4838 a a') b (f a))
Case conversion may be inaccurate. Consider using '#align function.update_apply Function.update_applyₓ'. -/
/-- On non-dependent functions, `function.update` can be expressed as an `ite` -/
theorem update_apply {β : Sort _} (f : α → β) (a' : α) (b : β) (a : α) : update f a' b a = if a = a' then b else f a :=
  by
  dsimp only [update]
  congr
  funext
  rw [eq_rec_constant]

@[simp]
theorem update_same (a : α) (v : β a) (f : ∀ a, β a) : update f a v a = v :=
  dif_pos rfl

theorem surjective_eval {α : Sort u} {β : α → Sort v} [h : ∀ a, Nonempty (β a)] (a : α) :
    Surjective (eval a : (∀ a, β a) → β a) := fun b =>
  ⟨@update _ _ (Classical.decEq α) (fun a => (h a).some) a b, @update_same _ _ (Classical.decEq α) _ _ _⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x «expr ≠ » a) -/
theorem exists_update_iff (f : ∀ a, β a) {a : α} {b : β a} (p : ∀ a, β a → Prop) :
    (∃ x, p x (update f a b x)) ↔ p a b ∨ ∃ (x : _)(_ : x ≠ a), p x (f x) := by
  rw [← not_forall_not, forall_update_iff f fun a b => ¬p a b]
  simp [not_and_distrib]

theorem apply_update₂ {ι : Sort _} [DecidableEq ι] {α β γ : ι → Sort _} (f : ∀ i, α i → β i → γ i) (g : ∀ i, α i)
    (h : ∀ i, β i) (i : ι) (v : α i) (w : β i) (j : ι) :
    f j (update g i v j) (update h i w j) = update (fun k => f k (g k) (h k)) i (f i v w) j := by
  by_cases h:j = i
  · subst j
    simp

  · simp [h]

end Update

noncomputable section Extend

attribute [local instance] Classical.propDecidable

variable {α β γ : Sort _} {f : α → β}

theorem apply_extend {δ} (hf : Injective f) (F : γ → δ) (g : α → γ) (e' : β → γ) (b : β) :
    F (extend f g e' b) = extend f (F ∘ g) (F ∘ e') b := by
  by_cases hb:∃ a, f a = b
  · cases' hb with a ha
    subst b
    rw [extend_apply hf, extend_apply hf]
    rfl
  · rw [extend_apply' _ _ _ hb, extend_apply' _ _ _ hb]
    rfl

theorem extend_injective (hf : Injective f) (e' : β → γ) : Injective fun g => extend f g e' := by
  intro g₁ g₂ hg
  refine' funext fun x => _
  have H := congr_fun hg (f x)
  simp only [hf, extend_apply] at H
  exact H

theorem Injective.surjective_comp_right' (hf : Injective f) (g₀ : β → γ) : Surjective fun g : β → γ => g ∘ f := fun g =>
  ⟨extend f g g₀, extend_comp hf _ _⟩

theorem Injective.surjective_comp_right [Nonempty γ] (hf : Injective f) : Surjective fun g : β → γ => g ∘ f :=
  hf.surjective_comp_right' fun _ => Classical.choice ‹_›

theorem Bijective.comp_right (hf : Bijective f) : Bijective fun g : β → γ => g ∘ f :=
  ⟨hf.surjective.injective_comp_right, fun g =>
    ⟨g ∘ surjInv hf.surjective,
      by simp only [comp.assoc g _ f, (left_inverse_surj_inv hf).comp_eq_id, comp.right_id]⟩⟩

end Extend

section Bicomp

variable {α β γ δ ε : Type _}

-- mathport name: «expr ∘₂ »
-- Suggested local notation:
local notation f " ∘₂ " g => bicompr f g

end Bicomp

section Uncurry

variable {α β γ δ : Type _}

/-- Uncurrying operator. The most generic use is to recursively uncurry. For instance
`f : α → β → γ → δ` will be turned into `↿f : α × β × γ → δ`. One can also add instances
for bundled maps.-/
add_decl_doc HasUncurry.uncurry

-- mathport name: uncurry
notation:arg "↿" x:arg => HasUncurry.uncurry x

instance hasUncurryBase : HasUncurry (α → β) α β :=
  ⟨id⟩

instance hasUncurryInduction [HasUncurry β γ δ] : HasUncurry (α → β) (α × γ) δ :=
  ⟨fun f p => (↿(f p.1)) p.2⟩

end Uncurry

/-- A function is involutive, if `f ∘ f = id`. -/
def Involutive {α} (f : α → α) : Prop :=
  ∀ x, f (f x) = x

theorem involutive_iff_iter_2_eq_id {α} {f : α → α} : Involutive f ↔ f^[2] = id :=
  funext_iff.symm

theorem _root_.bool.involutive_bnot : Involutive not :=
  bnot_bnot

namespace Involutive

variable {α : Sort u} {f : α → α} (h : Involutive f)

include h

@[simp]
theorem comp_self : f ∘ f = id :=
  funext h

protected theorem left_inverse : LeftInverse f f :=
  h

protected theorem right_inverse : RightInverse f f :=
  h

protected theorem injective : Injective f :=
  h.LeftInverse.Injective

protected theorem surjective : Surjective f := fun x => ⟨f x, h x⟩

protected theorem bijective : Bijective f :=
  ⟨h.Injective, h.Surjective⟩

/-- Involuting an `ite` of an involuted value `x : α` negates the `Prop` condition in the `ite`. -/
protected theorem ite_not (P : Prop) [Decidable P] (x : α) : f (ite P x (f x)) = ite (¬P) x (f x) := by
  rw [apply_ite f, h, ite_not]

/-- An involution commutes across an equality. Compare to `function.injective.eq_iff`. -/
protected theorem eq_iff {x y : α} : f x = y ↔ x = f y :=
  h.Injective.eq_iff' (h y)

end Involutive

/-- The property of a binary function `f : α → β → γ` being injective.
Mathematically this should be thought of as the corresponding function `α × β → γ` being injective.
-/
def Injective2 {α β γ} (f : α → β → γ) : Prop :=
  ∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

namespace Injective2

variable {α β γ : Sort _} {f : α → β → γ}

/-- A binary injective function is injective when only the left argument varies. -/
protected theorem left (hf : Injective2 f) (b : β) : Function.Injective fun a => f a b := fun a₁ a₂ h => (hf h).left

/-- A binary injective function is injective when only the right argument varies. -/
protected theorem right (hf : Injective2 f) (a : α) : Function.Injective (f a) := fun a₁ a₂ h => (hf h).right

protected theorem uncurry {α β γ : Type _} {f : α → β → γ} (hf : Injective2 f) : Function.Injective (uncurry f) :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h => And.elim (hf h) (congr_arg2 _)

/-- As a map from the left argument to a unary function, `f` is injective. -/
theorem left' (hf : Injective2 f) [Nonempty β] : Function.Injective f := fun a₁ a₂ h =>
  let ⟨b⟩ := ‹Nonempty β›
  hf.left b <| (congr_fun h b : _)

/-- As a map from the right argument to a unary function, `f` is injective. -/
theorem right' (hf : Injective2 f) [Nonempty α] : Function.Injective fun b a => f a b := fun b₁ b₂ h =>
  let ⟨a⟩ := ‹Nonempty α›
  hf.right a <| (congr_fun h a : _)

theorem eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun h => hf h, And.ndrec <| congr_arg2 f⟩

end Injective2

section Sometimes

attribute [local instance] Classical.propDecidable

/-- `sometimes f` evaluates to some value of `f`, if it exists. This function is especially
interesting in the case where `α` is a proposition, in which case `f` is necessarily a
constant function, so that `sometimes f = f a` for all `a`. -/
noncomputable def sometimes {α β} [Nonempty β] (f : α → β) : β :=
  if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›

theorem sometimes_eq {p : Prop} {α} [Nonempty α] (f : p → α) (a : p) : sometimes f = f a :=
  dif_pos ⟨a⟩

theorem sometimes_spec {p : Prop} {α} [Nonempty α] (P : α → Prop) (f : p → α) (a : p) (h : P (f a)) : P (sometimes f) :=
  by rwa [sometimes_eq]

end Sometimes

end Function

/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
def Set.piecewise {α : Type u} {β : α → Sort v} (s : Set α) (f g : ∀ i, β i) [∀ j, Decidable (j ∈ s)] : ∀ i, β i :=
  fun i => if i ∈ s then f i else g i

/-! ### Bijectivity of `eq.rec`, `eq.mp`, `eq.mpr`, and `cast` -/


theorem eq_rec_on_bijective {α : Sort _} {C : α → Sort _} :
    ∀ {a a' : α} (h : a = a'), Function.Bijective (@Eq.recOn _ _ C _ h)
  | _, _, rfl => ⟨fun x y => id, fun x => ⟨x, rfl⟩⟩

theorem eq_mp_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mp h) :=
  eq_rec_on_bijective h

theorem eq_mpr_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mpr h) :=
  eq_rec_on_bijective h.symm

theorem cast_bijective {α β : Sort _} (h : α = β) : Function.Bijective (cast h) :=
  eq_rec_on_bijective h

/-! Note these lemmas apply to `Type*` not `Sort*`, as the latter interferes with `simp`, and
is trivial anyway.-/


@[simp]
theorem eq_rec_inj {α : Sort _} {a a' : α} (h : a = a') {C : α → Type _} (x y : C a) :
    (Eq.ndrec x h : C a') = Eq.ndrec y h ↔ x = y :=
  (eq_rec_on_bijective h).Injective.eq_iff

@[simp]
theorem cast_inj {α β : Type _} (h : α = β) {x y : α} : cast h x = cast h y ↔ x = y :=
  (cast_bijective h).Injective.eq_iff

theorem Function.LeftInverse.eq_rec_eq {α β : Sort _} {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) : (congr_arg f (h a)).rec (C (g (f a))) = C a :=
  eq_of_heq <| (eq_rec_heq _ _).trans <| by rw [h]

theorem Function.LeftInverse.eq_rec_on_eq {α β : Sort _} {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) : (congr_arg f (h a)).recOn (C (g (f a))) = C a :=
  h.eq_rec_eq _ _

theorem Function.LeftInverse.cast_eq {α β : Sort _} {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    cast (congr_arg (fun a => γ (f a)) (h a)) (C (g (f a))) = C a :=
  eq_of_heq <| (eq_rec_heq _ _).trans <| by rw [h]

/-- A set of functions "separates points"
if for each pair of distinct points there is a function taking different values on them. -/
def Set.SeparatesPoints {α β : Type _} (A : Set (α → β)) : Prop :=
  ∀ ⦃x y : α⦄, x ≠ y → ∃ f ∈ A, (f x : β) ≠ f y

theorem IsSymmOp.flip_eq {α β} (op) [IsSymmOp α β op] : flip op = op :=
  funext fun a => funext fun b => (IsSymmOp.symm_op a b).symm

theorem InvImage.equivalence {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β) (h : Equivalence r) :
    Equivalence (InvImage r f) :=
  ⟨fun _ => h.1 _, fun _ _ x => h.2.1 x, InvImage.trans r f h.2.2⟩
