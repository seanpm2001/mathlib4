import Mathlib.Algebra.Algebra.NonUnitalSubalgebra.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# Relating unital and non-unital substructures

This file takes unital and non-unital structures and relates them.

## Main declarations

* `non_unital_subalgebra.unitization s : unitization R s →ₐ[R] algebra.adjoin R (s : set A)`:
  where `s` is a non-unital subalgebra of a unital `R`-algebra `A`, this is the natural algebra
  homomorphism sending `(r, a)` to `r • 1 + a`. This is always surjective.#check
* `non_unital_subalgebra.unitization_equiv s : unitization R s ≃ₐ[R] algebra.adjoin R (s : set A)`:
  when `R` is a field and `1 ∉ s`, the above homomorphism is injective is upgraded to
  an `alg_equiv`.
* `subsemiring.closure_equiv_adjoin_nat : subsemiring.closure s ≃ₐ[ℕ] algebra.adjoin ℕ s`: the
  identity map between these subsemirings, viewed as `ℕ`-algebras.
* `subring.closure_equiv_adjoin_int : subring.closure s ≃ₐ[ℤ] algebra.adjoin ℤ s`: the
  identity map between these subsemirings, viewed as `ℤ`-algebras.
* `non_unital_subsemiring.unitization : unitization ℕ S →ₐ[ℕ] subsemiring.closure (S : set R)`:
  the natural `ℕ`-algebra homomorphism between the unitization of a non-unital subsemiring `S` and
  its `subsemiring.closure`. This is just `non_unital_subalgebra.unitization S` where we replace the
  codomain using `subsemiring.closure_equiv_adjoint_nat`
* `non_unital_subring.unitization : unitization ℤ S →ₐ[ℤ] subring.closure (S : set R)`:
  the natural `ℤ`-algebra homomorphism between the unitization of a non-unital subring `S` and
  its `subring.closure`. This is just `non_unital_subalgebra.unitization S` where we replace the
  codomain using `subring.closure_equiv_adjoint_int`

-/


namespace Subsemiring

variable {R : Type _} [NonAssocSemiring R]

@[elab_as_elim]
theorem closure_induction' {s : Set R} {p : closure s → Prop} (a : closure s)
    (Hs : ∀ (x) (h : x ∈ s), p ⟨x, subset_closure h⟩) (H0 : p 0) (H1 : p 1)
    (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y)) : p a :=
  Subtype.recOn a fun b hb =>
    by
    refine' Exists.elim _ fun (hb : b ∈ closure s) (hc : p ⟨b, hb⟩) => hc
    refine'
      closure_induction hb (fun x hx => ⟨subset_closure hx, Hs x hx⟩) ⟨zero_mem (closure s), H0⟩
        ⟨one_mem (closure s), H1⟩ _ _
    · rintro x y ⟨hx, hpx⟩ ⟨hy, hpy⟩
      exact ⟨add_mem hx hy, Hadd _ _ hpx hpy⟩
    · rintro x y ⟨hx, hpx⟩ ⟨hy, hpy⟩
      exact ⟨mul_mem hx hy, Hmul _ _ hpx hpy⟩
#align subsemiring.closure_induction' Subsemiring.closure_induction'

end Subsemiring

namespace Subring

variable {R : Type _} [Ring R]

@[elab_as_elim]
theorem closure_induction' {s : Set R} {p : closure s → Prop} (a : closure s)
    (Hs : ∀ (x) (h : x ∈ s), p ⟨x, subset_closure h⟩) (H0 : p 0) (H1 : p 1)
    (Hadd : ∀ x y, p x → p y → p (x + y)) (Hneg : ∀ x, p x → p (-x))
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p a :=
  Subtype.recOn a fun b hb =>
    by
    refine' Exists.elim _ fun (hb : b ∈ closure s) (hc : p ⟨b, hb⟩) => hc
    refine'
      closure_induction hb (fun x hx => ⟨subset_closure hx, Hs x hx⟩) ⟨zero_mem (closure s), H0⟩
        ⟨one_mem (closure s), H1⟩ _ _ _
    · rintro x y ⟨hx, hpx⟩ ⟨hy, hpy⟩
      exact ⟨add_mem hx hy, Hadd _ _ hpx hpy⟩
    · rintro x ⟨hx, hpx⟩
      exact ⟨neg_mem hx, Hneg _ hpx⟩
    · rintro x y ⟨hx, hpx⟩ ⟨hy, hpy⟩
      exact ⟨mul_mem hx hy, Hmul _ _ hpx hpy⟩
#align subring.closure_induction' Subring.closure_induction'

end Subring


section Generic

variable {R S A : Type _} [CommSemiring R] [Semiring A] [Algebra R A] [SetLike S A]
  [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A] (s : S)


instance NonUnitalSubalgebraClass.isScalarTower : IsScalarTower R s s
    where smul_assoc r x y := Subtype.ext <| smul_assoc r (x : A) (y : A)
#align non_unital_subalgebra_class.is_scalar_tower NonUnitalSubalgebraClass.isScalarTower

instance NonUnitalSubalgebraClass.sMulCommClass : SMulCommClass R s s
    where smul_comm r x y := Subtype.ext <| smul_comm r (x : A) (y : A)
#align non_unital_subalgebra_class.smul_comm_class NonUnitalSubalgebraClass.sMulCommClass

/-- The natural `R`-algebra homomorphism from the unitization of a non-unital subalgebra to
its `algebra.adjoin`. -/
def NonUnitalSubalgebra.unitization : Unitization R s →ₐ[R] Algebra.adjoin R (s : Set A) :=
  Unitization.starLift
    { toFun := fun x : s => (⟨x, Algebra.subset_adjoin x.Prop⟩ : Algebra.adjoin R (s : Set A))
      map_smul' := fun (_ : R) _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
#align non_unital_subalgebra.unitization NonUnitalSubalgebra.unitization

@[simp]
theorem NonUnitalSubalgebra.unitization_apply_coe (x : Unitization R s) :
    (NonUnitalSubalgebra.unitization s x : A) =
      algebraMap R (Algebra.adjoin R (s : Set A)) x.fst + x.snd :=
  rfl
#align non_unital_subalgebra.unitization_apply_coe NonUnitalSubalgebra.unitization_apply_coe

theorem NonUnitalSubalgebra.unitization_surjective :
    Function.Surjective (NonUnitalSubalgebra.unitization s) :=
  by
  refine' Algebra.adjoin_induction' _ _ _ _
  · refine' fun x hx => ⟨(0, ⟨x, hx⟩), Subtype.ext _⟩
    simp only [NonUnitalSubalgebra.unitization_apply_coe, Subtype.coe_mk]
    change (algebraMap R { x // x ∈ Algebra.adjoin R (s : Set A) } 0 : A) + x = x
    rw [map_zero, Subsemiring.coe_zero, zero_add]
  · exact fun r => ⟨algebraMap R (Unitization R s) r, AlgHom.commutes _ r⟩
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, map_mul _ _ _⟩
#align non_unital_subalgebra.unitization_surjective NonUnitalSubalgebra.unitization_surjective

theorem NonUnitalSubalgebra.unitization_injective {R S A : Type _} [Field R] [Ring A] [Algebra R A]
    [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A] (s : S)
    (h1 : (1 : A) ∉ s) : Function.Injective (NonUnitalSubalgebra.unitization s) :=
  by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  refine' fun x hx => _
  induction' x using Unitization.ind with r a
  rw [map_add] at hx
  have hx' := congr_arg (coe : _ → A) hx
  simp only [NonUnitalSubalgebra.unitization_apply_coe, Unitization.fst_inl,
    Subalgebra.coe_algebraMap, Unitization.snd_inl, ZeroMemClass.coe_zero, add_zero, map_neg,
    AddSubgroupClass.coe_neg, Unitization.fst_inr, map_zero, Unitization.snd_inr,
    Subalgebra.coe_add, zero_add] at hx'
  by_cases hr : r = 0
  · simp only [hr, map_zero, Unitization.inl_zero, zero_add] at hx' ⊢
    rw [← ZeroMemClass.coe_zero s] at hx'
    exact congr_arg _ (Subtype.coe_injective hx')
  · refine' False.elim (h1 _)
    rw [← eq_sub_iff_add_eq, zero_sub] at hx'
    replace hx' := congr_arg (fun y => r⁻¹ • y) hx'
    simp only [Algebra.algebraMap_eq_smul_one, ← smul_assoc, smul_eq_mul, inv_mul_cancel hr,
      one_smul] at hx'
    exact hx'.symm ▸ SMulMemClass.smul_mem r⁻¹ (neg_mem a.prop)
#align non_unital_subalgebra.unitization_injective NonUnitalSubalgebra.unitization_injective

/-- If a `non_unital_subalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `algebra.adjoin`. -/
noncomputable def NonUnitalSubalgebra.unitizationAlgEquiv {R S A : Type _} [Field R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h1 : (1 : A) ∉ s) : Unitization R s ≃ₐ[R] Algebra.adjoin R (s : Set A) :=
  AlgEquiv.ofBijective (NonUnitalSubalgebra.unitization s)
    ⟨NonUnitalSubalgebra.unitization_injective s h1, NonUnitalSubalgebra.unitization_surjective s⟩
#align non_unital_subalgebra.unitization_alg_equiv NonUnitalSubalgebra.unitizationAlgEquiv

end Generic

section Subsemiring

variable {R : Type _} [NonAssocSemiring R]

/-! ## Subsemirings -/


/-- Turn a `subsemiring` into a `non_unital_subsemiring` by forgetting that it contains `1`. -/
def Subsemiring.toNonUnitalSubsemiring (S : Subsemiring R) : NonUnitalSubsemiring R :=
  { S with carrier := S.carrier }
#align subsemiring.to_non_unital_subsemiring Subsemiring.toNonUnitalSubsemiring

theorem Subsemiring.one_mem_toNonUnitalSubsemiring (S : Subsemiring R) :
    (1 : R) ∈ S.toNonUnitalSubsemiring :=
  S.one_mem
#align subsemiring.one_mem_to_non_unital_subsemiring Subsemiring.one_mem_toNonUnitalSubsemiring

/-- Turn a non-unital subsemiring containing `1` into a subsemiring. -/
def NonUnitalSubsemiring.toSubsemiring (S : NonUnitalSubsemiring R) (h1 : (1 : R) ∈ S) :
    Subsemiring R :=
  { S with
    carrier := S.carrier
    one_mem' := h1 }
#align non_unital_subsemiring.to_subsemiring NonUnitalSubsemiring.toSubsemiring

theorem Subsemiring.toNonUnitalSubsemiring_toSubsemiring (S : Subsemiring R) :
    S.toNonUnitalSubsemiring.toSubsemiring S.one_mem = S :=
  Subsemiring.casesOn S fun _ _ _ _ _ => rfl
#align subsemiring.to_non_unital_subsemiring_to_subsemiring Subsemiring.toNonUnitalSubsemiring_toSubsemiring

theorem NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring (S : NonUnitalSubsemiring R)
    (h1 : (1 : R) ∈ S) : (NonUnitalSubsemiring.toSubsemiring S h1).toNonUnitalSubsemiring = S := by
  cases S; rfl
#align non_unital_subsemiring.to_subsemiring_to_non_unital_subsemiring NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring

/-- The `ℕ`-algebra equivalence between `subsemiring.closure s` and `algebra.adjoin ℕ s` given
by the identity map. -/
def Subsemiring.closureEquivAdjoinNat {R : Type _} [Semiring R] (s : Set R) :
    Subsemiring.closure s ≃ₐ[ℕ] Algebra.adjoin ℕ s
    where
  toFun :=
    Subtype.map id fun r hr =>
      Subsemiring.closure_induction hr Algebra.subset_adjoin (zero_mem _) (one_mem _)
        (fun _ _ => add_mem) fun _ _ => mul_mem
  invFun :=
    Subtype.map id fun r hr =>
      Algebra.adjoin_induction hr Subsemiring.subset_closure (natCast_mem _) (fun _ _ => add_mem)
        fun _ _ => mul_mem
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl
#align subsemiring.closure_equiv_adjoin_nat Subsemiring.closureEquivAdjoinNat

/-- The natural `ℕ`-algebra homomorphism from the unitization of a non-unital subsemiring to
its `subsemiring.closure`. -/
def NonUnitalSubsemiring.unitization {R : Type _} [Semiring R] (S : NonUnitalSubsemiring R) :
    Unitization ℕ S →ₐ[ℕ] Subsemiring.closure (S : Set R) :=
  AlgEquiv.refl.arrowCongr (Subsemiring.closureEquivAdjoinNat (S : Set R)).symm <|
    NonUnitalSubalgebra.unitization S
#align non_unital_subsemiring.unitization NonUnitalSubsemiring.unitization

@[simp]
theorem NonUnitalSubsemiring.unitization_apply_coe {R : Type _} [Semiring R]
    (S : NonUnitalSubsemiring R) (x : Unitization ℕ S) :
    (S.Unitization x : R) = algebraMap ℕ (Subsemiring.closure (S : Set R)) x.fst + x.snd :=
  rfl
#align non_unital_subsemiring.unitization_apply_coe NonUnitalSubsemiring.unitization_apply_coe

theorem NonUnitalSubsemiring.unitization_surjective {R : Type _} [Semiring R]
    (S : NonUnitalSubsemiring R) : Function.Surjective S.Unitization :=
  by
  intro x
  refine' Subsemiring.closure_induction' x _ ⟨0, map_zero _⟩ ⟨1, map_one _⟩ _ _
  · refine' fun x hx => ⟨(0, ⟨x, hx⟩), Subtype.ext _⟩
    simp only [NonUnitalSubsemiring.unitization_apply_coe, Subtype.coe_mk, Unitization.fst,
      Unitization.snd, map_zero, Subsemiring.coe_zero, zero_add]
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, map_mul _ _ _⟩
#align non_unital_subsemiring.unitization_surjective NonUnitalSubsemiring.unitization_surjective

end Subsemiring

section Subring

variable {R : Type _} [Ring R]

/-! ## Subrings -/


/-- Turn a `subring` into a `non_unital_subring` by forgetting that it contains `1`. -/
def Subring.toNonUnitalSubring (S : Subring R) : NonUnitalSubring R :=
  { S with carrier := S.carrier }
#align subring.to_non_unital_subring Subring.toNonUnitalSubring

theorem Subring.one_mem_toNonUnitalSubring (S : Subring R) : (1 : R) ∈ S.toNonUnitalSubring :=
  S.one_mem
#align subring.one_mem_to_non_unital_subring Subring.one_mem_toNonUnitalSubring

/-- Turn a non-unital subring containing `1` into a subring. -/
def NonUnitalSubring.toSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) : Subring R :=
  { S with
    carrier := S.carrier
    one_mem' := h1 }
#align non_unital_subring.to_subring NonUnitalSubring.toSubring

theorem Subring.toNonUnitalSubring_toSubring (S : Subring R) :
    S.toNonUnitalSubring.toSubring S.one_mem = S :=
  Subring.casesOn S fun _ _ _ _ _ _ => rfl
#align subring.to_non_unital_subring_to_subring Subring.toNonUnitalSubring_toSubring

theorem NonUnitalSubring.toSubring_toNonUnitalSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) :
    (NonUnitalSubring.toSubring S h1).toNonUnitalSubring = S := by cases S; rfl
#align non_unital_subring.to_subring_to_non_unital_subring NonUnitalSubring.toSubring_toNonUnitalSubring

-- why don't we have this theorem?
theorem int_cast_mem {S : Type _} {R : Type _} [AddGroupWithOne R] [SetLike S R] (s : S)
    [AddSubmonoidWithOneClass S R] [NegMemClass S R] (n : ℤ) : (n : R) ∈ s :=
  by
  cases n
  simpa only [Int.cast_ofNat, Int.ofNat_eq_coe] using natCast_mem s n
  simpa only [Int.cast_negSucc] using neg_mem (natCast_mem s (n + 1))
#align int_cast_mem int_cast_mem

/-- The `ℤ`-algebra equivalence between `subring.closure s` and `algebra.adjoin ℤ s` given by
the identity map. -/
def Subring.closureEquivAdjoinInt (s : Set R) : Subring.closure s ≃ₐ[ℤ] Algebra.adjoin ℤ s
    where
  toFun :=
    Subtype.map id fun r hr =>
      Subring.closure_induction hr Algebra.subset_adjoin (zero_mem _) (one_mem _)
        (fun _ _ => add_mem) (fun _ => neg_mem) fun _ _ => mul_mem
  invFun :=
    Subtype.map id fun r hr =>
      Algebra.adjoin_induction hr Subring.subset_closure (int_cast_mem _) (fun _ _ => add_mem)
        fun _ _ => mul_mem
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl
#align subring.closure_equiv_adjoin_int Subring.closureEquivAdjoinInt

/-- The natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring to
its `subring.closure`. -/
def NonUnitalSubring.unitization
    (S : NonUnitalSubring R) :-- (h : ∀ n : ℕ, (n : R) ∉ S) :
        Unitization
        ℤ S →ₐ[ℤ]
      Subring.closure (S : Set R) :=
  AlgEquiv.refl.arrowCongr (Subring.closureEquivAdjoinInt (S : Set R)).symm <|
    NonUnitalSubalgebra.unitization S
#align non_unital_subring.unitization NonUnitalSubring.unitization

@[simp]
theorem NonUnitalSubring.unitization_apply_coe (S : NonUnitalSubring R) (x : Unitization ℤ S) :
    (S.Unitization x : R) = algebraMap ℤ (Subring.closure (S : Set R)) x.fst + x.snd :=
  rfl
#align non_unital_subring.unitization_apply_coe NonUnitalSubring.unitization_apply_coe

theorem NonUnitalSubring.unitization_surjective (S : NonUnitalSubring R) :
    Function.Surjective S.Unitization := by
  intro x
  refine' Subring.closure_induction' x _ ⟨0, map_zero _⟩ ⟨1, map_one _⟩ _ _ _
  · refine' fun x hx => ⟨(0, ⟨x, hx⟩), Subtype.ext _⟩
    simp only [NonUnitalSubring.unitization_apply_coe, Subtype.coe_mk, Unitization.fst,
      Unitization.snd, map_zero, Subring.coe_zero, zero_add]
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨-x, map_neg _ _⟩
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, map_mul _ _ _⟩
#align non_unital_subring.unitization_surjective NonUnitalSubring.unitization_surjective

end Subring

section Subalgebra

variable {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]

/-! ## Subalgebras -/


/-- Turn a `subalgebra` into a `non_unital_subalgebra` by forgetting that it contains `1`. -/
def Subalgebra.toNonUnitalSubalgebra (S : Subalgebra R A) : NonUnitalSubalgebra R A :=
  { S with
    carrier := S.carrier
    smul_mem' := fun r x hx => S.smul_mem hx r }
#align subalgebra.to_non_unital_subalgebra Subalgebra.toNonUnitalSubalgebra

theorem Subalgebra.one_mem_toNonUnitalSubalgebra (S : Subalgebra R A) :
    (1 : A) ∈ S.toNonUnitalSubalgebra :=
  S.one_mem
#align subalgebra.one_mem_to_non_unital_subalgebra Subalgebra.one_mem_toNonUnitalSubalgebra

/-- Turn a non-unital subalgebra containing `1` into a subalgebra. -/
def NonUnitalSubalgebra.toSubalgebra (S : NonUnitalSubalgebra R A) (h1 : (1 : A) ∈ S) :
    Subalgebra R A :=
  { S with
    carrier := S.carrier
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (@Algebra.algebraMap_eq_smul_one R A _ _ _ r).symm ▸ S.smul_mem h1 r }
#align non_unital_subalgebra.to_subalgebra NonUnitalSubalgebra.toSubalgebra

theorem Subalgebra.toNonUnitalSubalgebra_toSubalgebra (S : Subalgebra R A) :
    S.toNonUnitalSubalgebra.toSubalgebra S.one_mem = S :=
  Subalgebra.casesOn S fun _ _ _ _ _ _ => rfl
#align subalgebra.to_non_unital_subalgebra_to_subalgebra Subalgebra.toNonUnitalSubalgebra_toSubalgebra

theorem NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A)
    (h1 : (1 : A) ∈ S) : (NonUnitalSubalgebra.toSubalgebra S h1).toNonUnitalSubalgebra = S := by
  cases S; rfl
#align non_unital_subalgebra.to_subalgebra_to_non_unital_subalgebra NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra

end Subalgebra

namespace Unitization

section StarAlgHom

variable {S R A : Type _} [CommSemiring S] [CommSemiring R] [StarRing R] [NonUnitalSemiring A]
  [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A]
  {C : Type _} [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `unitization R A`
realized as a non-unital algebra homomorphism. -/
@[simps]
def coeNonUnitalStarAlgHom (R A : Type _) [CommSemiring R] [StarAddMonoid R] [NonUnitalSemiring A]
    [Star A] [Module R A] : A →⋆ₙₐ[R] Unitization R A
    where
  toFun := coe
  map_smul' := inr_smul R
  map_zero' := inr_zero R
  map_add' := inr_add R
  map_mul' := inr_mul R
  map_star' := inr_star
#align unitization.coe_non_unital_star_alg_hom Unitization.coeNonUnitalStarAlgHom

/-- Non-unital star algebra homomorphisms from `A` into a unital star `R`-algebra `C` lift uniquely
to `unitization R A →⋆ₐ[R] C`. This is the universal property of the unitization. -/
@[simps apply_apply]
def starLift : (A →⋆ₙₐ[R] C) ≃ (Unitization R A →⋆ₐ[R] C)
    where
  toFun φ :=
    {
      Unitization.lift'
        φ.toNonUnitalAlgHom with
      toFun := Unitization.lift' φ.toNonUnitalAlgHom
      map_star' := fun x => by
        induction x using Unitization.ind
        simp only [star_add, lift'_apply_apply, fst_add, fst_star, fst_inl, fst_coe, star_zero,
          add_zero, snd_add, snd_star, snd_inl, snd_coe, zero_add,
          NonUnitalStarAlgHom.coe_toNonUnitalAlgHom, map_star, algebraMap_star_comm] }
  invFun φ := φ.toNonUnitalStarAlgHom.comp (coeNonUnitalStarAlgHom R A)
  left_inv φ := by ext; simp
  right_inv φ := bar (by simp)
#align unitization.star_lift Unitization.starLift

theorem starLift_symm_apply (φ : Unitization R A →⋆ₐ[R] C) (a : A) :
    Unitization.starLift.symm φ a = φ a :=
  rfl
#align unitization.star_lift_symm_apply Unitization.starLift_symm_apply

end StarAlgHom

end Unitization

section StarSubalgebra

variable {R A : Type _} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]

variable [Algebra R A] [StarModule R A]

/-! ## star_subalgebras -/


/--
Turn a `star_subalgebra` into a `non_unital_star_subalgebra` by forgetting that it contains `1`. -/
def StarSubalgebra.toNonUnitalStarSubalgebra (S : StarSubalgebra R A) :
    NonUnitalStarSubalgebra R A :=
  { S with
    carrier := S.carrier
    smul_mem' := fun r x hx => S.smul_mem hx r }
#align star_subalgebra.to_non_unital_star_subalgebra StarSubalgebra.toNonUnitalStarSubalgebra

theorem StarSubalgebra.one_mem_toNonUnitalStarSubalgebra (S : StarSubalgebra R A) :
    (1 : A) ∈ S.toNonUnitalStarSubalgebra :=
  S.one_mem'
#align star_subalgebra.one_mem_to_non_unital_star_subalgebra StarSubalgebra.one_mem_toNonUnitalStarSubalgebra

/-- Turn a non-unital star_subalgebra containing `1` into a star_subalgebra. -/
def NonUnitalStarSubalgebra.toStarSubalgebra (S : NonUnitalStarSubalgebra R A) (h1 : (1 : A) ∈ S) :
    StarSubalgebra R A :=
  { S with
    carrier := S.carrier
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (@Algebra.algebraMap_eq_smul_one R A _ _ _ r).symm ▸ S.smul_mem h1 r }
#align non_unital_star_subalgebra.to_star_subalgebra NonUnitalStarSubalgebra.toStarSubalgebra

theorem StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra (S : StarSubalgebra R A) :
    S.toNonUnitalStarSubalgebra.toStarSubalgebra S.one_mem' = S :=
  StarSubalgebra.casesOn S fun _ _ _ _ _ _ _ => rfl
#align star_subalgebra.to_non_unital_star_subalgebra_to_star_subalgebra StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra

theorem NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) (h1 : (1 : A) ∈ S) :
    (NonUnitalStarSubalgebra.toStarSubalgebra S h1).toNonUnitalStarSubalgebra = S := by cases S; rfl
#align non_unital_star_subalgebra.to_star_subalgebra_to_non_unital_star_subalgebra NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra

/-- The natural `R`-algebra homomorphism from the unitization of a non-unital star_subalgebra to
its `algebra.adjoin`. -/
def NonUnitalStarSubalgebra.unitization (S : NonUnitalStarSubalgebra R A) :
    Unitization R S →⋆ₐ[R] StarSubalgebra.adjoin R (S : Set A) :=
  Unitization.starLift
    { toFun := fun x : S =>
        (⟨x, StarSubalgebra.subset_adjoin R _ x.Prop⟩ : StarSubalgebra.adjoin R (S : Set A))
      map_smul' := fun (_ : R) _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      map_star' := fun _ => rfl }
#align non_unital_star_subalgebra.unitization NonUnitalStarSubalgebra.unitization

@[simp]
theorem NonUnitalStarSubalgebra.unitization_apply_coe (S : NonUnitalStarSubalgebra R A)
    (x : Unitization R S) :
    (S.Unitization x : A) = algebraMap R (StarSubalgebra.adjoin R (S : Set A)) x.fst + x.snd :=
  rfl
#align non_unital_star_subalgebra.unitization_apply_coe NonUnitalStarSubalgebra.unitization_apply_coe

theorem NonUnitalStarSubalgebra.unitization_surjective (S : NonUnitalStarSubalgebra R A) :
    Function.Surjective S.Unitization :=
  by
  refine' fun x => StarSubalgebra.adjoin_induction' x _ _ _ _ _
  · refine' fun x hx => ⟨(0, ⟨x, hx⟩), Subtype.ext _⟩
    simp only [NonUnitalSubalgebra.unitization_apply_coe, Subtype.coe_mk]
    change (algebraMap R { x // x ∈ Algebra.adjoin R (S : Set A) } 0 : A) + x = x
    rw [map_zero, Subsemiring.coe_zero, zero_add]
  · exact fun r => ⟨algebraMap R (Unitization R S) r, AlgHom.commutes _ r⟩
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, map_mul _ _ _⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨star x, map_star _ _⟩
#align non_unital_star_subalgebra.unitization_surjective NonUnitalStarSubalgebra.unitization_surjective

-- it would be nice to get the surjectivity and other results for free from the non-starred version
end StarSubalgebra
