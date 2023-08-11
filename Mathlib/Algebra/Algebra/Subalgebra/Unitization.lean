/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# Relating unital and non-unital substructures

This file relates various algebraic structures and provides maps (generally algebra homomorphisms),
from the unitization of a non-unital subobject into the full structure. The range of this map is
the unital closure of the non-unital subobject (e.g., `Algebra.adjoin`, `Subring.closure`,
`Subsemiring.closure` or `StarSubalgebra.adjoin`). When the underlying scalar ring is a field, for
this map to be injective it suffices that the range omits `1`. In this setting we provide suitable
`AlgEquiv` (or `StarAlgEquiv`) onto the range.

## Main declarations

* `NonUnitalSubalgebra.unitization s : Unitization R s →ₐ[R] A`:
  where `s` is a non-unital subalgebra of a unital `R`-algebra `A`, this is the natural algebra
  homomorphism sending `(r, a)` to `r • 1 + a`. The range of this map is
  `Algebra.adjoin R (s : Set A)`.
* `NonUnitalSubalgebra.unitizationAlgEquiv s : Unitization R s ≃ₐ[R] Algebra.adjoin R (s : Set A)`:
  when `R` is a field and `1 ∉ s`. This is `NonUnitalSubalgebra.unitization` upgraded to an
  `AlgEquiv` onto its range.
* `NonUnitalSubsemiring.unitization : Unitization ℕ S →ₐ[ℕ] R`: the natural `ℕ`-algebra homomorphism
  from the unitization of a non-unital subsemiring `S` into the ring containing it. The range of
  this map is `subalgebraOfSubsemiring (Subsemiring.closure S)`.
  This is just `NonUnitalSubalgebra.unitization S` but we provide a separate declaration because
  there is an instance Lean can't find on its own due to `outParam`.
* `NonUnitalSubring.unitization : Unitization ℤ S →ₐ[ℤ] R`:
  the natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring `S` into the
  ring containing it. The range of this map is `subalgebraOfSubring (Subring.closure S)`.
  This is just `NonUnitalSubalgebra.unitization S` but we provide a separate declaration because
  there is an instance Lean can't find on its own due to `outParam`.
* `NonUnitalStarSubalgebra S : Unitization R S →⋆ₐ[R] A`: A version of
  `NonUnitalSubalgebra.unitization` for star algebras.
* `NonUnitalStarSubalgebra.unitizationStarAlgEquiv S :`
  `Unitization R S ≃⋆ₐ[R] StarSubalgebra.adjoin R (S : Set A)`:
  a version of `NonUnitalSubalgebra.unitizationAlgEquiv` for star algebras.
-/

section Subalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-! ## Subalgebras -/


/-- Turn a `Subalgebra` into a `NonUnitalSubalgebra` by forgetting that it contains `1`. -/
def Subalgebra.toNonUnitalSubalgebra (S : Subalgebra R A) : NonUnitalSubalgebra R A :=
  { S with
    smul_mem' := fun r _x hx => S.smul_mem hx r }

theorem Subalgebra.one_mem_toNonUnitalSubalgebra (S : Subalgebra R A) :
    (1 : A) ∈ S.toNonUnitalSubalgebra :=
  S.one_mem

/-- Turn a non-unital subalgebra containing `1` into a subalgebra. -/
def NonUnitalSubalgebra.toSubalgebra (S : NonUnitalSubalgebra R A) (h1 : (1 : A) ∈ S) :
    Subalgebra R A :=
  { S with
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1 }

theorem Subalgebra.toNonUnitalSubalgebra_toSubalgebra (S : Subalgebra R A) :
    S.toNonUnitalSubalgebra.toSubalgebra S.one_mem = S := by cases S; rfl

theorem NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A)
    (h1 : (1 : A) ∈ S) : (NonUnitalSubalgebra.toSubalgebra S h1).toNonUnitalSubalgebra = S := by
  cases S; rfl

end Subalgebra

section LiftRange

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [Semiring C] [Algebra R C]

theorem Unitization.lift_range_le {f : A →ₙₐ[R] C} {S : Subalgebra R C} :
    (Unitization.lift f).range ≤ S ↔ NonUnitalAlgHom.range f ≤ S.toNonUnitalSubalgebra := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x using Unitization.ind with
    | _ r a => simpa using add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

theorem Unitization.lift_range (f : A →ₙₐ[R] C) :
    (Unitization.lift f).range = Algebra.adjoin R (NonUnitalAlgHom.range f : Set C) :=
  eq_of_forall_ge_iff fun c ↦ by rw [Unitization.lift_range_le, Algebra.adjoin_le_iff]; rfl

end LiftRange

section Generic

variable {R S A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [SetLike S A]
  [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A] (s : S)

/-- The natural `R`-algebra homomorphism from the unitization of a non-unital subalgebra into
the algebra containing it. -/
def NonUnitalSubalgebra.unitization : Unitization R s →ₐ[R] A :=
  Unitization.lift (NonUnitalSubalgebraClass.subtype s)

@[simp]
theorem NonUnitalSubalgebra.unitization_apply (x : Unitization R s) :
    NonUnitalSubalgebra.unitization s x = algebraMap R A x.fst + x.snd :=
  rfl

theorem NonUnitalSubalgebra.unitization_range :
    (NonUnitalSubalgebra.unitization s).range = Algebra.adjoin R (s : Set A) := by
  rw [unitization, Unitization.lift_range]
  simp only [NonUnitalAlgHom.coe_range, NonUnitalSubalgebraClass.coeSubtype,
    Subtype.range_coe_subtype, SetLike.mem_coe]
  rfl

/-- This is a generic version which allows us to prove both
`NonUnitalSubalgebra.unitization_injective` and `NonUnitalStarSubalgebra.unitization_injective`. -/
theorem AlgHomClass.unitization_injective' {F R S A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h : ∀ r, r ≠ 0 → algebraMap R A r ∉ s) [AlgHomClass F R (Unitization R s) A] (f : F)
    (hf : ∀ x : s, f x = x) : Function.Injective f := by
  refine' (injective_iff_map_eq_zero _).mpr fun x hx => _
  induction' x using Unitization.ind with r a
  simp_rw [map_add, hf, ←Unitization.algebraMap_eq_inl, AlgHomClass.commutes] at hx
  rw [add_eq_zero_iff_eq_neg] at hx ⊢
  by_cases hr : r = 0
  · ext <;> simp [hr] at hx ⊢
    exact hx
  · exact (h r hr <| hx ▸ (neg_mem a.property)).elim

/-- This is a generic version which allows us to prove both
`NonUnitalSubalgebra.unitization_injective` and `NonUnitalStarSubalgebra.unitization_injective`. -/
theorem AlgHomClass.unitization_injective {F R S A : Type*} [Field R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h1 : 1 ∉ s) [AlgHomClass F R (Unitization R s) A] (f : F)
    (hf : ∀ x : s, f x = x) : Function.Injective f := by
  refine AlgHomClass.unitization_injective' s (fun r hr hr' ↦ ?_) f hf
  rw [Algebra.algebraMap_eq_smul_one] at hr'
  exact h1 <| inv_smul_smul₀ hr (1 : A) ▸ SMulMemClass.smul_mem r⁻¹ hr'

variable {R S A : Type*} [Field R] [Ring A] [Algebra R A]
  [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A] (s : S)

theorem NonUnitalSubalgebra.unitization_injective (h1 : (1 : A) ∉ s) :
    Function.Injective (NonUnitalSubalgebra.unitization s) :=
  AlgHomClass.unitization_injective s h1 (NonUnitalSubalgebra.unitization s) fun _ ↦ by simp

/-- If a `NonUnitalSubalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `Algebra.adjoin`. -/
@[simps! apply_coe]
noncomputable def NonUnitalSubalgebra.unitizationAlgEquiv (h1 : (1 : A) ∉ s) :
    Unitization R s ≃ₐ[R] Algebra.adjoin R (s : Set A) :=
  let algHom : Unitization R s →ₐ[R] Algebra.adjoin R (s : Set A) :=
    ((NonUnitalSubalgebra.unitization s).codRestrict _
      fun x ↦ (NonUnitalSubalgebra.unitization_range s).le <| AlgHom.mem_range_self _ x)
  AlgEquiv.ofBijective algHom <| by
    refine ⟨?_, fun x ↦ ?_⟩
    · have := AlgHomClass.unitization_injective s h1
        ((Subalgebra.val _).comp <| algHom) fun _ ↦ by simp
      simp only [AlgHom.coe_comp, Subalgebra.coe_val] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) ∈ (NonUnitalSubalgebra.unitization s).range) :=
        (NonUnitalSubalgebra.unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

end Generic

section Subsemiring

variable {R : Type*} [NonAssocSemiring R]

/-! ## Subsemirings -/

/-- Turn a `Subsemiring` into a `NonUnitalSubsemiring` by forgetting that it contains `1`. -/
def Subsemiring.toNonUnitalSubsemiring (S : Subsemiring R) : NonUnitalSubsemiring R :=
  { S with }

theorem Subsemiring.one_mem_toNonUnitalSubsemiring (S : Subsemiring R) :
    (1 : R) ∈ S.toNonUnitalSubsemiring :=
  S.one_mem

/-- Turn a non-unital subsemiring containing `1` into a subsemiring. -/
def NonUnitalSubsemiring.toSubsemiring (S : NonUnitalSubsemiring R) (h1 : (1 : R) ∈ S) :
    Subsemiring R :=
  { S with
    one_mem' := h1 }

theorem Subsemiring.toNonUnitalSubsemiring_toSubsemiring (S : Subsemiring R) :
    S.toNonUnitalSubsemiring.toSubsemiring S.one_mem = S := by cases S; rfl

theorem NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring (S : NonUnitalSubsemiring R)
    (h1 : (1 : R) ∈ S) : (NonUnitalSubsemiring.toSubsemiring S h1).toNonUnitalSubsemiring = S := by
  cases S; rfl

/-- The natural `ℕ`-algebra homomorphism from the unitization of a non-unital subsemiring to
its `Subsemiring.closure`. -/
def NonUnitalSubsemiring.unitization {R : Type*} [Semiring R] (S : NonUnitalSubsemiring R) :
    Unitization ℕ S →ₐ[ℕ] R :=
  NonUnitalSubalgebra.unitization (hSRA := AddSubmonoidClass.nsmulMemClass) S

@[simp]
theorem NonUnitalSubsemiring.unitization_apply {R : Type*} [Semiring R]
    (S : NonUnitalSubsemiring R) (x : Unitization ℕ S) :
    S.unitization x = x.fst + x.snd :=
  rfl

theorem NonUnitalSubsemiring.unitization_range {R : Type*} [Semiring R]
    (S : NonUnitalSubsemiring R) :
    S.unitization.range = subalgebraOfSubsemiring (Subsemiring.closure S) := by
  have := AddSubmonoidClass.nsmulMemClass (S := NonUnitalSubsemiring R)
  rw [unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_nat]

end Subsemiring

section Subring

variable {R : Type*} [Ring R]

/-! ## Subrings -/

/-- Turn a `Subring` into a `NonUnitalSubring` by forgetting that it contains `1`. -/
def Subring.toNonUnitalSubring (S : Subring R) : NonUnitalSubring R :=
  { S with }

theorem Subring.one_mem_toNonUnitalSubring (S : Subring R) : (1 : R) ∈ S.toNonUnitalSubring :=
  S.one_mem

/-- Turn a non-unital subring containing `1` into a subring. -/
def NonUnitalSubring.toSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) : Subring R :=
  { S with
    one_mem' := h1 }

theorem Subring.toNonUnitalSubring_toSubring (S : Subring R) :
    S.toNonUnitalSubring.toSubring S.one_mem = S := by cases S; rfl

theorem NonUnitalSubring.toSubring_toNonUnitalSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) :
    (NonUnitalSubring.toSubring S h1).toNonUnitalSubring = S := by cases S; rfl

/-- The natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring to
its `Subring.closure`. -/
def NonUnitalSubring.unitization (S : NonUnitalSubring R) :
    Unitization ℤ S →ₐ[ℤ] R :=
  NonUnitalSubalgebra.unitization (hSRA := AddSubgroupClass.zsmulMemClass) S

@[simp]
theorem NonUnitalSubring.unitization_apply (S : NonUnitalSubring R) (x : Unitization ℤ S) :
    S.unitization x = x.fst + x.snd :=
  rfl

theorem NonUnitalSubring.unitization_range (S : NonUnitalSubring R) :
    S.unitization.range = subalgebraOfSubring (Subring.closure S) := by
  have := AddSubgroupClass.zsmulMemClass (S := NonUnitalSubring R)
  rw [unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_int]

end Subring

section Subalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-! ## Subalgebras -/


/-- Turn a `Subalgebra` into a `NonUnitalSubalgebra` by forgetting that it contains `1`. -/
def Subalgebra.toNonUnitalSubalgebra (S : Subalgebra R A) : NonUnitalSubalgebra R A :=
  { S with
    carrier := S.carrier
    smul_mem' := fun r _x hx => S.smul_mem hx r }

theorem Subalgebra.one_mem_toNonUnitalSubalgebra (S : Subalgebra R A) :
    (1 : A) ∈ S.toNonUnitalSubalgebra :=
  S.one_mem

/-- Turn a non-unital subalgebra containing `1` into a subalgebra. -/
def NonUnitalSubalgebra.toSubalgebra (S : NonUnitalSubalgebra R A) (h1 : (1 : A) ∈ S) :
    Subalgebra R A :=
  { S with
    carrier := S.carrier
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1 }

theorem Subalgebra.toNonUnitalSubalgebra_toSubalgebra (S : Subalgebra R A) :
    S.toNonUnitalSubalgebra.toSubalgebra S.one_mem = S := by cases S; rfl

theorem NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A)
    (h1 : (1 : A) ∈ S) : (NonUnitalSubalgebra.toSubalgebra S h1).toNonUnitalSubalgebra = S := by
  cases S; rfl

end Subalgebra

section StarSubalgebra

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]

variable {R A C : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
variable [Algebra R A] [StarModule R A]

/-! ## star_subalgebras -/

/-- Turn a `StarSubalgebra` into a `NonUnitalStarSubalgebra` by forgetting that it contains `1`. -/
def StarSubalgebra.toNonUnitalStarSubalgebra (S : StarSubalgebra R A) :
    NonUnitalStarSubalgebra R A :=
  { S with
    carrier := S.carrier
    smul_mem' := fun r _x hx => S.smul_mem hx r }

theorem StarSubalgebra.one_mem_toNonUnitalStarSubalgebra (S : StarSubalgebra R A) :
    (1 : A) ∈ S.toNonUnitalStarSubalgebra :=
  S.one_mem'

/-- Turn a non-unital star subalgebra containing `1` into a `StarSubalgebra`. -/
def NonUnitalStarSubalgebra.toStarSubalgebra (S : NonUnitalStarSubalgebra R A) (h1 : (1 : A) ∈ S) :
    StarSubalgebra R A :=
  { S with
    carrier := S.carrier
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1 }

theorem StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra (S : StarSubalgebra R A) :
    S.toNonUnitalStarSubalgebra.toStarSubalgebra S.one_mem' = S := by cases S; rfl

theorem NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) (h1 : (1 : A) ∈ S) :
    (S.toStarSubalgebra h1).toNonUnitalStarSubalgebra = S := by
  cases S; rfl

section StarLiftRange

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing R] [StarRing A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A]
variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem Unitization.starLift_range_le
    {f : A →⋆ₙₐ[R] C} {S : StarSubalgebra R C} :
    (starLift f).range ≤ S ↔ NonUnitalStarAlgHom.range f ≤ S.toNonUnitalStarSubalgebra := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x using Unitization.ind with
    | _ r a => simpa using add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

theorem Unitization.starLift_range (f : A →⋆ₙₐ[R] C) :
    (starLift f).range = StarSubalgebra.adjoin R (NonUnitalStarAlgHom.range f : Set C) :=
  eq_of_forall_ge_iff fun c ↦ by 
    rw [Unitization.starLift_range_le, StarSubalgebra.adjoin_le_iff]
    rfl

end StarLiftRange

/-- The natural star `R`-algebra homomorphism from the unitization of a non-unital star subalgebra
to its `StarSubalgebra.adjoin`. -/
def NonUnitalStarSubalgebra.unitization (S : NonUnitalStarSubalgebra R A) :
    Unitization R S →⋆ₐ[R] A :=
  Unitization.starLift <| NonUnitalStarSubalgebraClass.subtype S

@[simp]
theorem NonUnitalStarSubalgebra.unitization_apply (S : NonUnitalStarSubalgebra R A)
    (x : Unitization R S) :
    S.unitization x = algebraMap R A x.fst + x.snd :=
  rfl

theorem NonUnitalStarSubalgebra.unitization_range (S : NonUnitalStarSubalgebra R A) :
    S.unitization.range = StarSubalgebra.adjoin R (S : Set A) := by
  rw [unitization, Unitization.starLift_range]
  simp only [NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass.coeSubtype,
    Subtype.range_coe_subtype]
  rfl

end Semiring

section Field

variable {R A : Type*} [Field R] [StarRing R] [Ring A] [StarRing A] [Algebra R A] [StarModule R A]
variable (S : NonUnitalStarSubalgebra R A)

theorem NonUnitalStarSubalgebra.unitization_injective (h1 : (1 : A) ∉ S) :
    Function.Injective S.unitization :=
  AlgHomClass.unitization_injective S h1 S.unitization fun _ ↦ by simp

/-- If a `NonUnitalStarSubalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `StarSubalgebra.adjoin`. -/
@[simps! apply_coe]
noncomputable def NonUnitalStarSubalgebra.unitizationStarAlgEquiv (h1 : (1 : A) ∉ S) :
    Unitization R S ≃⋆ₐ[R] StarSubalgebra.adjoin R (S : Set A) :=
  let starAlgHom : Unitization R S →⋆ₐ[R] StarSubalgebra.adjoin R (S : Set A) :=
    (S.unitization.codRestrict _
      fun x ↦ S.unitization_range.le <| Set.mem_range_self x)
  StarAlgEquiv.ofBijective starAlgHom <| by
    refine ⟨?_, fun x ↦ ?_⟩
    · have h_eq : S.unitization = (StarSubalgebra.subtype _).comp starAlgHom := rfl
      have this := S.unitization_injective h1
      rw [h_eq, StarAlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) ∈ S.unitization.range) :=
        S.unitization_range.ge x.property
      exact ⟨a, Subtype.ext ha⟩

end Field

end StarSubalgebra
