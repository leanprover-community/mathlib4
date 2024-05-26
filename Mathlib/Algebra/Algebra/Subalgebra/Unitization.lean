/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Relating unital and non-unital substructures

This file relates various algebraic structures and provides maps (generally algebra homomorphisms),
from the unitization of a non-unital subobject into the full structure. The range of this map is
the unital closure of the non-unital subobject (e.g., `Algebra.adjoin`, `Subring.closure`,
`Subsemiring.closure` or `StarAlgebra.adjoin`). When the underlying scalar ring is a field, for
this map to be injective it suffices that the range omits `1`. In this setting we provide suitable
`AlgEquiv` (or `StarAlgEquiv`) onto the range.

## Main declarations

* `NonUnitalSubalgebra.unitization s : Unitization R s →ₐ[R] A`:
  where `s` is a non-unital subalgebra of a unital `R`-algebra `A`, this is the natural algebra
  homomorphism sending `(r, a)` to `r • 1 + a`. The range of this map is
  `Algebra.adjoin R (s : Set A)`.
* `NonUnitalSubalgebra.unitizationAlgEquiv s : Unitization R s ≃ₐ[R] Algebra.adjoin R (s : Set A)`
  when `R` is a field and `1 ∉ s`. This is `NonUnitalSubalgebra.unitization` upgraded to an
  `AlgEquiv` onto its range.
* `NonUnitalSubsemiring.unitization : Unitization ℕ s →ₐ[ℕ] R`: the natural `ℕ`-algebra homomorphism
  from the unitization of a non-unital subsemiring `s` into the ring containing it. The range of
  this map is `subalgebraOfSubsemiring (Subsemiring.closure s)`.
  This is just `NonUnitalSubalgebra.unitization s` but we provide a separate declaration because
  there is an instance Lean can't find on its own due to `outParam`.
* `NonUnitalSubring.unitization : Unitization ℤ s →ₐ[ℤ] R`:
  the natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring `s` into the
  ring containing it. The range of this map is `subalgebraOfSubring (Subring.closure s)`.
  This is just `NonUnitalSubalgebra.unitization s` but we provide a separate declaration because
  there is an instance Lean can't find on its own due to `outParam`.
* `NonUnitalStarSubalgebra s : Unitization R s →⋆ₐ[R] A`: a version of
  `NonUnitalSubalgebra.unitization` for star algebras.
* `NonUnitalStarSubalgebra.unitizationStarAlgEquiv s :`
  `Unitization R s ≃⋆ₐ[R] StarAlgebra.adjoin R (s : Set A)`:
  a version of `NonUnitalSubalgebra.unitizationAlgEquiv` for star algebras.
-/

/-! ## Subalgebras -/

section Subalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

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

open Submodule in
lemma Algebra.adjoin_nonUnitalSubalgebra_eq_span (s : NonUnitalSubalgebra R A) :
    Subalgebra.toSubmodule (adjoin R (s : Set A)) = span R {1} ⊔ s.toSubmodule := by
  rw [adjoin_eq_span, Submonoid.closure_eq_one_union, span_union, ← NonUnitalAlgebra.adjoin_eq_span,
      NonUnitalAlgebra.adjoin_eq]

variable (R)

lemma NonUnitalAlgebra.adjoin_le_algebra_adjoin (s : Set A) :
    adjoin R s ≤ (Algebra.adjoin R s).toNonUnitalSubalgebra :=
  adjoin_le Algebra.subset_adjoin

lemma Algebra.adjoin_nonUnitalSubalgebra (s : Set A) :
    adjoin R (NonUnitalAlgebra.adjoin R s : Set A) = adjoin R s :=
  le_antisymm
    (adjoin_le <| NonUnitalAlgebra.adjoin_le_algebra_adjoin R s)
    (adjoin_le <| (NonUnitalAlgebra.subset_adjoin R).trans subset_adjoin)

end Subalgebra

namespace Unitization

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [Semiring C] [Algebra R C]

theorem lift_range_le {f : A →ₙₐ[R] C} {S : Subalgebra R C} :
    (lift f).range ≤ S ↔ NonUnitalAlgHom.range f ≤ S.toNonUnitalSubalgebra := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

theorem lift_range (f : A →ₙₐ[R] C) :
    (lift f).range = Algebra.adjoin R (NonUnitalAlgHom.range f : Set C) :=
  eq_of_forall_ge_iff fun c ↦ by rw [lift_range_le, Algebra.adjoin_le_iff]; rfl

end Unitization

namespace NonUnitalSubalgebra

section Semiring

variable {R S A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [SetLike S A]
  [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A] (s : S)

/-- The natural `R`-algebra homomorphism from the unitization of a non-unital subalgebra into
the algebra containing it. -/
def unitization : Unitization R s →ₐ[R] A :=
  Unitization.lift (NonUnitalSubalgebraClass.subtype s)

@[simp]
theorem unitization_apply (x : Unitization R s) :
    unitization s x = algebraMap R A x.fst + x.snd :=
  rfl

theorem unitization_range : (unitization s).range = Algebra.adjoin R (s : Set A) := by
  rw [unitization, Unitization.lift_range]
  simp only [NonUnitalAlgHom.coe_range, NonUnitalSubalgebraClass.coeSubtype,
    Subtype.range_coe_subtype, SetLike.mem_coe]
  rfl

end Semiring

/-- A sufficient condition for injectivity of `NonUnitalSubalgebra.unitization` when the scalars
are a commutative ring. When the scalars are a field, one should use the more natural
`NonUnitalStarSubalgebra.unitization_injective` whose hypothesis is easier to verify. -/
theorem _root_.AlgHomClass.unitization_injective' {F R S A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h : ∀ r, r ≠ 0 → algebraMap R A r ∉ s)
    [FunLike F (Unitization R s) A] [AlgHomClass F R (Unitization R s) A]
    (f : F) (hf : ∀ x : s, f x = x) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  induction' x with r a
  simp_rw [map_add, hf, ← Unitization.algebraMap_eq_inl, AlgHomClass.commutes] at hx
  rw [add_eq_zero_iff_eq_neg] at hx ⊢
  by_cases hr : r = 0
  · ext <;> simp [hr] at hx ⊢
    exact hx
  · exact (h r hr <| hx ▸ (neg_mem a.property)).elim

/-- This is a generic version which allows us to prove both
`NonUnitalSubalgebra.unitization_injective` and `NonUnitalStarSubalgebra.unitization_injective`. -/
theorem _root_.AlgHomClass.unitization_injective {F R S A : Type*} [Field R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h1 : 1 ∉ s) [FunLike F (Unitization R s) A] [AlgHomClass F R (Unitization R s) A]
    (f : F) (hf : ∀ x : s, f x = x) : Function.Injective f := by
  refine AlgHomClass.unitization_injective' s (fun r hr hr' ↦ ?_) f hf
  rw [Algebra.algebraMap_eq_smul_one] at hr'
  exact h1 <| inv_smul_smul₀ hr (1 : A) ▸ SMulMemClass.smul_mem r⁻¹ hr'

section Field

variable {R S A : Type*} [Field R] [Ring A] [Algebra R A]
  [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A] (s : S)

theorem unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (unitization s) :=
  AlgHomClass.unitization_injective s h1 (unitization s) fun _ ↦ by simp

/-- If a `NonUnitalSubalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `Algebra.adjoin`. -/
@[simps! apply_coe]
noncomputable def unitizationAlgEquiv (h1 : (1 : A) ∉ s) :
    Unitization R s ≃ₐ[R] Algebra.adjoin R (s : Set A) :=
  let algHom : Unitization R s →ₐ[R] Algebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
      fun x ↦ (unitization_range s).le <| AlgHom.mem_range_self _ x)
  AlgEquiv.ofBijective algHom <| by
    refine ⟨?_, fun x ↦ ?_⟩
    · have := AlgHomClass.unitization_injective s h1
        ((Subalgebra.val _).comp algHom) fun _ ↦ by simp [algHom]
      rw [AlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) ∈ (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

end Field

end NonUnitalSubalgebra

/-! ## Subsemirings -/

section Subsemiring

variable {R : Type*} [NonAssocSemiring R]

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

end Subsemiring

namespace NonUnitalSubsemiring

variable {R S : Type*} [Semiring R] [SetLike S R] [hSR : NonUnitalSubsemiringClass S R] (s : S)

/-- The natural `ℕ`-algebra homomorphism from the unitization of a non-unital subsemiring to
its `Subsemiring.closure`. -/
def unitization : Unitization ℕ s →ₐ[ℕ] R :=
  NonUnitalSubalgebra.unitization (hSRA := AddSubmonoidClass.nsmulMemClass) s

@[simp]
theorem unitization_apply (x : Unitization ℕ s) : unitization s x = x.fst + x.snd :=
  rfl

theorem unitization_range :
    (unitization s).range = subalgebraOfSubsemiring (Subsemiring.closure s) := by
  have := AddSubmonoidClass.nsmulMemClass (S := S)
  rw [unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_nat]

end NonUnitalSubsemiring

/-! ## Subrings -/

section Subring

-- TODO: Maybe we could use `NonAssocRing` here but right now `Subring` takes a `Ring` argument.
variable {R : Type*} [Ring R]

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

end Subring

namespace NonUnitalSubring

variable {R S : Type*} [Ring R] [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

/-- The natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring to
its `Subring.closure`. -/
def unitization : Unitization ℤ s →ₐ[ℤ] R :=
  NonUnitalSubalgebra.unitization (hSRA := AddSubgroupClass.zsmulMemClass) s

@[simp]
theorem unitization_apply (x : Unitization ℤ s) : unitization s x = x.fst + x.snd :=
  rfl

theorem unitization_range :
    (unitization s).range = subalgebraOfSubring (Subring.closure s) := by
  have := AddSubgroupClass.zsmulMemClass (S := S)
  rw [unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_int]

end NonUnitalSubring

/-! ## Star subalgebras -/

section StarSubalgebra

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
variable [Algebra R A] [StarModule R A]

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

open Submodule in
lemma StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span (s : NonUnitalStarSubalgebra R A) :
    Subalgebra.toSubmodule (adjoin R (s : Set A)).toSubalgebra = span R {1} ⊔ s.toSubmodule := by
  rw [adjoin_eq_span, Submonoid.closure_eq_one_union, span_union,
    ← NonUnitalStarAlgebra.adjoin_eq_span, NonUnitalStarAlgebra.adjoin_eq]

variable (R)

lemma NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin (s : Set A) :
    adjoin R s ≤ (StarAlgebra.adjoin R s).toNonUnitalStarSubalgebra :=
  adjoin_le <| StarAlgebra.subset_adjoin R s

lemma StarAlgebra.adjoin_nonUnitalStarSubalgebra (s : Set A) :
    adjoin R (NonUnitalStarAlgebra.adjoin R s : Set A) = adjoin R s :=
  le_antisymm
    (adjoin_le <| NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin R s)
    (adjoin_le <| (NonUnitalStarAlgebra.subset_adjoin R s).trans <| subset_adjoin R _)

end StarSubalgebra

namespace Unitization

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing R] [StarRing A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A]
variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem starLift_range_le
    {f : A →⋆ₙₐ[R] C} {S : StarSubalgebra R C} :
    (starLift f).range ≤ S ↔ NonUnitalStarAlgHom.range f ≤ S.toNonUnitalStarSubalgebra := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

theorem starLift_range (f : A →⋆ₙₐ[R] C) :
    (starLift f).range = StarAlgebra.adjoin R (NonUnitalStarAlgHom.range f : Set C) :=
  eq_of_forall_ge_iff fun c ↦ by
    rw [starLift_range_le, StarAlgebra.adjoin_le_iff]
    rfl

end Unitization

namespace NonUnitalStarSubalgebra

section Semiring

variable {R S A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A] [SetLike S A] [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A]
  [StarMemClass S A] (s : S)
/-- The natural star `R`-algebra homomorphism from the unitization of a non-unital star subalgebra
to its `StarAlgebra.adjoin`. -/
def unitization : Unitization R s →⋆ₐ[R] A :=
  Unitization.starLift <| NonUnitalStarSubalgebraClass.subtype s

@[simp]
theorem unitization_apply (x : Unitization R s) : unitization s x = algebraMap R A x.fst + x.snd :=
  rfl

theorem unitization_range : (unitization s).range = StarAlgebra.adjoin R s := by
  rw [unitization, Unitization.starLift_range]
  simp only [NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass.coeSubtype,
    Subtype.range_coe_subtype]
  rfl

end Semiring

section Field

variable {R S A : Type*} [Field R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
  [StarModule R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
  [StarMemClass S A] (s : S)

theorem unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (unitization s) :=
  AlgHomClass.unitization_injective s h1 (unitization s) fun _ ↦ by simp

/-- If a `NonUnitalStarSubalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `StarAlgebra.adjoin`. -/
@[simps! apply_coe]
noncomputable def unitizationStarAlgEquiv (h1 : (1 : A) ∉ s) :
    Unitization R s ≃⋆ₐ[R] StarAlgebra.adjoin R (s : Set A) :=
  let starAlgHom : Unitization R s →⋆ₐ[R] StarAlgebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
      fun x ↦ (unitization_range s).le <| Set.mem_range_self x)
  StarAlgEquiv.ofBijective starAlgHom <| by
    refine ⟨?_, fun x ↦ ?_⟩
    · have := AlgHomClass.unitization_injective s h1 ((StarSubalgebra.subtype _).comp starAlgHom)
        fun _ ↦ by simp [starAlgHom]
      rw [StarAlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) ∈ (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

end Field

end NonUnitalStarSubalgebra
