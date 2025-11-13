/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Unitization
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
  simp

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
  induction x with
  | inl_add_inr r a =>
    simp_rw [map_add, hf, ← Unitization.algebraMap_eq_inl, AlgHomClass.commutes] at hx
    rw [add_eq_zero_iff_eq_neg] at hx ⊢
    by_cases hr : r = 0
    · ext
      · simp [hr]
      · simpa [hr] using hx
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
    (unitization s).range = subalgebraOfSubsemiring (.closure s) := by
  have := AddSubmonoidClass.nsmulMemClass (S := S)
  rw [unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_nat]

end NonUnitalSubsemiring

/-! ## Subrings -/

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
    (unitization s).range = subalgebraOfSubring (.closure s) := by
  have := AddSubgroupClass.zsmulMemClass (S := S)
  rw [unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_int]

end NonUnitalSubring

/-! ## Star subalgebras -/

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
  simp only [NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass.coe_subtype,
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
