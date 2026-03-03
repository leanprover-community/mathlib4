/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.DirectSum.Ring

/-!
# Internally-graded rings and algebras

This file defines the typeclass `GradedAlgebra 𝒜`, for working with an algebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → Submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `GradedRing 𝒜`: the typeclass, which is a combination of `SetLike.GradedMonoid`, and
  `DirectSum.Decomposition 𝒜`.
* `GradedAlgebra 𝒜`: A convenience alias for `GradedRing` when `𝒜` is a family of submodules.
* `DirectSum.decomposeRingEquiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `DirectSum.decompose 𝒜`.
* `DirectSum.decomposeAlgEquiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `DirectSum.decompose 𝒜`.
* `GradedAlgebra.proj 𝒜 i` is the linear map from `A` to its degree `i : ι` component, such that
  `proj 𝒜 i x = decompose 𝒜 x i`.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `𝒜 : ι → Submodule ℕ A` and `𝒜 : ι → Submodule ℤ A` respectively, since all
`Semiring`s are ℕ-algebras via `Semiring.toNatAlgebra`, and all `Ring`s are `ℤ`-algebras via
`Ring.toIntAlgebra`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/

@[expose] public section


open DirectSum

variable {ι R A σ : Type*}

section GradedRing

variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)

open DirectSum

/-- An internally-graded `R`-algebra `A` is one that can be decomposed into a collection
of `Submodule R A`s indexed by `ι` such that the canonical map `A → ⨁ i, 𝒜 i` is bijective and
respects multiplication, i.e. the product of an element of degree `i` and an element of degree `j`
is an element of degree `i + j`.

Note that the fact that `A` is internally-graded, `GradedAlgebra 𝒜`, implies an externally-graded
algebra structure `DirectSum.GAlgebra R (fun i ↦ ↥(𝒜 i))`, which in turn makes available an
`Algebra R (⨁ i, 𝒜 i)` instance.
-/
class GradedRing (𝒜 : ι → σ) extends SetLike.GradedMonoid 𝒜, DirectSum.Decomposition 𝒜

variable [GradedRing 𝒜]

namespace DirectSum

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
a ring to a direct sum of components. -/
def decomposeRingEquiv : A ≃+* ⨁ i, 𝒜 i :=
  RingEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := (coeRingHom 𝒜).map_mul }

@[simp]
theorem decompose_one : decompose 𝒜 (1 : A) = 1 :=
  map_one (decomposeRingEquiv 𝒜)

@[simp]
theorem decompose_symm_one : (decompose 𝒜).symm 1 = (1 : A) :=
  map_one (decomposeRingEquiv 𝒜).symm

@[simp]
theorem decompose_mul (x y : A) : decompose 𝒜 (x * y) = decompose 𝒜 x * decompose 𝒜 y :=
  map_mul (decomposeRingEquiv 𝒜) x y

@[simp]
theorem decompose_symm_mul (x y : ⨁ i, 𝒜 i) :
    (decompose 𝒜).symm (x * y) = (decompose 𝒜).symm x * (decompose 𝒜).symm y :=
  map_mul (decomposeRingEquiv 𝒜).symm x y

end DirectSum

/-- The projection maps of a graded ring -/
def GradedRing.proj (i : ι) : A →+ A :=
  (AddSubmonoidClass.subtype (𝒜 i)).comp <|
    (DFinsupp.evalAddMonoidHom i).comp <|
      RingHom.toAddMonoidHom <| RingEquiv.toRingHom <| DirectSum.decomposeRingEquiv 𝒜

@[simp]
theorem GradedRing.proj_apply (i : ι) (r : A) :
    GradedRing.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i :=
  rfl

theorem GradedRing.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
    GradedRing.proj 𝒜 i ((decompose 𝒜).symm a) = (decompose 𝒜).symm (DirectSum.of _ i (a i)) := by
  rw [GradedRing.proj_apply, decompose_symm_of, Equiv.apply_symm_apply]

theorem GradedRing.mem_support_iff [∀ (i) (x : 𝒜 i), Decidable (x ≠ 0)] (r : A) (i : ι) :
    i ∈ (decompose 𝒜 r).support ↔ GradedRing.proj 𝒜 i r ≠ 0 :=
  DFinsupp.mem_support_iff.trans ZeroMemClass.coe_eq_zero.not.symm

end GradedRing

section AddCancelMonoid

open DirectSum

variable [DecidableEq ι] [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable {i j : ι}

namespace DirectSum

theorem coe_decompose_mul_add_of_left_mem [AddLeftCancelMonoid ι] [GradedRing 𝒜] {a b : A}
    (a_mem : a ∈ 𝒜 i) : (decompose 𝒜 (a * b) (i + j) : A) = a * decompose 𝒜 b j := by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul, decompose_coe, coe_of_mul_apply_add]

theorem coe_decompose_mul_add_of_right_mem [AddRightCancelMonoid ι] [GradedRing 𝒜] {a b : A}
    (b_mem : b ∈ 𝒜 j) : (decompose 𝒜 (a * b) (i + j) : A) = decompose 𝒜 a i * b := by
  lift b to 𝒜 j using b_mem
  rw [decompose_mul, decompose_coe, coe_mul_of_apply_add]

theorem decompose_mul_add_left [AddLeftCancelMonoid ι] [GradedRing 𝒜] (a : 𝒜 i) {b : A} :
    decompose 𝒜 (↑a * b) (i + j) =
      @GradedMonoid.GMul.mul ι (fun i => 𝒜 i) _ _ _ _ a (decompose 𝒜 b j) :=
  Subtype.ext <| coe_decompose_mul_add_of_left_mem 𝒜 a.2

theorem decompose_mul_add_right [AddRightCancelMonoid ι] [GradedRing 𝒜] {a : A} (b : 𝒜 j) :
    decompose 𝒜 (a * ↑b) (i + j) =
      @GradedMonoid.GMul.mul ι (fun i => 𝒜 i) _ _ _ _ (decompose 𝒜 a i) b :=
  Subtype.ext <| coe_decompose_mul_add_of_right_mem 𝒜 b.2

theorem coe_decompose_mul_of_left_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b : A}
    (a_mem : a ∈ 𝒜 0) : (decompose 𝒜 (a * b) j : A) = a * decompose 𝒜 b j := by
  lift a to 𝒜 0 using a_mem
  rw [decompose_mul, decompose_coe, coe_of_mul_apply_of_mem_zero]

theorem coe_decompose_mul_of_right_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b : A}
    (b_mem : b ∈ 𝒜 0) : (decompose 𝒜 (a * b) i : A) = decompose 𝒜 a i * b := by
  lift b to 𝒜 0 using b_mem
  rw [decompose_mul, decompose_coe, coe_mul_of_apply_of_mem_zero]

end DirectSum

end AddCancelMonoid

section GradedAlgebra

variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]
variable (𝒜 : ι → Submodule R A)

/-- A special case of `GradedRing` with `σ = Submodule R A`. This is useful both because it
can avoid typeclass search, and because it provides a more concise name. -/
abbrev GradedAlgebra :=
  GradedRing 𝒜

/-- A helper to construct a `GradedAlgebra` when the `SetLike.GradedMonoid` structure is already
available. This makes the `left_inv` condition easier to prove, and phrases the `right_inv`
condition in a way that allows custom `@[ext]` lemmas to apply.

See note [reducible non-instances]. -/
abbrev GradedAlgebra.ofAlgHom [SetLike.GradedMonoid 𝒜] (decompose : A →ₐ[R] ⨁ i, 𝒜 i)
    (right_inv : (DirectSum.coeAlgHom 𝒜).comp decompose = AlgHom.id R A)
    (left_inv : ∀ i (x : 𝒜 i), decompose (x : A) = DirectSum.of (fun i => ↥(𝒜 i)) i x) :
    GradedAlgebra 𝒜 where
  decompose' := decompose
  left_inv := AlgHom.congr_fun right_inv
  right_inv := by
    suffices decompose.comp (DirectSum.coeAlgHom 𝒜) = AlgHom.id _ _ from AlgHom.congr_fun this
    ext i x : 2
    exact (decompose.congr_arg <| DirectSum.coeAlgHom_of _ _ _).trans (left_inv i x)

variable [GradedAlgebra 𝒜]

namespace DirectSum

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
an algebra to a direct sum of components. -/
-- We have to write the `@[simps]` lemmas by hand to see through the
-- `AlgEquiv.symm (decomposeAddEquiv 𝒜).symm`.
def decomposeAlgEquiv : A ≃ₐ[R] ⨁ i, 𝒜 i :=
  AlgEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := map_mul (coeAlgHom 𝒜)
      commutes' := (coeAlgHom 𝒜).commutes }

@[simp]
lemma decomposeAlgEquiv_apply (a : A) :
    decomposeAlgEquiv 𝒜 a = decompose 𝒜 a := rfl

@[simp]
lemma decomposeAlgEquiv_symm_apply (a : ⨁ i, 𝒜 i) :
    (decomposeAlgEquiv 𝒜).symm a = (decompose 𝒜).symm a := rfl

@[simp]
lemma decompose_algebraMap (r : R) :
    decompose 𝒜 (algebraMap R A r) = algebraMap R (⨁ i, 𝒜 i) r :=
  (decomposeAlgEquiv 𝒜).commutes r

@[simp]
lemma decompose_symm_algebraMap (r : R) :
    (decompose 𝒜).symm (algebraMap R (⨁ i, 𝒜 i) r) = algebraMap R A r :=
  (decomposeAlgEquiv 𝒜).symm.commutes r

end DirectSum

open DirectSum

/-- The projection maps of graded algebra -/
def GradedAlgebra.proj (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (i : ι) : A →ₗ[R] A :=
  (𝒜 i).subtype.comp <| (DFinsupp.lapply i).comp <| (decomposeAlgEquiv 𝒜).toAlgHom.toLinearMap

@[simp]
theorem GradedAlgebra.proj_apply (i : ι) (r : A) :
    GradedAlgebra.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i :=
  rfl

theorem GradedAlgebra.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
    GradedAlgebra.proj 𝒜 i ((decompose 𝒜).symm a) = (decompose 𝒜).symm (of _ i (a i)) := by
  rw [GradedAlgebra.proj_apply, decompose_symm_of, Equiv.apply_symm_apply]

theorem GradedAlgebra.mem_support_iff [DecidableEq A] (r : A) (i : ι) :
    i ∈ (decompose 𝒜 r).support ↔ GradedAlgebra.proj 𝒜 i r ≠ 0 :=
  DFinsupp.mem_support_iff.trans Submodule.coe_eq_zero.not.symm

end GradedAlgebra

section CanonicalOrder

open SetLike.GradedMonoid DirectSum

variable [Semiring A] [DecidableEq ι]
variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- If `A` is graded by a canonically ordered additive monoid, then the projection map `x ↦ x₀`
is a ring homomorphism.
-/
@[simps]
def GradedRing.projZeroRingHom : A →+* A where
  toFun a := decompose 𝒜 a 0
  map_one' := decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem
  map_zero' := by rw [decompose_zero, zero_apply, ZeroMemClass.coe_zero]
  map_add' _ _ := by rw [decompose_add, add_apply, AddMemClass.coe_add]
  map_mul' := by
    refine DirectSum.Decomposition.inductionOn 𝒜 (fun x => ?_) ?_ ?_
    · simp only [zero_mul, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rintro i ⟨c, hc⟩
      refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
      · simp only [mul_zero, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
      · rintro j ⟨c', hc'⟩
        simp only
        by_cases h : i + j = 0
        · rw [decompose_of_mem_same 𝒜
              (show c * c' ∈ 𝒜 0 from h ▸ SetLike.GradedMul.mul_mem hc hc'),
            decompose_of_mem_same 𝒜 (show c ∈ 𝒜 0 from (add_eq_zero.mp h).1 ▸ hc),
            decompose_of_mem_same 𝒜 (show c' ∈ 𝒜 0 from (add_eq_zero.mp h).2 ▸ hc')]
        · rw [decompose_of_mem_ne 𝒜 (SetLike.GradedMul.mul_mem hc hc') h]
          rcases show i ≠ 0 ∨ j ≠ 0 by rwa [add_eq_zero, not_and_or] at h with h' | h'
          · simp only [decompose_of_mem_ne 𝒜 hc h', zero_mul]
          · simp only [decompose_of_mem_ne 𝒜 hc' h', mul_zero]
      · intro _ _ hd he
        simp only [mul_add, decompose_add, add_apply, AddMemClass.coe_add, hd, he]
    · rintro _ _ ha hb _
      simp only [add_mul, decompose_add, add_apply, AddMemClass.coe_add, ha, hb]

section GradeZero

/-- The ring homomorphism from `A` to `𝒜 0` sending every `a : A` to `a₀`. -/
def GradedRing.projZeroRingHom' : A →+* 𝒜 0 :=
  ((GradedRing.projZeroRingHom 𝒜).codRestrict _ fun _x => SetLike.coe_mem _ :
  A →+* SetLike.GradeZero.subsemiring 𝒜)

@[simp] lemma GradedRing.coe_projZeroRingHom'_apply (a : A) :
    (GradedRing.projZeroRingHom' 𝒜 a : A) = GradedRing.projZeroRingHom 𝒜 a := rfl

@[simp] lemma GradedRing.projZeroRingHom'_apply_coe (a : 𝒜 0) :
    GradedRing.projZeroRingHom' 𝒜 a = a := by
  ext; simp only [coe_projZeroRingHom'_apply, projZeroRingHom_apply, decompose_coe, of_eq_same]

/-- The ring homomorphism `GradedRing.projZeroRingHom' 𝒜` is surjective. -/
lemma GradedRing.projZeroRingHom'_surjective :
    Function.Surjective (GradedRing.projZeroRingHom' 𝒜) :=
  Function.RightInverse.surjective (GradedRing.projZeroRingHom'_apply_coe 𝒜)

end GradeZero

variable {a b : A} {n i : ι}

namespace DirectSum

theorem coe_decompose_mul_of_left_mem_of_not_le (a_mem : a ∈ 𝒜 i) (h : ¬i ≤ n) :
    (decompose 𝒜 (a * b) n : A) = 0 := by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_not_le]

theorem coe_decompose_mul_of_right_mem_of_not_le (b_mem : b ∈ 𝒜 i) (h : ¬i ≤ n) :
    (decompose 𝒜 (a * b) n : A) = 0 := by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_not_le]

variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]

theorem coe_decompose_mul_of_left_mem_of_le (a_mem : a ∈ 𝒜 i) (h : i ≤ n) :
    (decompose 𝒜 (a * b) n : A) = a * decompose 𝒜 b (n - i) := by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_le]

theorem coe_decompose_mul_of_right_mem_of_le (b_mem : b ∈ 𝒜 i) (h : i ≤ n) :
    (decompose 𝒜 (a * b) n : A) = decompose 𝒜 a (n - i) * b := by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_le]

theorem coe_decompose_mul_of_left_mem (n) [Decidable (i ≤ n)] (a_mem : a ∈ 𝒜 i) :
    (decompose 𝒜 (a * b) n : A) = if i ≤ n then a * decompose 𝒜 b (n - i) else 0 := by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul, decompose_coe, coe_of_mul_apply]

theorem coe_decompose_mul_of_right_mem (n) [Decidable (i ≤ n)] (b_mem : b ∈ 𝒜 i) :
    (decompose 𝒜 (a * b) n : A) = if i ≤ n then decompose 𝒜 a (n - i) * b else 0 := by
  lift b to 𝒜 i using b_mem
  rw [decompose_mul, decompose_coe, coe_mul_of_apply]

end DirectSum

end CanonicalOrder

namespace DirectSum.IsInternal

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {M : ι → Submodule R A} [SetLike.GradedMonoid M]

-- The following lines were given on Zulip by Adam Topaz
/-- The canonical isomorphism of an internal direct sum with the ambient algebra -/
noncomputable def coeAlgEquiv (hM : DirectSum.IsInternal M) :
    (DirectSum ι fun i => ↥(M i)) ≃ₐ[R] A :=
  { RingEquiv.ofBijective (DirectSum.coeAlgHom M) hM with commutes' := fun r => by simp }

/-- Given an `R`-algebra `A` and a family `ι → Submodule R A` of submodules
parameterized by an additive monoid `ι`
and satisfying `SetLike.GradedMonoid M` (essentially, is multiplicative)
such that `DirectSum.IsInternal M` (`A` is the direct sum of the `M i`),
we endow `A` with the structure of a graded algebra.
The submodules are the *homogeneous* parts. -/
@[implicit_reducible]
noncomputable def gradedAlgebra (hM : DirectSum.IsInternal M) : GradedAlgebra M :=
  { (inferInstance : SetLike.GradedMonoid M) with
    decompose' := hM.coeAlgEquiv.symm
    left_inv := hM.coeAlgEquiv.symm.left_inv
    right_inv := hM.coeAlgEquiv.left_inv }

end DirectSum.IsInternal
