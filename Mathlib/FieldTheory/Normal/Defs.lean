/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Thomas Browning, Patrick Lutz
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Normal field extensions

In this file we define normal field extensions.

## Main Definitions

- `Normal F K` where `K` is a field extension of `F`.
-/

noncomputable section

open Polynomial IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- Typeclass for normal field extensions: an algebraic extension of fields `K/F` is *normal*
if the minimal polynomial of every element `x` in `K` splits in `K`, i.e. every `F`-conjugate
of `x` is in `K`. -/
@[stacks 09HM]
class Normal : Prop extends Algebra.IsAlgebraic F K where
  splits' (x : K) : Splits (algebraMap F K) (minpoly F x)

variable {F K}

theorem Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegral F x :=
  Algebra.IsIntegral.isIntegral x

theorem Normal.splits (_ : Normal F K) (x : K) : Splits (algebraMap F K) (minpoly F x) :=
  Normal.splits' x

theorem normal_iff : Normal F K ↔ ∀ x : K, IsIntegral F x ∧ Splits (algebraMap F K) (minpoly F x) :=
  ⟨fun h x => ⟨h.isIntegral x, h.splits x⟩, fun h =>
    { isAlgebraic := fun x => (h x).1.isAlgebraic
      splits' := fun x => (h x).2 }⟩

theorem Normal.out : Normal F K → ∀ x : K, IsIntegral F x ∧ Splits (algebraMap F K) (minpoly F x) :=
  normal_iff.1

variable (F K)

instance normal_self : Normal F F where
  isAlgebraic := fun _ => isIntegral_algebraMap.isAlgebraic
  splits' := fun x => (minpoly.eq_X_sub_C' x).symm ▸ splits_X_sub_C _

section NormalTower

variable (E : Type*) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

@[stacks 09HN]
theorem Normal.tower_top_of_normal [h : Normal F E] : Normal K E :=
  normal_iff.2 fun x => by
    obtain ⟨hx, hhx⟩ := h.out x
    rw [algebraMap_eq F K E] at hhx
    exact
      ⟨hx.tower_top,
        Polynomial.splits_of_splits_of_dvd (algebraMap K E)
          (Polynomial.map_ne_zero (minpoly.ne_zero hx))
          ((Polynomial.splits_map_iff (algebraMap F K) (algebraMap K E)).mpr hhx)
          (minpoly.dvd_map_of_isScalarTower F K x)⟩

theorem AlgHom.normal_bijective [h : Normal F E] (ϕ : E →ₐ[F] K) : Function.Bijective ϕ :=
  h.toIsAlgebraic.bijective_of_isScalarTower' ϕ

variable {E F}
variable {E' : Type*} [Field E'] [Algebra F E']

theorem Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E') : Normal F E' := by
  rw [normal_iff] at h ⊢
  intro x; specialize h (f.symm x)
  rw [← f.apply_symm_apply x, minpoly.algEquiv_eq, ← f.toAlgHom.comp_algebraMap]
  exact ⟨h.1.map f, splits_comp_of_splits _ _ h.2⟩

theorem AlgEquiv.transfer_normal (f : E ≃ₐ[F] E') : Normal F E ↔ Normal F E' :=
  ⟨fun _ ↦ Normal.of_algEquiv f, fun _ ↦ Normal.of_algEquiv f.symm⟩

theorem Normal.of_equiv_equiv {M N : Type*} [Field N] [Field M] [Algebra M N]
    [Algebra.IsAlgebraic F E] [h : Normal F E] {f : F ≃+* M} {g : E ≃+* N}
    (hcomp : (algebraMap M N).comp f = (g : E →+* N).comp (algebraMap F E)) :
    Normal M N := by
  rw [normal_iff] at h ⊢
  intro x
  rw [← g.apply_symm_apply x]
  refine ⟨(h (g.symm x)).1.map_of_comp_eq _ _ hcomp, ?_⟩
  rw [← minpoly.map_eq_of_equiv_equiv hcomp, Polynomial.splits_map_iff, hcomp]
  exact Polynomial.splits_comp_of_splits _ _ (h (g.symm x)).2

end NormalTower

namespace IntermediateField

variable {F K}
variable {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]

@[simp]
theorem restrictScalars_normal {E : IntermediateField K L} :
    Normal F (E.restrictScalars F) ↔ Normal F E :=
  Iff.rfl

end IntermediateField

variable {F} {K}
variable {K₁ K₂ K₃ : Type*} [Field K₁] [Field K₂] [Field K₃] [Algebra F K₁]
  [Algebra F K₂] [Algebra F K₃] (ϕ : K₁ →ₐ[F] K₂) (χ : K₁ ≃ₐ[F] K₂) (ψ : K₂ →ₐ[F] K₃)
  (ω : K₂ ≃ₐ[F] K₃)

section Restrict

variable (E : Type*) [Field E] [Algebra F E] [Algebra E K₁] [Algebra E K₂] [Algebra E K₃]
  [IsScalarTower F E K₁] [IsScalarTower F E K₂] [IsScalarTower F E K₃]

/-- Restrict algebra homomorphism to image of normal subfield -/
def AlgHom.restrictNormalAux [h : Normal F E] :
    (toAlgHom F E K₁).range →ₐ[F] (toAlgHom F E K₂).range where
  toFun x :=
    ⟨ϕ x, by
      suffices (toAlgHom F E K₁).range.map ϕ ≤ _ by exact this ⟨x, Subtype.mem x, rfl⟩
      rintro x ⟨y, ⟨z, hy⟩, hx⟩
      rw [← hx, ← hy]
      apply minpoly.mem_range_of_degree_eq_one E
      refine
        Or.resolve_left (h.splits z).def (minpoly.ne_zero (h.isIntegral z)) (minpoly.irreducible ?_)
          (minpoly.dvd E _ (by simp [aeval_algHom_apply]))
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      suffices IsIntegral F _ by exact this.tower_top
      exact ((h.isIntegral z).map <| toAlgHom F E K₁).map ϕ⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext <| by simp
  map_mul' x y := Subtype.ext <| by simp
  commutes' x := Subtype.ext (ϕ.commutes x)

/-- Restrict algebra homomorphism to normal subfield. -/
@[stacks 0BME "Part 1"]
def AlgHom.restrictNormal [Normal F E] : E →ₐ[F] E :=
  ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂)).symm.toAlgHom.comp
        (ϕ.restrictNormalAux E)).comp
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₁)).toAlgHom

/-- Restrict algebra homomorphism to normal subfield (`AlgEquiv` version) -/
def AlgHom.restrictNormal' [Normal F E] : Gal(E/F) :=
  AlgEquiv.ofBijective (AlgHom.restrictNormal ϕ E) (AlgHom.normal_bijective F E E _)

@[simp]
theorem AlgHom.restrictNormal_commutes [Normal F E] (x : E) :
    algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x) :=
  Subtype.ext_iff.mp
    (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂))
      (ϕ.restrictNormalAux E ⟨IsScalarTower.toAlgHom F E K₁ x, x, rfl⟩))

theorem AlgHom.restrictNormal_comp [Normal F E] :
    (ψ.restrictNormal E).comp (ϕ.restrictNormal E) = (ψ.comp ϕ).restrictNormal E :=
  AlgHom.ext fun _ =>
    (algebraMap E K₃).injective (by simp only [AlgHom.comp_apply, AlgHom.restrictNormal_commutes])

/-- Restrict algebra isomorphism to a normal subfield -/
def AlgEquiv.restrictNormal [Normal F E] : Gal(E/F) :=
  AlgHom.restrictNormal' χ.toAlgHom E

@[simp]
theorem AlgEquiv.restrictNormal_commutes [Normal F E] (x : E) :
    algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x) :=
  χ.toAlgHom.restrictNormal_commutes E x

theorem AlgEquiv.restrictNormal_trans [Normal F E] :
    (χ.trans ω).restrictNormal E = (χ.restrictNormal E).trans (ω.restrictNormal E) :=
  AlgEquiv.ext fun _ =>
    (algebraMap E K₃).injective
      (by simp only [AlgEquiv.trans_apply, AlgEquiv.restrictNormal_commutes])

/-- Restriction to a normal subfield as a group homomorphism -/
def AlgEquiv.restrictNormalHom [Normal F E] : Gal(K₁/F) →* Gal(E/F) :=
  MonoidHom.mk' (fun χ => χ.restrictNormal E) fun ω χ => χ.restrictNormal_trans ω E

lemma AlgEquiv.restrictNormalHom_apply (L : IntermediateField F K₁) [Normal F L]
    (σ : Gal(K₁/F)) (x : L) : restrictNormalHom L σ x = σ x :=
  AlgEquiv.restrictNormal_commutes σ L x

variable (F K₁)

/-- If `K₁/E/F` is a tower of fields with `E/F` normal then `AlgHom.restrictNormal'` is an
equivalence. -/
@[simps, stacks 0BR4]
def Normal.algHomEquivAut [Normal F E] : (E →ₐ[F] K₁) ≃ Gal(E/F) where
  toFun σ := AlgHom.restrictNormal' σ E
  invFun σ := (IsScalarTower.toAlgHom F E K₁).comp σ.toAlgHom
  left_inv σ := by
    ext
    simp [AlgHom.restrictNormal']
  right_inv σ := by
    ext
    simp only [AlgHom.restrictNormal', AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_ofBijective]
    apply FaithfulSMul.algebraMap_injective E K₁
    rw [AlgHom.restrictNormal_commutes]
    simp

end Restrict

section lift

/-- The group homomorphism given by restricting an algebra isomorphism to itself
is the identity map. -/
@[simp]
theorem AlgEquiv.restrictNormalHom_id (F K : Type*)
    [Field F] [Field K] [Algebra F K] [Normal F K] :
    AlgEquiv.restrictNormalHom K = MonoidHom.id Gal(K/F) := by
  ext f x
  dsimp only [restrictNormalHom, MonoidHom.mk'_apply, MonoidHom.id_apply]
  apply (algebraMap K K).injective
  rw [AlgEquiv.restrictNormal_commutes]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

namespace IsScalarTower

/-- In a scalar tower `K₃/K₂/K₁/F` with `K₁` and `K₂` are normal over `F`, the group homomorphism
given by the restriction of algebra isomorphisms of `K₃` to `K₁` is equal to the composition of
the group homomorphism given by the restricting an algebra isomorphism of `K₃` to `K₂` and
the group homomorphism given by the restricting an algebra isomorphism of `K₂` to `K₁` -/
theorem AlgEquiv.restrictNormalHom_comp (F K₁ K₂ K₃ : Type*)
    [Field F] [Field K₁] [Field K₂] [Field K₃]
    [Algebra F K₁] [Algebra F K₂] [Algebra F K₃] [Algebra K₁ K₂] [Algebra K₁ K₃] [Algebra K₂ K₃]
    [IsScalarTower F K₁ K₃] [IsScalarTower F K₁ K₂] [IsScalarTower F K₂ K₃] [IsScalarTower K₁ K₂ K₃]
    [Normal F K₁] [Normal F K₂] :
    AlgEquiv.restrictNormalHom K₁ =
    (AlgEquiv.restrictNormalHom K₁).comp
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := K₃) K₂) := by
  ext f x
  apply (algebraMap K₁ K₃).injective
  rw [IsScalarTower.algebraMap_eq K₁ K₂ K₃]
  simp only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, RingHom.coe_comp, Function.comp_apply,
    ← algebraMap_apply, AlgEquiv.restrictNormal_commutes, MonoidHom.coe_comp]

theorem AlgEquiv.restrictNormalHom_comp_apply (K₁ K₂ : Type*) {F K₃ : Type*}
    [Field F] [Field K₁] [Field K₂] [Field K₃]
    [Algebra F K₁] [Algebra F K₂] [Algebra F K₃] [Algebra K₁ K₂] [Algebra K₁ K₃] [Algebra K₂ K₃]
    [IsScalarTower F K₁ K₃] [IsScalarTower F K₁ K₂] [IsScalarTower F K₂ K₃] [IsScalarTower K₁ K₂ K₃]
    [Normal F K₁] [Normal F K₂] (f : K₃ ≃ₐ[F] K₃) :
    AlgEquiv.restrictNormalHom K₁ f =
    (AlgEquiv.restrictNormalHom K₁) (AlgEquiv.restrictNormalHom K₂ f) := by
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp F K₁ K₂ K₃, MonoidHom.comp_apply]

end IsScalarTower

end lift
