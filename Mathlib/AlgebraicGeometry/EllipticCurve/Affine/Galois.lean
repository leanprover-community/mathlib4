/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Galois.Basic

/-!
# The Galois action on nonsingular points in affine coordinates

Let `W` be a Weierstrass curve defined over a subring of a ring `S`, and let `F` be a field
extension of `S`. The group `F ≃ₐ[S] F` of `S`-algebra automorphisms of `F` acts on the group of
nonsingular `F`-points of `W` in affine coordinates, by fixing the point at infinity and by acting
on the coordinates of a nonsingular affine point.

If `K` is a further field extension of `F`, then the image of the base change homomorphism
`WeierstrassCurve.Affine.Point.baseChange F K` always lands in the subgroup of nonsingular
`K`-points fixed by the natural action of `K ≃ₐ[F] K`. When `K / F` is a finite Galois extension,
this file shows that its image is precisely that subgroup, which is a special case of Galois
descent.

## Main definitions

* `WeierstrassCurve.Affine.Point.instDistribMulActionPoint`: the action of `F ≃ₐ[S] F` on the group
  of nonsingular `F`-points of a Weierstrass curve in affine coordinates.
* `WeierstrassCurve.Affine.Point.baseChangeFixedPointsRestrict`: the group homomorphism from the
  nonsingular `F`-points to the subgroup of nonsingular `K`-points fixed by `K ≃ₐ[F] K`.

## Main statements

* `WeierstrassCurve.Affine.Point.baseChange_range_le_fixedSubgroup`: the range of the base change
  homomorphism is contained in the subgroup of nonsingular `K`-points fixed by `K ≃ₐ[F] K`.
* `WeierstrassCurve.Affine.Point.baseChange_range_eq_fixedPoints`: if `K / F` is a finite Galois
  extension, then the range of the base change homomorphism is precisely the subgroup of
  nonsingular `K`-points fixed by `K ≃ₐ[F] K`.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, affine, point, group law, Galois
-/

@[expose] public section

namespace WeierstrassCurve.Affine.Point

variable {R : Type*} [CommRing R] {W' : Affine R} {S : Type*} [CommRing S] {F : Type*} [Field F]
  [DecidableEq F] {K : Type*} [Field K] [DecidableEq K]

section DistribMulAction

variable [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]

/-- The action of the group of `S`-algebra automorphisms of `F` on the group of nonsingular
`F`-points of a Weierstrass curve `W` in affine coordinates, where `W` is defined over a subring of
a ring `S`, and `F` is a field extension of `S`. -/
noncomputable instance instDistribMulActionPoint : DistribMulAction (F ≃ₐ[S] F) (W'⁄F).Point where
  smul σ := map σ.toAlgHom
  one_smul := by rintro (_ | _) <;> rfl
  mul_smul _ _ := by rintro (_ | _) <;> rfl
  smul_zero _ := rfl
  smul_add σ := _root_.map_add (map σ.toAlgHom)

@[simp]
lemma smul_def (P : (W'⁄F).Point) (σ : F ≃ₐ[S] F) : σ • P = map σ.toAlgHom P :=
  rfl

end DistribMulAction

section Galois

variable (F K) [Algebra R F] [Algebra R K] [Algebra F K] [IsScalarTower R F K]

lemma smul_baseChange (P : (W'⁄F).Point) (σ : K ≃ₐ[F] K) :
    σ • baseChange F K P = baseChange F K P :=
  map_baseChange σ.toAlgHom P

/-- The group homomorphism from the nonsingular `F`-points of a Weierstrass curve `W` in affine
coordinates to the subgroup of nonsingular `K`-points fixed by the natural action of the group of
`F`-algebra automorphisms of `K`, induced by `WeierstrassCurve.Affine.Point.baseChange F K`. -/
noncomputable abbrev baseChangeFixedPointsRestrict :
    (W'⁄F).Point →+ FixedPoints.addSubgroup (K ≃ₐ[F] K) (W'⁄K).Point :=
  (baseChange F K).codRestrict (FixedPoints.addSubgroup (K ≃ₐ[F] K) (W'⁄K).Point) <|
    smul_baseChange F K

@[simp]
lemma baseChangeFixedPointsRestrict_comp :
    (FixedPoints.addSubgroup (K ≃ₐ[F] K) (W'⁄K).Point).subtype.comp
      (baseChangeFixedPointsRestrict (W' := W') F K) = baseChange F K :=
  rfl

@[simp]
lemma baseChangeFixedPointsRestrict_apply (P : (W'⁄F).Point) :
    (FixedPoints.addSubgroup (K ≃ₐ[F] K) (W'⁄K).Point).subtype
      (baseChangeFixedPointsRestrict F K P) = baseChange F K P :=
  rfl

lemma baseChangeFixedPointsRestrict_injective :
    Function.Injective <| baseChangeFixedPointsRestrict (W' := W') F K :=
  fun _ _ h ↦ map_injective (W' := W') (Algebra.ofId F K) <| Subtype.ext_iff.mp h

lemma baseChange_range_le_fixedSubgroup :
    (baseChange F K (W' := W')).range ≤ FixedPoints.addSubgroup (K ≃ₐ[F] K) (W'⁄K).Point := by
  rw [← baseChangeFixedPointsRestrict_comp]
  exact (baseChangeFixedPointsRestrict F K).subtype_comp_range_le

-- `FiniteDimensional` is unnecessary with infinite Galois theory
variable [FiniteDimensional F K] [IsGalois F K]

lemma baseChangeFixedPointsRestrict_surjective :
    Function.Surjective <| baseChangeFixedPointsRestrict (W' := W') F K := by
  rintro ⟨_ | ⟨x, y, hxy⟩, h⟩
  · exact ⟨0, rfl⟩
  · simp only [FixedPoints.mem_addSubgroup, smul_def, map_some, some.injEq,
      AlgEquiv.coe_toAlgHom] at h
    rcases (IsGalois.mem_range_algebraMap_iff_fixed (F := F) x).mpr fun σ ↦ (h σ).left with ⟨x, rfl⟩
    rcases (IsGalois.mem_range_algebraMap_iff_fixed (F := F) y).mpr fun σ ↦ (h σ).right with
      ⟨y, rfl⟩
    exact ⟨some _ _ <| (W'.baseChange_nonsingular (f := Algebra.ofId F K)
      (algebraMap F K).injective x y).mp hxy, rfl⟩

lemma baseChange_range_eq_fixedPoints :
    (baseChange F K (W' := W')).range = FixedPoints.addSubgroup (K ≃ₐ[F] K) (W'⁄K).Point := by
  rw [← baseChangeFixedPointsRestrict_comp]
  exact AddMonoidHom.subtype_comp_range_eq <| baseChangeFixedPointsRestrict_surjective F K

end Galois

end WeierstrassCurve.Affine.Point
