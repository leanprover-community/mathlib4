/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Cotangent and localization away

Let `R → S → T` be algebras such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P` with kernel `I` and `Q` is the
canonical `S`-presentation of `T`. Denote by `J` the kernel of the composition
`R[X,Y] → T`.

## Main results

- `Algebra.Generators.liftBaseChange_injective`:
  `T ⊗[S] (I/I²) → J/J²` is injective if `T` is the localization of `S` away from an element.

-/

open TensorProduct MvPolynomial

namespace Algebra.Generators

variable {R S T ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (g : S) [IsLocalization.Away g T] (P : Generators R S ι)

lemma comp_localizationAway_ker (P : Generators R S ι) (f : P.Ring)
    (h : algebraMap P.Ring S f = g) :
    ((Generators.localizationAway T g).comp P).ker =
      Ideal.map ((Generators.localizationAway T g).toComp P).toAlgHom P.ker ⊔
        Ideal.span {rename Sum.inr f * X (Sum.inl ()) - 1} := by
  have : (localizationAway T g).ker = Ideal.map ((localizationAway T g).ofComp P).toAlgHom
      (Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1}) := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_mul, map_one, ker_localizationAway,
      Hom.toAlgHom_X, toAlgHom_ofComp_rename, h, ofComp_val, Sum.elim_inl]
  rw [ker_comp_eq_sup, Algebra.Generators.map_toComp_ker, this,
    Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective _ P), ← RingHom.ker_eq_comap_bot,
    ← sup_assoc]
  simp

variable (T) in
/-- If `R[X] → S` generates `S`, `T` is the localization of `S` away from `g` and
`f` is a pre-image of `g` in `R[X]`, this is the `R`-algebra map `R[X,Y] →ₐ[R] (R[X]/I²)[1/f]`
defined via mapping `Y` to `1/f`. -/
noncomputable
def compLocalizationAwayAlgHom : ((Generators.localizationAway T g).comp P).Ring →ₐ[R]
      Localization.Away (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)) :=
  aeval (R := R) (S₁ := Localization.Away _)
    (Sum.elim
      (fun _ ↦ IsLocalization.Away.invSelf <| (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)))
      (fun i : ι ↦ algebraMap P.Ring _ (X i)))

@[simp]
lemma compLocalizationAwayAlgHom_toAlgHom_toComp (x : P.Ring) :
    compLocalizationAwayAlgHom T g P (((localizationAway T g).toComp P).toAlgHom x) =
      algebraMap P.Ring _ x := by
  simp only [toComp_toAlgHom, compLocalizationAwayAlgHom, comp,
    localizationAway, AlgHom.toRingHom_eq_coe, aeval_rename,
    Sum.elim_comp_inr, ← IsScalarTower.toAlgHom_apply (R := R), ← comp_aeval_apply,
    aeval_X_left_apply]

@[simp]
lemma compLocalizationAwayAlgHom_X_inl : compLocalizationAwayAlgHom T g P (X (Sum.inl ())) =
      IsLocalization.Away.invSelf ((Ideal.Quotient.mk (P.ker ^ 2)) (P.σ g)) := by
  simp [compLocalizationAwayAlgHom]

lemma compLocalizationAwayAlgHom_relation_eq_zero :
    compLocalizationAwayAlgHom T g P (rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1) = 0 := by
  rw [map_sub, map_one, map_mul, ← toComp_toAlgHom (Generators.localizationAway T g) P]
  change (compLocalizationAwayAlgHom T g P)
    (((localizationAway T g).toComp P).toAlgHom _) * _ - _ = _
  rw [compLocalizationAwayAlgHom_toAlgHom_toComp, compLocalizationAwayAlgHom_X_inl,
    IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away _)]
  simp

lemma sq_ker_comp_le_ker_compLocalizationAwayAlgHom :
    ((localizationAway T g).comp P).ker ^ 2 ≤
      RingHom.ker (compLocalizationAwayAlgHom T g P) := by
  have hsple {x} (hx : x ∈ Ideal.span {(rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1}) :
        (compLocalizationAwayAlgHom T g P) x = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, compLocalizationAwayAlgHom_relation_eq_zero, zero_mul]
  rw [comp_localizationAway_ker _ _ (P.σ g) (by simp), sq, Ideal.sup_mul, Ideal.mul_sup,
    Ideal.mul_sup]
  apply sup_le
  · apply sup_le
    · rw [← Ideal.map_mul, Ideal.map_le_iff_le_comap, ← sq]
      intro x hx
      simp only [Ideal.mem_comap, RingHom.mem_ker,
        compLocalizationAwayAlgHom_toAlgHom_toComp (T := T) g P x]
      rw [IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away _),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    · rw [Ideal.mul_le]
      intro x hx y hy
      simp [hsple hy]
  · apply sup_le <;>
    · rw [Ideal.mul_le]
      intro x hx y hy
      simp [hsple hx]

/--
Let `R → S → T` be algebras such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P` with kernel `I` and `Q` is the
canonical `S`-presentation of `T`. Denote by `J` the kernel of the composition
`R[X,Y] → T`. Then `T ⊗[S] (I/I²) → J/J²` is injective.
-/
@[stacks 08JZ "part of (1)"]
lemma liftBaseChange_injective_of_isLocalizationAway :
    Function.Injective (LinearMap.liftBaseChange T
      (Extension.Cotangent.map
        ((Generators.localizationAway T g).toComp P).toExtensionHom)) := by
  set Q := Generators.localizationAway T g
  algebraize [((Generators.localizationAway T g).toComp P).toAlgHom.toRingHom]
  let f : P.Ring ⧸ P.ker ^ 2 := P.σ g
  let π := compLocalizationAwayAlgHom T g P
  refine IsLocalizedModule.injective_of_map_zero (Submonoid.powers g)
    (TensorProduct.mk S T P.toExtension.Cotangent 1) (fun x hx ↦ ?_)
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  suffices h : algebraMap P.Ring (Localization.Away f) x.val = 0 by
    rw [IsScalarTower.algebraMap_apply _ (P.Ring ⧸ P.ker ^ 2) _,
      IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f)] at h
    obtain ⟨⟨m, ⟨n, rfl⟩⟩, hm⟩ := h
    rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers g)]
    use ⟨g ^ n, n, rfl⟩
    dsimp [f] at hm
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm
    simp only [Submonoid.smul_def]
    rw [show g = algebraMap P.Ring S (P.σ g) by simp, ← map_pow, algebraMap_smul, ← map_smul,
      Extension.Cotangent.mk_eq_zero_iff]
    simpa using hm
  rw [← compLocalizationAwayAlgHom_toAlgHom_toComp (T := T)]
  apply sq_ker_comp_le_ker_compLocalizationAwayAlgHom
  simpa only [LinearEquiv.coe_coe, LinearMap.ringLmapEquivSelf_symm_apply,
    mk_apply, lift.tmul, LinearMap.coe_restrictScalars, LinearMap.coe_smulRight,
    Module.End.one_apply, LinearMap.smul_apply, one_smul, Algebra.Extension.Cotangent.map_mk,
    Extension.Cotangent.mk_eq_zero_iff] using hx

end Algebra.Generators
