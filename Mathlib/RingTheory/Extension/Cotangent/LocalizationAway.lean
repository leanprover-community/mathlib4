/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Cotangent and localization away

Let `R → S → T` be algebras such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P : R[X] → S` with kernel `I` and
`Q : S[Y] → T` is the canonical `S`-presentation of `T` with kernel `K`.
Denote by `J` the kernel of the composition `R[X,Y] → T`.

This file proves `J/J² ≃ₗ[T] T ⊗[S] (I/I²) × K/K²`. For this we establish the exact sequence:
```
0 → T ⊗[S] (I/I²) → J/J² → K/K² → 0
```
and use that `K/K²` is free, so the sequence splits. The first part of the file
shows the exactness on the left and the rest of the file deduces the exact sequence
and the splitting from the Jacobi Zariski sequence.

## Main results

- `Algebra.Generators.liftBaseChange_injective`:
  `T ⊗[S] (I/I²) → J/J²` is injective if `T` is the localization of `S` away from an element.
- `Algebra.Generators.cotangentCompLocalizationAwayEquiv`: `J/J² ≃ₗ[T] T ⊗[S] (I/I²) × K/K²`.
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

/--
In the notation of the module docstring: Since `T` is standard smooth
of relative dimension one over `S`, `K/K²` is free of rank one generated
by the image of `g * X - 1`.
This is the section `K/K² → J/J²` defined by sending the image of `g * X - 1` to `x : J/J²`.
-/
noncomputable def cotangentCompAwaySec (x : ((localizationAway T g).comp P).toExtension.Cotangent) :
    (localizationAway T g).toExtension.Cotangent →ₗ[T]
      ((localizationAway T g).comp P).toExtension.Cotangent :=
  (basisCotangentAway T g).constr T fun _ ↦ x

variable (x : ((localizationAway T g).comp P).toExtension.Cotangent)

/-- By construction, the section `cotangentCompAwaySec` sends `g * X - 1` to `x`. -/
lemma cotangentCompAwaySec_apply :
    cotangentCompAwaySec g P x (cMulXSubOneCotangent T g) = x := by
  rw [← basisCotangentAway_apply _ (), cotangentCompAwaySec, Module.Basis.constr_basis]

variable {x}
  (hx : Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom x =
    cMulXSubOneCotangent T g)

include hx in
/-- The section `cotangentCompAwaySec` is indeed a section of the canonical map `J/J² → K/K²`. -/
lemma map_comp_cotangentCompAwaySec :
    (Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom) ∘ₗ
      cotangentCompAwaySec g P x = .id := by
  refine (basisCotangentAway T g).ext fun r ↦ ?_
  simpa only [LinearMap.coe_comp, Function.comp_apply, basisCotangentAway_apply,
    cotangentCompAwaySec_apply]

/--
Let `S` be generated over `R` by `P : R[X] → S` with kernel `I` and let `T`
be the localization of `S` away from `g` generated over `S` by `S[Y] → T` with
kernel `K`.
Denote by `J` the kernel of the induced `R[X, Y] → T`. Then
`J/J² ≃ₗ[T] T ⊗[S] (I/I²) × (K/K²)`.

This is the splitting characterised by `x ↦ (0, g * X - 1)`.
-/
@[stacks 08JZ "(1)"]
noncomputable
def cotangentCompLocalizationAwayEquiv :
    ((localizationAway T g).comp P).toExtension.Cotangent ≃ₗ[T]
      T ⊗[S] P.toExtension.Cotangent × (Generators.localizationAway T g).toExtension.Cotangent :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).1

lemma cotangentCompLocalizationAwayEquiv_symm_inr :
    (cotangentCompLocalizationAwayEquiv g P hx).symm
      (0, cMulXSubOneCotangent T g) = x := by
  simpa [cotangentCompLocalizationAwayEquiv, Function.Exact.splitSurjectiveEquiv] using
    cotangentCompAwaySec_apply g P x

lemma cotangentCompLocalizationAwayEquiv_symm_comp_inl :
    (cotangentCompLocalizationAwayEquiv g P hx).symm.toLinearMap ∘ₗ
      .inl T (T ⊗[S] P.toExtension.Cotangent) (localizationAway T g).toExtension.Cotangent =
      .liftBaseChange T
        (Extension.Cotangent.map ((localizationAway T g).toComp P).toExtensionHom) :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x,
      map_comp_cotangentCompAwaySec g P hx⟩).2.left.symm

@[simp]
lemma cotangentCompLocalizationAwayEquiv_symm_inl (a : T ⊗[S] P.toExtension.Cotangent) :
    (cotangentCompLocalizationAwayEquiv g P hx).symm (a, 0) = LinearMap.liftBaseChange T
        (Extension.Cotangent.map ((localizationAway T g).toComp P).toExtensionHom) a := by
  simp [← cotangentCompLocalizationAwayEquiv_symm_comp_inl g P hx]

lemma snd_comp_cotangentCompLocalizationAwayEquiv :
    LinearMap.snd T (T ⊗[S] P.toExtension.Cotangent) (localizationAway T g).toExtension.Cotangent ∘ₗ
      (cotangentCompLocalizationAwayEquiv g P hx).toLinearMap =
      Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom :=
  ((Cotangent.exact (localizationAway T g) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).2.right.symm

@[simp]
lemma snd_cotangentCompLocalizationAwayEquiv
    (a : ((localizationAway T g).comp P).toExtension.Cotangent) :
    (cotangentCompLocalizationAwayEquiv g P hx a).2 =
      Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom a := by
  simp [← snd_comp_cotangentCompLocalizationAwayEquiv g P hx]

end Algebra.Generators
