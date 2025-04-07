/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Presentation
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.CotangentLocalizationAway
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Cotangent and localization away

In this file we use the Jacobi-Zariski sequence to show some results
where `R → S → T` is such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P` with kernel `I` and `Q` is the
canonical `S`-presentation of `T`.

## Main results

- `Algebra.Generators.liftBaseChange_injective`: The map `T ⊗[S] (I⧸I²)` is injective.

-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open TensorProduct MvPolynomial

namespace Algebra.Generators

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (g : S) [IsLocalization.Away g T] (P : Generators R S)

instance : Module.Free T (localizationAway g (S := T)).toExtension.Cotangent :=
  inferInstanceAs <| Module.Free T
    ((SubmersivePresentation.localizationAway g (S := T)).toExtension.Cotangent)

lemma Hom.algebraMap_toAlgHom' {R R' S : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R' S] [Algebra R R'] [IsScalarTower R R' S]
    {P : Generators R S} {P' : Generators R' S} (f : Hom P P') (x) :
    MvPolynomial.aeval P'.val (f.toAlgHom x) = MvPolynomial.aeval P.val x :=
  f.algebraMap_toAlgHom _

noncomputable def cotangentCompAwaySec (x : ((localizationAway g (S := T)).comp P).Ring)
    (hx : ((localizationAway g (S := T)).ofComp P).toAlgHom x = C g * X () - 1) :
    (localizationAway g (S := T)).toExtension.Cotangent →ₗ[T]
      ((localizationAway g (S := T)).comp P).toExtension.Cotangent :=
  have hxmem : (aeval ((localizationAway g).comp P).val) x = 0 := by
    rw [← ((localizationAway g (S := T)).ofComp P).algebraMap_toAlgHom', hx]
    simp [localizationAway]
  (SubmersivePresentation.localizationAway g (S := T)).basisCotangent.constr T
    fun _ ↦ Extension.Cotangent.mk ⟨x, hxmem⟩

lemma cotangentCompAwaySec_apply (x : ((localizationAway g (S := T)).comp P).Ring)
    (hx : ((localizationAway g (S := T)).ofComp P).toAlgHom x = C g * X () - 1) :
    (cotangentCompAwaySec g P x hx)
      (Extension.Cotangent.mk ⟨C g * X () - 1,
        (Presentation.localizationAway g (S := T)).relation_mem_ker ()⟩) =
        Extension.Cotangent.mk ⟨x,
          by
            simp only [toExtension_Ring, RingHom.mem_ker, algebraMap_apply,
              ← ((localizationAway g (S := T)).ofComp P).algebraMap_toAlgHom', hx]
            simp [localizationAway]⟩ := by
  show (cotangentCompAwaySec g P x hx)
    (Extension.Cotangent.mk <|
      ⟨(SubmersivePresentation.localizationAway g (S := T)).relation (),
        (SubmersivePresentation.localizationAway g (S := T)).relation_mem_ker ()⟩) = _
  dsimp only [cotangentCompAwaySec]
  erw [← (SubmersivePresentation.localizationAway g (S := T)).basisCotangent_apply]
  erw [Basis.constr_basis]

lemma map_comp_cotangentCompAwaySec
    (x : ((localizationAway g (S := T)).comp P).Ring)
    (hx : ((localizationAway g (S := T)).ofComp P).toAlgHom x = C g * X () - 1) :
    (Extension.Cotangent.map ((localizationAway g).ofComp P).toExtensionHom) ∘ₗ
      cotangentCompAwaySec g P x hx = .id := by
  apply (SubmersivePresentation.localizationAway g (S := T)).basisCotangent.ext
  intro r
  simp only [toExtension_Ring, toExtension_commRing, toExtension_algebra₂, LinearMap.coe_comp,
    Function.comp_apply, Basis.constr_basis, cotangentCompAwaySec]
  erw [Extension.Cotangent.map_mk]
  simp only [toExtension_Ring, toExtension_commRing, toExtension_algebra₂, Extension.Hom.toAlgHom,
    Hom.toExtensionHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_mk, RingHom.coe_coe, hx]
  simp only [SubmersivePresentation.basisCotangent, toExtension_Ring, toExtension_commRing,
    toExtension_algebra₂, Basis.coe_mk]
  simp
  show Extension.Cotangent.mk _ = (SubmersivePresentation.localizationAway T g).cotangentEquiv.symm
      ((SubmersivePresentation.localizationAway T g).basisDeriv r)
  apply (SubmersivePresentation.localizationAway T g).cotangentEquiv.injective
  ext
  simp [-SubmersivePresentation.cotangentEquiv_apply]
  simp only [SubmersivePresentation.cotangentEquiv_apply]
  erw [PreSubmersivePresentation.cotangentComplexAux_apply]
  rfl

noncomputable
def cotangentCompLocalizationAwayEquiv
    (x : ((localizationAway g (S := T)).comp P).Ring)
    (hx : ((localizationAway g (S := T)).ofComp P).toAlgHom x = C g * X () - 1) :
    ((localizationAway g (S := T)).comp P).toExtension.Cotangent ≃ₗ[T]
      T ⊗[S] P.toExtension.Cotangent ×
        (Generators.localizationAway g (S := T)).toExtension.Cotangent :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x hx,
      map_comp_cotangentCompAwaySec g P x hx⟩).1

variable (x : ((localizationAway g (S := T)).comp P).Ring)
  (hx : ((localizationAway g (S := T)).ofComp P).toAlgHom x = C g * X () - 1)

lemma cotangentCompLocalizationAwayEquiv_symm_inr :
    (cotangentCompLocalizationAwayEquiv (T := T) g P x hx).symm
      (0, Extension.Cotangent.mk ⟨C g * X () - 1,
        (Presentation.localizationAway g (S := T)).relation_mem_ker ()⟩) =
          Extension.Cotangent.mk ⟨x,
            by
              simp only [toExtension_Ring, RingHom.mem_ker, algebraMap_apply,
                ← ((localizationAway g (S := T)).ofComp P).algebraMap_toAlgHom', hx]
              simp [localizationAway]⟩ := by
  simp only [cotangentCompLocalizationAwayEquiv, Function.Exact.splitSurjectiveEquiv,
    Equiv.coe_fn_mk, LinearEquiv.symm_symm,
    LinearEquiv.ofBijective_apply, LinearMap.add_apply, LinearMap.coe_comp, LinearMap.coe_fst,
    Function.comp_apply, map_zero, LinearMap.coe_snd, zero_add,
    cotangentCompAwaySec_apply]

lemma cotangentCompLocalizationAwayEquiv_symm_comp_inl :
    (cotangentCompLocalizationAwayEquiv (T := T) g P x hx).symm.toLinearMap ∘ₗ
      LinearMap.inl T (T ⊗[S] P.toExtension.Cotangent) (localizationAway g).toExtension.Cotangent =
      LinearMap.liftBaseChange T
        (Extension.Cotangent.map ((localizationAway g).toComp P).toExtensionHom) :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x hx,
      map_comp_cotangentCompAwaySec g P x hx⟩).2.left.symm

@[simp]
lemma cotangentCompLocalizationAwayEquiv_symm_inl (a : T ⊗[S] P.toExtension.Cotangent) :
    (cotangentCompLocalizationAwayEquiv (T := T) g P x hx).symm (a, 0) = LinearMap.liftBaseChange T
        (Extension.Cotangent.map ((localizationAway g).toComp P).toExtensionHom) a := by
  rw [← cotangentCompLocalizationAwayEquiv_symm_comp_inl g P x hx]
  simp

lemma snd_comp_cotangentCompLocalizationAwayEquiv :
    LinearMap.snd T (T ⊗[S] P.toExtension.Cotangent) (localizationAway g).toExtension.Cotangent ∘ₗ
      (cotangentCompLocalizationAwayEquiv (T := T) g P x hx).toLinearMap =
      Extension.Cotangent.map ((localizationAway g).ofComp P).toExtensionHom :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x hx,
      map_comp_cotangentCompAwaySec g P x hx⟩).2.right.symm

@[simp]
lemma snd_cotangentCompLocalizationAwayEquiv
    (a : ((localizationAway g).comp P).toExtension.Cotangent) :
    (cotangentCompLocalizationAwayEquiv (T := T) g P x hx a).2 =
      Extension.Cotangent.map ((localizationAway g).ofComp P).toExtensionHom a := by
  rw [← snd_comp_cotangentCompLocalizationAwayEquiv g P x hx]
  simp

@[simp]
lemma _root_.MvPolynomial.aeval_C_comp_left {σ ι R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    (f : σ → S) (p : MvPolynomial σ R) :
    aeval (R := R) (C (σ := ι) ∘ f) p = C (aeval f p) := by
  rw [← MvPolynomial.algebraMap_eq, Function.comp_def]
  simp_rw [← IsScalarTower.toAlgHom_apply R S (MvPolynomial ι S), comp_aeval_apply]

lemma MvPolynomial.coeff_def {σ R : Type*} [CommSemiring R] (m : σ →₀ ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.coeff m p = @DFunLike.coe ((σ →₀ ℕ) →₀ R) _ _ _ p m :=
  rfl

lemma foo (σ A B) [AddMonoid A] [AddCommMonoid B] (f₁ f₂ : σ) (g₁ g₂ : A) (F : σ → A → B)
    (H : f₁ ≠ f₂) (HF : ∀ f, F f 0 = 0) :
    Finsupp.sum (Finsupp.single f₁ g₁ + Finsupp.single f₂ g₂) F = F f₁ g₁ + F f₂ g₂ := by
  classical
  by_cases hg₁ : g₁ = 0
  · simp [hg₁, HF]
  by_cases hg₂ : g₂ = 0
  · simp [hg₂, HF]
  have : (Finsupp.single f₁ g₁ + Finsupp.single f₂ g₂).support = {f₁, f₂} := by
    ext a
    simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq, Finset.mem_insert,
      Finset.mem_singleton, Finsupp.single_apply]
    split_ifs <;> aesop
  simp [Finsupp.sum, this, H, H.symm]

lemma relation_comp_localizationAway_inl (P : Presentation R S)
    (h1 : P.σ (-1) = -1) (h0 : P.σ 0 = 0) (r) :
    ((Presentation.localizationAway T g).comp P).relation (Sum.inl r) =
      rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1 := by
  classical
  simp only [Presentation.comp, Sum.elim_inl, Presentation.comp_relation_aux,
    Presentation.localizationAway_relation]
  rw [sub_eq_add_neg, C_mul_X_eq_monomial, ← map_one C, ← map_neg C]
  refine (foo _ _ _ (Finsupp.single () 1) 0 g (-1 : S) _ ?_ ?_).trans ?_
  · simp
  · simp [h0]
  · simp only [Finsupp.mapDomain_single, h1, map_neg, map_one, Finsupp.mapDomain_zero,
      monomial_zero', C_1, mul_one, sub_eq_add_neg, add_left_inj]
    rfl

lemma toAlgHom_ofComp_localizationAway :
    ((localizationAway (S := T) g).ofComp P).toAlgHom
      ((rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1) = C g * X () - 1 := by
  simp only [Hom.toAlgHom, ofComp, map_sub, map_mul, aeval_X, Sum.elim_inl, map_one, sub_left_inj]
  erw [aeval_rename, Sum.elim_comp_inr]
  simp only [aeval_C_comp_left, aeval_val_σ]
  rfl

end Algebra.Generators
