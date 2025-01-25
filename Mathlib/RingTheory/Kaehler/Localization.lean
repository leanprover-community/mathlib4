/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Presentation
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
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

open TensorProduct MvPolynomial

namespace Algebra.Generators

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (g : S) [IsLocalization.Away g T] (P : Generators R S)

lemma comp_localizationAway_ker (P : Generators R S) (f : P.Ring) (h : algebraMap P.Ring S f = g) :
    ((Generators.localizationAway g).comp P).ker =
      Ideal.map ((Generators.localizationAway (S := T) g).toComp P).toAlgHom P.ker ⊔
        Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1} := by
  set Q := Generators.localizationAway (S := T) g
  have : Q.ker = Ideal.span {MvPolynomial.C g * MvPolynomial.X () - 1} := by
    convert (Algebra.Presentation.localizationAway T g).span_range_relation_eq_ker.symm
    simp [Presentation.localizationAway]
  have : Q.ker = Ideal.map (Q.ofComp P).toAlgHom
      (Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1}) := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_mul, map_one, this]
    simp only [Hom.toAlgHom, MvPolynomial.aeval_X, ofComp_val, Sum.elim_inl, sub_left_inj,
      Generators.comp, Generators.ofComp, Generators.localizationAway, Q]
    rw [MvPolynomial.aeval_rename, Sum.elim_comp_inr]
    simp_rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.coe_toAlgHom' R S (MvPolynomial Unit S)]
    rw [Function.comp_def, ← MvPolynomial.comp_aeval_apply, ← Algebra.Generators.algebraMap_apply,
      h]
  rw [ker_comp_eq_sup, Algebra.Generators.map_toComp_ker, this,
    Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective Q P), ← RingHom.ker_eq_comap_bot,
    ← sup_assoc]
  simp [Q]

variable (T) in
/-- If `R[X] → S` generates `S`, `T` is the localization of `S` away from `g` and
`f` is a pre-image of `g` in `R[X]`, this is the `R`-algebra map `R[X,Y] →ₐ[R] (R[X]/I²)[1/f]`
defined via mapping `Y` to `1/f`. -/
noncomputable
def compLocalizationAwayAlgHom : ((Generators.localizationAway g (S := T)).comp P).Ring →ₐ[R]
      Localization.Away (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)) :=
  aeval (R := R) (S₁ := Localization.Away _)
    (Sum.elim
      (fun _ ↦ IsLocalization.Away.invSelf <| (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)))
      (fun i : P.vars ↦ algebraMap P.Ring _ (X i)))

@[simp]
lemma compLocalizationAwayAlgHom_toAlgHom_toComp (x : P.Ring) :
    (compLocalizationAwayAlgHom T g P) (((localizationAway g (S := T)).toComp P).toAlgHom x) =
      algebraMap P.Ring _ x := by
  simp only [toComp_toAlgHom, Ideal.mem_comap, RingHom.mem_ker, compLocalizationAwayAlgHom, comp,
    localizationAway, AlgHom.toRingHom_eq_coe, aeval_rename,
    Sum.elim_comp_inr, ← IsScalarTower.toAlgHom_apply (R := R), ← comp_aeval_apply,
    aeval_X_left_apply]

@[simp]
lemma compLocalizationAwayAlgHom_X_inl : (compLocalizationAwayAlgHom T g P) (X (Sum.inl ())) =
      IsLocalization.Away.invSelf ((Ideal.Quotient.mk (P.ker ^ 2)) (P.σ g)) := by
  simp [compLocalizationAwayAlgHom]

lemma compLocalizationAwayAlgHom_relation_eq_zero :
    (compLocalizationAwayAlgHom T g P) ((rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1) = 0 := by
  rw [map_sub, map_one, map_mul, ← toComp_toAlgHom (Generators.localizationAway g (S := T)) P]
  show (compLocalizationAwayAlgHom T g P) (((localizationAway g).toComp P).toAlgHom _) * _ - _ = _
  rw [compLocalizationAwayAlgHom_toAlgHom_toComp, compLocalizationAwayAlgHom_X_inl,
    IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away _)]
  simp

lemma sq_ker_comp_le_ker_compLocalizationAwayAlgHom :
    ((localizationAway g (S := T)).comp P).ker ^ 2 ≤
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

/-- `T ⊗[S] (I/I²) → J/J²` is injective if `T` is the localization of `S` away from an element. -/
@[stacks 08JZ "part of (1)"]
lemma liftBaseChange_injective_of_isLocalizationAway :
    Function.Injective (LinearMap.liftBaseChange T
      (Extension.Cotangent.map
        ((Generators.localizationAway g (S := T)).toComp P).toExtensionHom)) := by
  set Q := Generators.localizationAway g (S := T)
  algebraize [((Generators.localizationAway g (S := T)).toComp P).toAlgHom.toRingHom]
  let f : P.Ring ⧸ P.ker ^ 2 := P.σ g
  let π := compLocalizationAwayAlgHom T g P
  refine IsLocalizedModule.injective_of_map_zero (Submonoid.powers g)
    (TensorProduct.mk S T P.toExtension.Cotangent 1) _ (fun x hx ↦ ?_)
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
    LinearMap.one_apply, LinearMap.smul_apply, one_smul, Algebra.Extension.Cotangent.map_mk,
    Extension.Cotangent.mk_eq_zero_iff] using hx

instance : Module.Free T (localizationAway g (S := T)).toExtension.Cotangent :=
  inferInstanceAs <| Module.Free T
    ((SubmersivePresentation.localizationAway g (S := T)).toExtension.Cotangent)

lemma Hom.algebraMap_toAlgHom' {R R' S : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R' S] [Algebra R R'] [IsScalarTower R R' S]
    {P : Generators R S} {P' : Generators R' S} (f : Hom P P') (x) :
    MvPolynomial.aeval P'.val (f.toAlgHom x) = MvPolynomial.aeval P.val x :=
  f.algebraMap_toAlgHom _

noncomputable
def cotangentCompLocalizationAwaySection
    (x : ((localizationAway g (S := T)).comp P).Ring)
    (hx : ((localizationAway g (S := T)).ofComp P).toAlgHom x = C g * X () - 1) :
    (localizationAway g (S := T)).toExtension.Cotangent →ₗ[T]
      ((localizationAway g (S := T)).comp P).toExtension.Cotangent :=
  have hxmem : (aeval ((localizationAway g).comp P).val) x = 0 := by
    rw [← ((localizationAway g (S := T)).ofComp P).algebraMap_toAlgHom', hx]
    simp [localizationAway]
  (SubmersivePresentation.localizationAway g (S := T)).basisCotangent.constr T
    (fun _ ↦ Extension.Cotangent.mk ⟨x, hxmem⟩)

lemma _root_.Algebra.SubmersivePresentation.basisCotangent_apply {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (P : SubmersivePresentation R S) (r : P.rels) :
    P.basisCotangent r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩ := by
  simp [SubmersivePresentation.basisCotangent]

lemma cotangentCompLocalizationAwaySection_apply
    (x : ((localizationAway g (S := T)).comp P).Ring)
    (hx : ((localizationAway g (S := T)).ofComp P).toAlgHom x = C g * X () - 1) :
    (cotangentCompLocalizationAwaySection g P x hx)
      (Extension.Cotangent.mk ⟨C g * X () - 1,
        (Presentation.localizationAway g (S := T)).relation_mem_ker ()⟩) =
        Extension.Cotangent.mk ⟨x,
          by
            simp only [toExtension_Ring, RingHom.mem_ker, algebraMap_apply,
              ← ((localizationAway g (S := T)).ofComp P).algebraMap_toAlgHom', hx]
            simp [localizationAway]⟩ := by
  show (cotangentCompLocalizationAwaySection g P x hx)
    (Extension.Cotangent.mk <|
      ⟨(SubmersivePresentation.localizationAway g (S := T)).relation (),
        (SubmersivePresentation.localizationAway g (S := T)).relation_mem_ker ()⟩) = _
  dsimp only [cotangentCompLocalizationAwaySection]
  erw [← (SubmersivePresentation.localizationAway g (S := T)).basisCotangent_apply]
  erw [Basis.constr_basis]

lemma map_comp_cotangentCompLocalizationAwaySection
    (x : ((localizationAway g (S := T)).comp P).Ring)
    (hx : ((localizationAway g (S := T)).ofComp P).toAlgHom x = C g * X () - 1) :
    (Extension.Cotangent.map ((localizationAway g).ofComp P).toExtensionHom) ∘ₗ
      cotangentCompLocalizationAwaySection g P x hx = .id := by
  apply (SubmersivePresentation.localizationAway g (S := T)).basisCotangent.ext
  intro r
  simp only [toExtension_Ring, toExtension_commRing, toExtension_algebra₂, LinearMap.coe_comp,
    Function.comp_apply, Basis.constr_basis, cotangentCompLocalizationAwaySection]
  erw [Extension.Cotangent.map_mk]
  simp only [toExtension_Ring, toExtension_commRing, toExtension_algebra₂, Extension.Hom.toAlgHom,
    Hom.toExtensionHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_mk, RingHom.coe_coe, hx]
  simp only [SubmersivePresentation.basisCotangent, toExtension_Ring, toExtension_commRing,
    toExtension_algebra₂, Basis.coe_mk]
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
    ⟨cotangentCompLocalizationAwaySection g P x hx,
      map_comp_cotangentCompLocalizationAwaySection g P x hx⟩).1

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
    cotangentCompLocalizationAwaySection_apply]

lemma cotangentCompLocalizationAwayEquiv_symm_comp_inl :
    (cotangentCompLocalizationAwayEquiv (T := T) g P x hx).symm.toLinearMap ∘ₗ
      LinearMap.inl T (T ⊗[S] P.toExtension.Cotangent) (localizationAway g).toExtension.Cotangent =
      LinearMap.liftBaseChange T
        (Extension.Cotangent.map ((localizationAway g).toComp P).toExtensionHom) :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompLocalizationAwaySection g P x hx,
      map_comp_cotangentCompLocalizationAwaySection g P x hx⟩).2.left.symm

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
    ⟨cotangentCompLocalizationAwaySection g P x hx,
      map_comp_cotangentCompLocalizationAwaySection g P x hx⟩).2.right.symm

@[simp]
lemma snd_cotangentCompLocalizationAwayEquiv
    (a : ((localizationAway g).comp P).toExtension.Cotangent) :
    (cotangentCompLocalizationAwayEquiv (T := T) g P x hx a).2 =
      Extension.Cotangent.map ((localizationAway g).ofComp P).toExtensionHom a := by
  rw [← snd_comp_cotangentCompLocalizationAwayEquiv g P x hx]
  simp

/-
lemma relation_mem_ker_comp :
      (rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1 ∈
        ((localizationAway (S := T) g).comp P).ker :=
    sorry
-/

@[simp]
lemma _root_.MvPolynomial.aeval_C_comp_left {σ ι R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    (f : σ → S) (p : MvPolynomial σ R) :
    aeval (R := R) (C (σ := ι) ∘ f) p = C (aeval f p) := by
  rw [← MvPolynomial.algebraMap_eq, Function.comp_def]
  simp_rw [← IsScalarTower.toAlgHom_apply R S (MvPolynomial ι S), comp_aeval_apply]

/-
@[simp]
lemma cotangentCompLocalizationAwayEquiv_symm_inr' :
    (cotangentCompLocalizationAwayEquiv (T := T) g P x hx).symm
      (0, Extension.Cotangent.mk ⟨(Presentation.localizationAway T g).relation (),
            (Presentation.localizationAway T g).relation_mem_ker _⟩) =
          Extension.Cotangent.mk
            ⟨rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1, relation_mem_ker_comp _ _⟩ := by
  apply (cotangentCompLocalizationAwayEquiv (T := T) g P x hx).injective
  simp
  ext : 1
  · simp
    sorry
  · simp only [snd_cotangentCompLocalizationAwayEquiv]
    erw [Extension.Cotangent.map_mk]
    congr 1
    simp only [toExtension_Ring, toExtension_commRing, Extension.Hom.toAlgHom, Hom.toExtensionHom,
      Hom.toAlgHom, ofComp, AlgHom.toRingHom_eq_coe, AlgHom.coe_mk, RingHom.coe_coe, map_sub,
      map_mul, aeval_X, Sum.elim_inl, map_one, Subtype.mk.injEq, sub_left_inj]
    erw [aeval_rename, Sum.elim_comp_inr]
    simp only [aeval_C_comp_left, aeval_val_σ]
    rfl
-/

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
