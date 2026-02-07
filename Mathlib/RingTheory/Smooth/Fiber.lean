/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Etale.Locus

/-!

# Flat and smooth fibers imply smooth

## Main results
- `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`:
  Let `(R, m, k)` be a local ring, `S` be a local `R`-algebra that is flat,
  essentially of finite presentation, and `k ⊗[R] S` is `k`-formally smooth.
  Then `S` is `R`-formally smooth.
- `Algebra.mem_smoothLocus_of_formallySmooth_fiber`:
  Let `S` be a flat and finitely presented `R`-algebra, and `q` be a prime of `S` lying over `p`.
  If `κ(p) ⊗[R] S` is `κ(p)`-smooth, then `S` is smooth at `q`.
- `Algebra.Smooth.of_formallySmooth_fiber`:
  Flat and finitely presented and smooth fibers imply smooth.
- `Algebra.Etale.of_formallyUnramified_of_flat`:
  Flat and finitely presented and (formally) unramified implies etale.

## Note

For the converse that smooth imples flat, see `Mathlib/RingTheory/Smooth/Flat.lean`.

-/

open TensorProduct IsLocalRing

@[expose] public section

namespace Algebra

local notation "𝓀[" R "]" => ResidueField R
local notation "𝓂[" R "]" => maximalIdeal R

variable {R S P : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
variable [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]

section IsLocalRing

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallySmooth 𝓀[R] (𝓀[R] ⊗[R] S)]

attribute [local irreducible] KaehlerDifferential in
attribute [local instance] TensorProduct.rightAlgebra in
/--
Let `(R, m, k)` be a local ring, `(S, M, K)` be a local `R`-algebra that is `R`-flat such that
`k ⊗[R] S` is `k`-formally smooth.

Suppose there exists an `R`-presentation `S = P/I` with `I` finitely generated, and that
`P` is `R`-formally smooth and `Ω[P⁄R]` is `P`-finite free.

Then `S` is `R`-formally smooth.

Such `P` always exists when `S` is essentially of finite presentation over `R`.
See `FormallySmooth.of_formallySmooth_residueField_tensor`.
-/
private lemma FormallySmooth.of_formallySmooth_residueField_tensor_aux
    [FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG) :
    Algebra.FormallySmooth R S := by
  /-
  From the given presentation `0 → I → P → S → 0`, we construct the presentation
  `0 → k ⊗ᵣ I → k ⊗ᵣ P → k ⊗ᵣ S → 0` using the flatness of `S`.
  We also need the fact that `k ⊗ᵣ S` is also local with residue field `K`.
  -/
  let Sp := 𝓀[R] ⊗[R] S
  let Pp := 𝓀[R] ⊗[R] P
  let φ : Pp →ₐ[𝓀[R]] Sp := Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let ψ : Sp →ₐ[R] 𝓀[S] := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom _ _ _)
    (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  algebraize [φ.toRingHom, (φ.toRingHom.comp (algebraMap P Pp)), ψ.toRingHom,
    ψ.toRingHom.comp φ.toRingHom]
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have := IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  have : IsScalarTower P S Sp := .of_algebraMap_eq' rfl
  have : IsScalarTower S Sp 𝓀[S] := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, ψ, Sp]
  have : IsScalarTower P Sp 𝓀[S] := .to₁₃₄ _ S _ _
  have : IsScalarTower P Pp 𝓀[S] := .to₁₂₄ _ _ Sp _
  let ePp : Pp ≃ₐ[P] P ⊗[R] 𝓀[R] := { __ := TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e₀ : Ω[Pp⁄𝓀[R]] ≃ₗ[Pp] Pp ⊗[P] Ω[P⁄R] :=
    (KaehlerDifferential.tensorKaehlerEquiv R 𝓀[R] P Pp).symm
  have : Module.Free Pp Ω[Pp⁄𝓀[R]] := .of_equiv e₀.symm
  have : Module.Finite Pp Ω[Pp⁄𝓀[R]] := .of_surjective e₀.symm.toLinearMap e₀.symm.surjective
  let e₁ : RingHom.ker φ ≃ₗ[Pp] Pp ⊗[P] RingHom.ker (algebraMap P S) :=
    kerTensorProductMapIdToAlgHomEquiv _ _ _ _ h₁
  have h₁' : Function.Surjective φ := LinearMap.lTensor_surjective _ h₁
  have h₂' : (RingHom.ker φ).FG := by
    suffices Module.Finite Pp (RingHom.ker φ) from (Submodule.fg_top _).mp this.1
    have : Module.Finite P (RingHom.ker (algebraMap P S)) := ⟨(Submodule.fg_top _).mpr h₂⟩
    exact .equiv e₁.symm
  have h₃ : 𝓂[Sp] ≤ RingHom.ker ψ := by
    intro x hx
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective _ _ _ (by exact residue_surjective) x
    have : ¬IsUnit x := fun h ↦ hx <| h.map TensorProduct.includeRight
    simpa [ψ, Sp]
  /-
  The key is then to use jacobi criterion `FormallySmooth.iff_injective_cotangentComplexBaseChange`.
  Applying the criterion to `0 → I → P → S → 0` and `0 → k ⊗ᵣ I → k ⊗ᵣ P → k ⊗ᵣ S → 0`,
  the goal becomes the injectivity of `K ⊗ₛ I → K ⊗ₚ Ω[P/R]`,
  while the assumption that `S` is smooth at the maximal ideal translates to the injectivity of
  `K ⊗[k ⊗ᵣ S] (k ⊗ᵣ I) → K ⊗[k ⊗ᵣ P] Ω[k ⊗ᵣ P/R]`.
  -/
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField (P := P) h₁ h₂]
  have := (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange
    (R := 𝓀[R]) _ _ h₁' h₂' h₃).mp inferInstance
  -- But `K ⊗[k ⊗ᵣ P] Ω[k ⊗ᵣ P/R] = K ⊗[k ⊗ᵣ P] ((k ⊗ᵣ P) ⊗[P] Ω[P/R]) = K ⊗[P] Ω[P/R]`,
  let eᵣ : 𝓀[S] ⊗[Pp] Ω[Pp⁄𝓀[R]] ≃ₗ[S] 𝓀[S] ⊗[P] Ω[P⁄R] :=
    (AlgebraTensorModule.congr (.refl 𝓀[S] _) e₀).restrictScalars S ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange P Pp Sp 𝓀[S] Ω[P⁄R]).restrictScalars S
  -- and `K ⊗[k ⊗ᵣ S] (k ⊗ᵣ I) = K ⊗[k ⊗ᵣ P] ((k ⊗ᵣ P) ⊗[P] S) = K ⊗[P] S`.
  let eₗ : 𝓀[S] ⊗[Pp] RingHom.ker φ ≃ₗ[S] 𝓀[S] ⊗[P] RingHom.ker (algebraMap P S) :=
    (AlgebraTensorModule.congr (.refl 𝓀[S] 𝓀[S]) e₁).restrictScalars S ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange P Pp Sp 𝓀[S] _).restrictScalars S
  -- It remains to check that the two maps are equal under the identifications above.
  convert (eᵣ.injective.comp this).comp eₗ.symm.injective
  ext x
  dsimp
  induction x with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add x y _ _ => simp only [LinearEquiv.map_add, LinearMap.map_add, *]
  | tmul x y =>
  dsimp [eₗ, eᵣ, e₁, KaehlerDifferential.cotangentComplexBaseChange,
    TensorProduct.one_def, Pp, smul_tmul']
  rw [kerTensorProductMapIdToAlgHomEquiv_symm_apply]
  simp [e₀, Pp, ← TensorProduct.one_def]

/--
Let `(R, m, k)` be a local ring, `S` be a local `R`-algebra that is flat,
essentially of finite presentation, and `k ⊗[R] S` is `k`-formally smooth.
Then `S` is `R`-formally smooth.

Since we don't have an "essentially of finite presentation" type class yet, we explicitly require a
`P` that is of finite presentation over `R` and that `S` is a localization of it.
-/
lemma FormallySmooth.of_formallySmooth_residueField_tensor (M : Submonoid P)
    [IsLocalization M S] [Algebra.FinitePresentation R P] : Algebra.FormallySmooth R S := by
  /-
  By the fact that `S` is essentially of finite presentation, we get
  `S = (P/I)[M⁻¹] = P[M⁻¹]/I[M⁻¹]`, where `P` is a polynomial ring and `M` some submonoid of `P/I`.
  We then apply `FormallySmooth.of_formallySmooth_residueField_tensor_aux` to this presentation.
  -/
  classical
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstanceAs (Algebra.FiniteType R P))
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] S := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R P S).comp f₀) fun x ↦ by
    simpa using IsLocalization.map_units (M := M) _ ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  have hfP : (RingHom.ker fP).FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective _ hf₀
    convert this.map (algebraMap _ P')
    refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ by simp_all [fP])
    intro x hx
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M' x
    obtain ⟨a, ha, e⟩ : ∃ a ∈ M, a * f₀ x = 0 := by
      simpa [fP, IsLocalization.lift_mk', IsLocalization.map_eq_zero_iff M] using hx
    obtain ⟨a, rfl⟩ := hf₀ a
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨a, ha, by simpa⟩
  algebraize [fP.toRingHom]
  have : FormallyEtale (MvPolynomial (Fin n) R) P' := .of_isLocalization M'
  have : FormallySmooth R P' := .comp _ (MvPolynomial (Fin n) R) _
  have : Module.Free P' Ω[P'⁄R] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) P')
  exact FormallySmooth.of_formallySmooth_residueField_tensor_aux (R := R) (S := S) hf₁ hfP

end IsLocalRing

-- It is not hard to generalize the proof to get the full generality of the stacks tag.
-- The hard part is figuring out the right way to state the result. Hence we refrain from this
-- generalization until we have an application.
@[stacks 00TF "We require the whole fiber to be smooth instead"]
lemma IsSmoothAt.of_formallySmooth_fiber
    [Algebra.FinitePresentation R S] (p : Ideal R) (q : Ideal S)
    [p.IsPrime] [q.IsPrime] [q.LiesOver p] [FormallySmooth p.ResidueField (p.Fiber S)] :
    Algebra.IsSmoothAt R q := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := algebraMapSubmonoid S p.primeCompl)
        (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
        by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : FormallySmooth 𝓀[Rp] (𝓀[Rp] ⊗[Rp] Sq) := by
    let : Algebra S (𝓀[Rp] ⊗[R] S) := TensorProduct.rightAlgebra
    have : FormallySmooth 𝓀[Rp] ((𝓀[Rp] ⊗[R] S) ⊗[S] Sq) :=
      .comp _ (𝓀[Rp] ⊗[R] S) _
    let e : 𝓀[Rp] ⊗[R] S ≃ₐ[S] S ⊗[R] 𝓀[Rp] :=
      { __ := TensorProduct.comm _ _ _, commutes' _ := rfl }
    let e' : (𝓀[Rp] ⊗[R] S) ⊗[S] Sq ≃ₐ[R] 𝓀[Rp] ⊗[Rp] Sq :=
      ((TensorProduct.comm _ _ _).restrictScalars R).trans <|
      ((TensorProduct.congr (.refl (R := S)) e).restrictScalars R).trans <|
      ((TensorProduct.cancelBaseChange _ _ S _ _).restrictScalars R).trans <|
      (TensorProduct.comm _ _ _).trans (TensorProduct.equivOfCompatibleSMul _ _ _ _)
    have : e'.toAlgHom.comp (IsScalarTower.toAlgHom R p.ResidueField _) =
        IsScalarTower.toAlgHom _ _ _ := by ext
    let e'' : (𝓀[Rp] ⊗[R] S) ⊗[S] Sq ≃ₐ[𝓀[Rp]] 𝓀[Rp] ⊗[Rp] Sq :=
      { __ := e', commutes' r := congr($this r) }
    exact .of_equiv e''
  have := FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Sq) (P := Sp) (algebraMapSubmonoid _ q.primeCompl)
  exact .comp R Rp Sq

lemma Smooth.of_formallySmooth_fiber [Algebra.FinitePresentation R S]
    (H : ∀ (I : Ideal R) [I.IsPrime], FormallySmooth I.ResidueField (I.Fiber S)) :
    Algebra.Smooth R S := by
  refine ⟨smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q ↦ ?_), ‹_›⟩
  exact .of_formallySmooth_fiber (q.asIdeal.under R) _

attribute [local instance] FormallyEtale.of_formallyUnramified_of_field in
@[stacks 08WD "(3) => (1)"]
lemma Etale.of_formallyUnramified_of_flat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S] [FormallyUnramified R S] :
    Etale R S :=
  have : Smooth R S := .of_formallySmooth_fiber inferInstance
  ⟨⟨inferInstance, inferInstance⟩, ‹_›⟩

lemma IsEtaleAt.of_isUnramifiedAt_of_flat
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime] [IsUnramifiedAt R q] :
    IsEtaleAt R q := by
  obtain ⟨f, hfp, H⟩ := exists_unramified_of_isUnramifiedAt (R := R) q
  change ⟨q, ‹_›⟩ ∈ etaleLocus R S
  suffices Algebra.Etale R (Localization.Away f) from
    (basicOpen_subset_etaleLocus_iff (R := R) (f := f)).mpr inferInstance hfp
  exact .of_formallyUnramified_of_flat

end Algebra
