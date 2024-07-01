/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Restrict

/-!

# Nilpotents and zero locus on schemes

In this file we show some properties of the zero locus of a set of sections specific
to locally ringed spaces or schemes and characterise nilpotent sections in terms of
the associated basic open.

In the case of affine schemes, the zero locus corresponds under the `Scheme.isoSpec` isomorphism
to the zero locus in the sense of prime spectra. We provide API for reasoning about zero loci on
affine schemes to avoid using the `Scheme.isoSpec` isomorphism in applications.

## Main results

- `Scheme.isNilpotent_of_basicOpen_eq_bot_of_isCompact`: a section over a compact open
  of a scheme is nilpotent if and only if the associated basic open is empty.

## TODO

- Relate the zero locus to evaluation of sections in the residue fields of points.

-/

universe u

open TopologicalSpace CategoryTheory Opposite

noncomputable section

namespace AlgebraicGeometry

section toΓSpecFun

/-- On an affine scheme, `toΓSpecFun` is bijective. -/
lemma Scheme.toΓSpecFun_bijective_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    Function.Bijective X.toΓSpecFun :=
  (ConcreteCategory.bijective_of_isIso X.isoSpec.hom.val.base)

/-- On an affine scheme, `toΓSpecFun` is a closed map. -/
lemma Scheme.toΓSpecFun_isClosedMap (X : Scheme.{u}) [IsAffine X] :
    IsClosedMap X.toΓSpecFun :=
  (TopCat.homeoOfIso (asIso <| X.isoSpec.hom.val.base)).isClosedMap

end toΓSpecFun

section Cover

/-- If two global sections agree after restriction to each member of a finite open cover, then
they agree globally. -/
lemma Scheme.eq_of_eq_cover {X : Scheme.{u}} (f g : Γ(X, ⊤)) (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.J, Scheme.Γ.map (𝒰.map i).op f = Scheme.Γ.map (𝒰.map i).op g) : f = g := by
  fapply TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun i ↦ Scheme.Hom.opensRange (𝒰.map (𝒰.f i))) _ (fun _ ↦ homOfLE le_top)
  · rintro x -; simpa using ⟨_, 𝒰.covers x⟩
  · intro x;
    replace h := h (𝒰.f x)
    rw [← IsOpenImmersion.map_ΓIso_inv] at h
    exact (IsOpenImmersion.ΓIso (𝒰.map (𝒰.f x))).commRingCatIsoToRingEquiv.symm.injective h

/-- If the restriction of a global section to each member of an open cover is zero, then it is
globally zero. -/
lemma Scheme.zero_of_zero_cover {X : Scheme.{u}} (s : Γ(X, ⊤)) (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.J, Scheme.Γ.map (𝒰.map i).op s = 0) : s = 0 := by
  refine eq_of_eq_cover s 0 𝒰 (fun i ↦ by rw [map_zero]; exact h i)

end Cover

section ZeroLocus

lemma Scheme.zeroLocus_def {X : Scheme.{u}} {U : Opens X} (s : Set Γ(X, U)) :
    X.toRingedSpace.zeroLocus s = ⋂ f ∈ s, (X.basicOpen f).carrierᶜ :=
  rfl

/-- On a locally ringed space `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `toΓSpecFun` agrees with the associated zero locus on `X`. -/
lemma LocallyRingedSpace.toΓSpec_preim_zeroLocus_eq {X : LocallyRingedSpace}
    (s : Set (X.presheaf.obj (op ⊤))) :
    X.toΓSpecFun ⁻¹' PrimeSpectrum.zeroLocus s = X.toRingedSpace.zeroLocus s := by
  simp only [RingedSpace.zeroLocus]
  have (i : LocallyRingedSpace.Γ.obj (op X)) (_ : i ∈ s) :
      ((X.toRingedSpace.basicOpen i).carrier)ᶜ =
        X.toΓSpecFun ⁻¹' (PrimeSpectrum.basicOpen i).carrierᶜ := by
    symm
    rw [Set.preimage_compl, X.toΓSpec_preim_basicOpen_eq i]
  erw [Set.iInter₂_congr this]
  simp only [← Set.preimage_iInter₂, Γ_obj, Opens.carrier_eq_coe,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl, ← PrimeSpectrum.zeroLocus_iUnion₂]
  simp

/-- If `X` is affine, the image of the zero locus of global sections of `X` under `toΓSpecFun`
is the zero locus in terms of the prime spectrum of `Γ(X, ⊤)`. -/
lemma Scheme.toΓSpec_image_zeroLocus_eq {X : Scheme} [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.toΓSpecFun '' X.toRingedSpace.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← X.toΓSpec_preim_zeroLocus_eq, Set.image_preimage_eq]
  exact X.toΓSpecFun_bijective_of_isAffine.surjective

/-- If `X` is an affine scheme, every closed set of `X` is the zero locus
of a set of global sections. -/
lemma eq_zeroLocus_of_isClosed (X : Scheme) [IsAffine X] (s : Set X) (hs : IsClosed s) :
    ∃ I : Ideal (Γ(X, ⊤)), s = X.toRingedSpace.zeroLocus (I : Set Γ(X, ⊤)) := by
  let Z : Set (Spec <| Γ(X, ⊤)) := X.toΓSpecFun '' s
  have hZ : IsClosed Z := X.toΓSpecFun_isClosedMap _ hs
  obtain ⟨I, (hI : Z = _)⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
  use I
  simp only [← LocallyRingedSpace.toΓSpec_preim_zeroLocus_eq, ← hI, Z]
  rw [Set.preimage_image_eq _ X.toΓSpecFun_bijective_of_isAffine.injective]

end ZeroLocus

section Nilpotents

/-- If a global section is nilpotent on each member of a finite open cover, then `f` is
nilpotent. -/
lemma Scheme.isNilpotent_of_isNilpotent_cover {X : Scheme.{u}} (s : Γ(X, ⊤)) (𝒰 : X.OpenCover)
    [Finite 𝒰.J] (h : ∀ i : 𝒰.J, IsNilpotent (Scheme.Γ.map (𝒰.map i).op s)) : IsNilpotent s := by
  choose fn hfn using h
  have : Fintype 𝒰.J := Fintype.ofFinite 𝒰.J
  /- the maximum of all `fn i` (exists, because `𝒰.J` is finite) -/
  let N : ℕ := Finset.sup Finset.univ fn
  have hfnleN (i : 𝒰.J) : fn i ≤ N := Finset.le_sup (Finset.mem_univ i)
  use N
  apply zero_of_zero_cover
  intro i
  simp only [map_pow]
  exact pow_eq_zero_of_le (hfnleN i) (hfn i)

/-- If `U` is an affine open of a scheme `X`, a section over `U` is nilpotent if and only if
the associated basic open is empty.
See `Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact` for a version only assuming
`U` to be compact. -/
lemma IsAffineOpen.isNilpotent_iff_basicOpen_eq_bot {X : Scheme} {U : Opens X} (hU : IsAffineOpen U)
    (f : Γ(X, U)) : IsNilpotent f ↔ X.basicOpen f = ⊥ := by
  constructor
  · intro h
    apply X.basicOpen_eq_bot_of_isNilpotent
    exact h
  · intro h
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff, ← hU.fromSpec_preimage_basicOpen, h]
    rfl

/-- If `X` is an affine scheme and `f` is a global section, then `f` is nilpotent if and only
if the associated basic open is empty. -/
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isAffine (X : Scheme) [IsAffine X] (f : Γ(X, ⊤)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ :=
  (isAffineOpen_top X).isNilpotent_iff_basicOpen_eq_bot f


instance Scheme.ιOpens_appLE_isIso {X : Scheme.{u}} (U : Opens X) :
    IsIso ((Scheme.ιOpens U).appLE U ⊤ (by simp)) := by
  simp only [restrict_presheaf_obj, ofRestrict_appLE]
  let e : (Scheme.ιOpens U) ''ᵁ ⊤ ≤ U := by simp
  have : IsIso (homOfLE e) := by
    apply homOfLE_isIso_of_eq
    simp
  apply Functor.map_isIso

/-- If `U` is a compact open of a scheme and `f` a section over `U` such that the associated
basic open is empty, then `f` is nilpotent. This is the harder direction of
`Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact`. -/
lemma Scheme.isNilpotent_of_basicOpen_eq_bot_of_isCompact {X : Scheme.{u}}
    {U : Opens X} (hU : IsCompact U.carrier) (f : Γ(X, U))
    (hf : X.basicOpen f = ⊥) : IsNilpotent f := by
  let U' : Scheme.{u} := X ∣_ᵤ U
  have : CompactSpace U' := (isCompact_iff_compactSpace).mp hU
  let f' : Γ(U', ⊤) := (X.ιOpens U).appLE U ⊤ (by simp) f
  have hf' : U'.basicOpen f' = ⊥ := by
    simp only [f', Scheme.basicOpen_appLE, hf, ofRestrict_val_base, ge_iff_le, le_top,
      inf_of_le_right]
    rfl
  let 𝒰 : U'.OpenCover := U'.affineCover.finiteSubcover
  have (i : 𝒰.J) : IsAffine (𝒰.obj i) := Scheme.isAffine_affineCover U' _
  have hf' : IsNilpotent f' := by
    refine isNilpotent_of_isNilpotent_cover (X := U') f' 𝒰 (fun i ↦ ?_)
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isAffine (𝒰.obj i)]
    simp only [Γ_obj, Γ_map, Quiver.Hom.unop_op]
    erw [← preimage_basicOpen]
    rw [hf']
    rfl
  have hfinj : Function.Injective ((Hom.appLE (ιOpens U) U ⊤ (by simp))) := by
    apply Function.Bijective.injective
    exact ConcreteCategory.bijective_of_isIso (Hom.appLE (ιOpens U) U ⊤ _)
  rw [← IsNilpotent.map_iff hfinj]
  exact hf'

/-- A section over a compact open of a scheme is nilpotent if and only if its associated
basic open is empty. -/
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact {X : Scheme}
    {U : Opens X} (hU : IsCompact U.carrier) (f : Γ(X, U)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ :=
  ⟨X.basicOpen_eq_bot_of_isNilpotent U f,
    Scheme.isNilpotent_of_basicOpen_eq_bot_of_isCompact hU f⟩

/-- The zero locus of a set of sections over a compact open of a scheme is `X` if and only if
`s` is contained in the nilradical of `Γ(X, U)`. -/
lemma Scheme.zeroLocus_eq_top_iff_subset_nilradical_of_isCompact {X : Scheme.{u}} {U : Opens X}
    (hU : IsCompact U.carrier) (s : Set Γ(X, U)) :
    X.toRingedSpace.zeroLocus s = ⊤ ↔ s ⊆ (nilradical Γ(X, U)).carrier := by
  simp [Scheme.zeroLocus_def, ← Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU,
    ← mem_nilradical, Set.subset_def]

end Nilpotents

end AlgebraicGeometry
