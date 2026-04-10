/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Formally unramified morphisms

A morphism of schemes `f : X ⟶ Y` is formally unramified if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally unramified.

We show that these properties are local, and are stable under compositions and base change.

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

open AlgebraicGeometry

/-- If `S` is a formally unramified `R`-algebra, essentially of finite type, the diagonal is an
open immersion. -/
instance Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (TensorProduct.lmul' R (S := S)).toRingHom)) := by
  rw [isOpenImmersion_SpecMap_iff_of_surjective _ (fun x ↦ ⟨1 ⊗ₜ x, by simp⟩)]
  apply (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp
  apply (Ideal.cotangent_subsingleton_iff _).mp
  exact inferInstanceAs <| Subsingleton Ω[S⁄R]

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is formally unramified if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally unramified.

See `FormallyUnramified.hom_ext` and `FormallyUnramified.of_hom_ext`
for the infinitesimal lifting criterion. -/
@[mk_iff]
class FormallyUnramified (f : X ⟶ Y) : Prop where
  formallyUnramified_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FormallyUnramified

alias Scheme.Hom.formallyUnramified_appLE := FormallyUnramified.formallyUnramified_appLE

@[deprecated (since := "2026-01-20")]
alias FormallyUnramified.formallyUnramified_of_affine_subset := Scheme.Hom.formallyUnramified_appLE

namespace FormallyUnramified

instance : HasRingHomProperty @FormallyUnramified RingHom.FormallyUnramified where
  isLocal_ringHomProperty := RingHom.FormallyUnramified.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [formallyUnramified_iff, affineLocally_iff_forall_isAffineOpen]

instance : MorphismProperty.IsStableUnderComposition @FormallyUnramified :=
  HasRingHomProperty.stableUnderComposition RingHom.FormallyUnramified.stableUnderComposition

/-- `f : X ⟶ S` is formally unramified if `X ⟶ X ×ₛ X` is an open immersion.
In particular, monomorphisms (e.g. immersions) are formally unramified.
The converse is true if `f` is locally of finite type. -/
instance (priority := 900) [IsOpenImmersion (pullback.diagonal f)] : FormallyUnramified f := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @FormallyUnramified) Y.affineCover]
    intro i
    have inst : IsOpenImmersion (pullback.diagonal (pullback.snd f (Y.affineCover.f i))) :=
      MorphismProperty.pullback_snd (P := .diagonal @IsOpenImmersion) _ _ ‹_›
    exact this (pullback.snd _ _) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) X.affineCover]
    intro i
    have inst : IsOpenImmersion (pullback.diagonal (X.affineCover.f i ≫ f)) :=
      MorphismProperty.comp_mem (.diagonal @IsOpenImmersion) _ _
        (inferInstanceAs (IsOpenImmersion _)) ‹_›
    exact this (_ ≫ _) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl : Spec.map φ = f⟩ := Spec.homEquiv.symm.surjective f
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  algebraize [φ.hom]
  let F := (Algebra.TensorProduct.lmul' R (S := S)).toRingHom
  have hF : Function.Surjective F := fun x ↦ ⟨.mk _ _ _ x 1, by simp [F]⟩
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom F)) := by
    rwa [← MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _
      (pullbackSpecIso R S S).inv, ← AlgebraicGeometry.diagonal_SpecMap R S]
  obtain ⟨e, he, he'⟩ := (isOpenImmersion_SpecMap_iff_of_surjective _ hF).mp this
  refine ⟨subsingleton_of_forall_eq 0 fun x ↦ ?_⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton.mp (he'.le hx)
  refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
  rw [pow_two, Subtype.coe_mk, ← he, mul_assoc]
  exact Ideal.mul_mem_mul (he'.ge (Ideal.mem_span_singleton_self e)) hx

theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallyUnramified (f ≫ g)] : FormallyUnramified f :=
  HasRingHomProperty.of_comp (fun {R S T _ _ _} f g H ↦ by
    algebraize [f, g, g.comp f]
    exact Algebra.FormallyUnramified.of_restrictScalars R S T) ‹_›

instance : MorphismProperty.IsMultiplicative @FormallyUnramified where
  id_mem _ := inferInstance

instance : MorphismProperty.IsStableUnderBaseChange @FormallyUnramified :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.FormallyUnramified.isStableUnderBaseChange

open MorphismProperty in
/-- The diagonal of a formally unramified morphism of finite type is an open immersion. -/
instance isOpenImmersion_diagonal [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsOpenImmersion (pullback.diagonal f) := by
  wlog hX : (∃ S, X = Spec S) ∧ ∃ R, Y = Spec R
  · let 𝒰Y := Y.affineCover
    let 𝒰X (j : (Y.affineCover.pullback₁ f).I₀) :
        ((Y.affineCover.pullback₁ f).X j).OpenCover := Scheme.affineCover _
    apply IsZariskiLocalAtTarget.of_range_subset_iSup _
      (Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange f 𝒰Y 𝒰X)
    intro ⟨i, j⟩
    rw [arrow_mk_iso_iff (P := @IsOpenImmersion)
      (Scheme.Pullback.diagonalRestrictIsoDiagonal f 𝒰Y 𝒰X i j)]
    have hu : FormallyUnramified ((𝒰X i).f j ≫ pullback.snd f (𝒰Y.f i)) :=
      comp_mem _ _ _ inferInstance (pullback_snd _ _ inferInstance)
    have hfin : LocallyOfFiniteType ((𝒰X i).f j ≫ pullback.snd f (𝒰Y.f i)) :=
      comp_mem _ _ _ inferInstance (pullback_snd _ _ inferInstance)
    exact this _ ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  obtain ⟨⟨S, rfl⟩, R, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified),
    HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at *
  algebraize [f.hom]
  rw [show f = CommRingCat.ofHom (algebraMap R S) from rfl, diagonal_SpecMap R S,
    cancel_right_of_respectsIso (P := @IsOpenImmersion)]
  infer_instance

lemma stalkMap [FormallyUnramified f] (x : X) : (f.stalkMap x).hom.FormallyUnramified :=
  HasRingHomProperty.stalkMap
    (fun f hf p q ↦
      RingHom.FormallyUnramified.holdsForLocalization.localRingHom
        RingHom.FormallyUnramified.stableUnderComposition
        RingHom.FormallyUnramified.isStableUnderBaseChange.localizationPreserves _ hf) ‹_› x

instance [FormallyUnramified f] [LocallyOfFiniteType f] (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f.base x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  suffices h : Algebra.IsSeparable
      (IsLocalRing.ResidueField <| Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField <| X.presheaf.stalk x) by
    convert h
    refine Algebra.algebra_ext _ _ fun x ↦ ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact stalkMap f x
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Given any commuting diagram
```
Z' --→ X
|      |
↓      ↓
Z  --→ Y
```
With `X ⟶ Y` formally unramified and `Z' ⟶ Z` an infinitesimal thickening, there exists at most
one arrow `Z ⟶ X` making the diagram commute.
-/
@[stacks 04F1]
protected lemma hom_ext {Z' Z : Scheme} (i : Z' ⟶ Z) (hi : IsNilpotent i.ker) [IsClosedImmersion i]
    (f : X ⟶ Y) [FormallyUnramified f]
    {g₁ g₂ : Z ⟶ X} (hig : i ≫ g₁ = i ≫ g₂) (hgf : g₁ ≫ f = g₂ ≫ f) : g₁ = g₂ := by
  have : IsDominant i := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff, denseRange_iff_closure_range, ← i.support_ker,
      ← i.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g₁ x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  have : g₁.base = g₂.base := by ext x; obtain ⟨x, rfl⟩ := i.surjective x; exact congr($hig x)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV : W ≤ _⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (And.intro hxV (by simpa [← this])) (g₁ ⁻¹ᵁ V ⊓ g₂ ⁻¹ᵁ V).isOpen
  refine ⟨W, hxW, ?_⟩
  have := f.formallyUnramified_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom,
    ((g₁ ≫ f).appLE U W (by grw [hWV, inf_le_left, hVU]; rfl)).hom]
  let ψ₁ : Γ(X, V) →ₐ[Γ(Y, U)] Γ(Z, W) := ⟨(g₁.appLE _ _ (hWV.trans inf_le_left)).hom, fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE]⟩
  let ψ₂ : Γ(X, V) →ₐ[Γ(Y, U)] Γ(Z, W) := ⟨(g₂.appLE _ _ (hWV.trans inf_le_right)).hom, fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, hgf, - Scheme.Hom.comp_appLE]⟩
  suffices ψ₁ = ψ₂ by
    simpa [ψ₁, ψ₂, -Iso.cancel_iso_hom_left, IsAffineOpen.isoSpec_hom] using
      congr(hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ($this).toRingHom) ≫ hV.fromSpec)
  refine Algebra.FormallyUnramified.ext' (i.app W).hom ?_ ψ₁ ψ₂ ?_
  · obtain ⟨n, hn⟩ := hi
    exact ⟨n, by simpa using congr(($hn).ideal ⟨W, hW⟩)⟩
  · simp [ψ₁, ψ₂, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp, hig,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, - Scheme.Hom.comp_appLE]

/--
To show that `f : X ⟶ Y` is formally unramified,
it suffices to check for that every following commuting diagram
```
Spec R --→ X
  |        |
  ↓        ↓
Spec S --→ Y
```
with `S = R/I` for some `I² = 0`, there exists at most one arrow `Spec S ⟶ X` making
the diagram commute.
-/
protected lemma of_hom_ext (f : X ⟶ Y)
    (H : ∀ (R S : CommRingCat) (φ : R ⟶ S) (_ : Function.Surjective φ)
      (_ : RingHom.ker φ.hom ^ 2 = ⊥) (g₁ g₂ : Spec R ⟶ X)
      (_ : Spec.map φ ≫ g₁ = Spec.map φ ≫ g₂) (_ : g₁ ≫ f = g₂ ≫ f), g₁ = g₂) :
    FormallyUnramified f := by
  refine ⟨fun {U hU V hV hVU} ↦ ?_⟩
  letI := (f.appLE U V hVU).hom.toAlgebra
  refine Algebra.FormallyUnramified.iff_comp_injective.mpr fun R _ _ I hI g₁ g₂ hg₁g₂ ↦ ?_
  have hg₁ : f.appLE U V hVU ≫ CommRingCat.ofHom g₁ = CommRingCat.ofHom (algebraMap _ R) :=
    CommRingCat.hom_ext g₁.comp_algebraMap
  have hg₂ : f.appLE U V hVU ≫ CommRingCat.ofHom g₂ = CommRingCat.ofHom (algebraMap _ R) :=
    CommRingCat.hom_ext g₂.comp_algebraMap
  have := H (.of R) (.of (R ⧸ I)) (CommRingCat.ofHom (Ideal.Quotient.mkₐ Γ(Y, U) I))
    Ideal.Quotient.mk_surjective (by simpa)
    (Spec.map (CommRingCat.ofHom g₁) ≫ hV.fromSpec) (Spec.map (CommRingCat.ofHom g₂) ≫ hV.fromSpec)
    (by simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom, *])
    (by simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc, *])
  rw [cancel_mono, Spec.map_inj] at this
  exact AlgHom.ext fun x ↦ congr($this x)

end FormallyUnramified

end AlgebraicGeometry
