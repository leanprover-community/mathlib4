/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Small
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions and base change.

-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
@[mk_iff]
class LocallyOfFiniteType (f : X ⟶ Y) : Prop where
  finiteType_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FiniteType

alias Scheme.Hom.finiteType_appLE := LocallyOfFiniteType.finiteType_appLE

@[deprecated (since := "2026-01-20")]
alias LocallyOfFiniteType.finiteType_of_affine_subset :=
  Scheme.Hom.finiteType_appLE

instance : HasRingHomProperty @LocallyOfFiniteType RingHom.FiniteType where
  isLocal_ringHomProperty := RingHom.finiteType_isLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFiniteType_iff, affineLocally_iff_forall_isAffineOpen]

instance (priority := 900) locallyOfFiniteType_of_isOpenImmersion [IsOpenImmersion f] :
    LocallyOfFiniteType f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.finiteType_holdsForLocalizationAway.containsIdentities

instance : MorphismProperty.IsStableUnderComposition @LocallyOfFiniteType :=
  HasRingHomProperty.stableUnderComposition RingHom.finiteType_stableUnderComposition

instance locallyOfFiniteType_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFiniteType f] [hg : LocallyOfFiniteType g] : LocallyOfFiniteType (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

theorem locallyOfFiniteType_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f :=
  HasRingHomProperty.of_comp (fun _ _ ↦ RingHom.FiniteType.of_comp_finiteType) ‹_›

instance : MorphismProperty.IsMultiplicative @LocallyOfFiniteType where
  id_mem _ := inferInstance

open scoped TensorProduct in
instance locallyOfFiniteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyOfFiniteType :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.finiteType_isStableUnderBaseChange

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType g] :
    LocallyOfFiniteType (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [LocallyOfFiniteType f] : LocallyOfFiniteType (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

lemma LocallyOfFiniteType.stalkMap [LocallyOfFiniteType f] (x : X) :
    (f.stalkMap x).hom.EssFiniteType :=
  HasRingHomProperty.stalkMap_of_respectsIso RingHom.EssFiniteType.respectsIso
    (fun f hf _ _ ↦ RingHom.EssFiniteType.holdsForLocalization.localRingHom
      RingHom.EssFiniteType.stableUnderComposition
      RingHom.EssFiniteType.isStableUnderBaseChange.localizationPreserves _
      (RingHom.FiniteType.essFiniteType hf)) ‹_› x

instance {R} [CommRing R] [IsJacobsonRing R] : JacobsonSpace <| Spec <| .of R :=
  inferInstanceAs (JacobsonSpace (PrimeSpectrum R))

instance {R : CommRingCat} [IsJacobsonRing R] : JacobsonSpace (Spec R) :=
  inferInstanceAs (JacobsonSpace (PrimeSpectrum R))

nonrec lemma LocallyOfFiniteType.jacobsonSpace
    (f : X ⟶ Y) [LocallyOfFiniteType f] [JacobsonSpace Y] : JacobsonSpace X := by
  wlog hY : ∃ S, Y = Spec S
  · rw [(Scheme.OpenCover.isOpenCover_opensRange (Y.affineCover.pullback₁ f)).jacobsonSpace_iff]
    intro i
    have inst : LocallyOfFiniteType (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have inst : JacobsonSpace Y := ‹_› -- TC gets stuck on the WLOG hypothesis without it.
    have inst : JacobsonSpace (Y.affineCover.X i) :=
      .of_isOpenEmbedding (Y.affineCover.f i).isOpenEmbedding
    let e := ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding.isEmbedding.toHomeomorph
    have := this (Y.affineCover.pullbackHom f i) ⟨_, rfl⟩
    exact .of_isClosedEmbedding e.symm.isClosedEmbedding
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : JacobsonSpace (Spec R) := ‹_› -- TC gets stuck on the WLOG hypothesis without it.
    rw [X.affineCover.isOpenCover_opensRange.jacobsonSpace_iff]
    intro i
    have := this _ (X.affineCover.f i ≫ f) ⟨_, rfl⟩
    let e := (X.affineCover.f i).isOpenEmbedding.isEmbedding.toHomeomorph
    exact .of_isClosedEmbedding e.symm.isClosedEmbedding
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl : Spec.map φ = f⟩ := Spec.homEquiv.symm.surjective f
  have : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  have := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr ‹_›
  exact PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp (isJacobsonRing_of_finiteType (A := R))

set_option backward.isDefEq.respectTransparency false in
/--
The category of affine schemes locally of finite type over a fixed base scheme is essentially small.
TODO: extend this to (relatively) quasi-compact schemes.
-/
lemma essentiallySmall_costructuredArrow_Spec
    (P : MorphismProperty Scheme.{u}) (hP : P ≤ @LocallyOfFiniteType) [P.RespectsIso] :
    EssentiallySmall.{u} (P.CostructuredArrow ⊤ Scheme.Spec X) := by
  let F := MorphismProperty.CostructuredArrow.forget P ⊤ Scheme.Spec X ⋙ CostructuredArrow.proj _ _
  refine .of_functor F ?_ ?_
  · let Q' : ObjectProperty CommRingCat.{u} := fun S ↦
      ∃ R, (R ∈ Set.range fun U ↦ Γ(X, U)) ∧ ∃ (f : R ⟶ S), f.hom.FiniteType
    have : Q'.EssentiallySmall := CommRingCat.essentiallySmall_of_finiteType fun S ↦ id
    suffices ObjectProperty.EssentiallySmall.{u} (· ∈ Set.range (Opposite.unop ∘ F.obj)) by
      rw [← ObjectProperty.essentiallySmall_unop_iff]
      refine .of_le (Q := .isoClosure (· ∈ Set.range (Opposite.unop ∘ F.obj))) ?_
      exact fun R ⟨S, e⟩ ↦ ⟨_, ⟨S, rfl⟩, ⟨e.some.unop⟩⟩
    refine CommRingCat.essentiallySmall_of_localizationAway (Q := Q'.isoClosure) ?_
    rintro _ ⟨S, rfl⟩
    have (q : Spec (F.obj S).unop) : ∃ f, q ∈ PrimeSpectrum.basicOpen f ∧
        Q' Γ(Spec (F.obj S).unop, PrimeSpectrum.basicOpen f) := by
      obtain ⟨_, ⟨U, hU, rfl⟩, hqU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ <| S.hom q) isOpen_univ
      obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hqf, hfU⟩ :=
        PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hqU (S.hom ⁻¹ᵁ U).isOpen
      have : LocallyOfFiniteType S.hom := hP _ S.prop
      exact ⟨f, hqf, _, ⟨U, rfl⟩, S.hom.appLE _ _ hfU,
        (S.hom.finiteType_appLE hU (.Spec_basicOpen _)) _⟩
    choose f hqf hf using this
    refine ⟨Set.range f, PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp ?_, Set.forall_mem_range.mpr ?_⟩
    · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hqf _⟩
    · dsimp
      exact fun q ↦ ⟨_, hf q, ⟨(IsLocalization.algEquiv (.powers (f q)) _
        ((Spec.structureSheaf _).obj.obj (op _))).toRingEquiv.toCommRingCatIso⟩⟩
  · intro R
    refine ⟨.ofObj fun f : { f : Spec R.unop ⟶ X // P f } ↦ .mk _ f.1 f.2, inferInstance, ?_⟩
    refine fun S ⟨e⟩ ↦ ⟨_, .mk ⟨Spec.map e.inv.unop ≫ S.hom, ?_⟩,
      ⟨MorphismProperty.CostructuredArrow.isoMk e trivial trivial ?_⟩⟩
    · simp [← Spec.map_comp_assoc, F]
    · exact (P.cancel_left_of_respectsIso _ _).mpr S.prop

end AlgebraicGeometry
