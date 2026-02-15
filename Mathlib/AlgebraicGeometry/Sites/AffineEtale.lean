/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense

/-!
# Affine étale site

In this file we define the small affine étale site of a scheme `S`. The underlying
category is the category of commutative rings `R` equipped with an étale structure
morphism `Spec R ⟶ S`. We show that this category is essentially small,
that it is a dense subsite of the small étale site, and that it is `1`-hypercover
dense, which allows to show that if `S : Scheme.{u}`, then we can sheafify
étale presheaves with values in `Type u`, `AddCommGrpCat.{u}`, etc.

## Main results
- `AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv`: The category of sheaves on the
  small affine étale site is equivalent to the category of schemes on the small étale site.
-/

@[expose] public section

universe u v u'

open CategoryTheory Opposite Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

section

/-- Construct an object of affine `P`-schemes over `S` by giving a morphism `Spec R ⟶ S`. -/
@[simps! hom left]
def affineOverMk {P : MorphismProperty Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ S) (hf : P f) :
    P.CostructuredArrow ⊤ Scheme.Spec S :=
  .mk ⊤ f hf

/-- The `Spec` functor from affine `P`-schemes over `S` to `P`-schemes over `S` is dense
if `P` is local at the source. -/
instance isCoverDense_toOver_Spec (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (CostructuredArrow.toOver P Scheme.Spec S).IsCoverDense
      (smallGrothendieckTopology P) where
  is_cover U := by
    rw [Scheme.mem_smallGrothendieckTopology]
    let 𝒰 : Cover.{u} (precoverage P) U.left :=
      U.left.affineCover.changeProp
      (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ U.hom⟩
    let _ : Cover.Over S 𝒰 := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰, inferInstance,
      fun i ↦ P.comp_mem _ _ (𝒰.map_prop i) U.prop, fun X f ⟨i⟩ ↦ ?_⟩
    rw [Sieve.coverByImage]
    exact ⟨⟨affineOverMk (𝒰.f i ≫ U.hom) (P.comp_mem _ _ (𝒰.map_prop i) U.prop),
      CostructuredArrow.homMk (𝟙 _) ⟨⟩ rfl, Over.homMk (𝒰.f i) (by simp) trivial,
      by cat_disch⟩⟩

instance isOneHypercoverDense_toOver_Spec
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    Functor.IsOneHypercoverDense.{u} (CostructuredArrow.toOver P Scheme.Spec S)
    ((CostructuredArrow.toOver P Scheme.Spec S).inducedTopology (smallGrothendieckTopology P))
    (smallGrothendieckTopology P) :=
  Functor.IsOneHypercoverDense.of_hasPullbacks (fun X ↦ by
    let 𝒰 := affineOpenCover X.left
    let 𝒱 : Cover (precoverage P) X.left :=
      𝒰.openCover.changeProp (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒱.I₀) : (𝒱.X i).Over S := ⟨𝒰.f i ≫ X.hom⟩
    let : Cover.Over S 𝒱 := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰.I₀, fun i ↦ affineOverMk (𝒰.f i ≫ X.hom)
      (P.comp_mem _ _ (IsZariskiLocalAtSource.of_isOpenImmersion (𝒰.f i)) X.prop),
      fun i ↦ CostructuredArrow.homMk (𝒰.f i) (by simp), ?_⟩
    rw [Scheme.mem_smallGrothendieckTopology]
    exact ⟨𝒱, inferInstance, fun i ↦ P.comp_mem _ _ (𝒱.map_prop i) X.prop,
      fun _ _ ⟨i⟩ ↦ (Sieve.mem_ofArrows_iff ..).2 ⟨i, 𝟙 _, by cat_disch⟩⟩)

variable (S) in
/-- Given a scheme `S`, this is a structure which describes
an `S`-scheme that is finitely presented over an affine open
subset of `S`. This is used in the proof of the lemma
`essentiallySmall_costructuredArrow_Spec`. -/
structure FinitelyPresentedOverAffineOpen : Type u where
  /-- the (affine) open subset in the base scheme -/
  U : Opens S
  hU : IsAffineOpen U
  /-- the numbers of generators -/
  g : ℕ
  /-- the numbers of relations -/
  r : ℕ
  /-- the relations -/
  rel (x : Fin r) : MvPolynomial (Fin g) Γ(S, U)

namespace FinitelyPresentedOverAffineOpen

variable (P : S.FinitelyPresentedOverAffineOpen)

/-- The ring defined by the given presentation by generators and relations. -/
protected abbrev Ring : Type u :=
  MvPolynomial (Fin P.g) Γ(S, P.U) ⧸ Ideal.span (Set.range P.rel)

lemma exists_nhd {X : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (P : S.FinitelyPresentedOverAffineOpen),
      Nonempty (U.toScheme ≅ Spec (.of P.Ring)) := by
  obtain ⟨U, V, hx, hUV⟩ :
      ∃ (U : X.affineOpens) (V : S.affineOpens), x ∈ U.val ∧ U ≤ f.base ⁻¹' V := by
    obtain ⟨U, h₁, h₂, _⟩ := exists_isAffineOpen_mem_and_subset (x := f.base x) (U := ⊤) (by simp)
    obtain ⟨V, h₃, h₄, h₅⟩ := exists_isAffineOpen_mem_and_subset (x := x)
      (U := ⟨_, IsOpen.preimage f.continuous U.2⟩) (by simpa)
    exact ⟨⟨V, h₃⟩, ⟨U, h₁⟩, h₄, h₅⟩
  letI := (f.appLE V U hUV).hom.toAlgebra
  obtain ⟨n, φ, h₁, h₂⟩ :=
    (LocallyOfFinitePresentation.finitePresentation_appLE f V.prop U.prop hUV).out
  obtain ⟨r, ρ, hρ⟩ : ∃ (r : ℕ) (γ : Fin r → MvPolynomial (Fin n) Γ(S, V)),
      Ideal.span (Set.range γ) = RingHom.ker φ.toRingHom := by
    obtain ⟨s, hs⟩ := h₂
    exact ⟨s.card, Subtype.val ∘ s.equivFin.symm, by rw [← hs]; simp⟩
  let P : S.FinitelyPresentedOverAffineOpen :=
    { U := V.1, hU := V.prop, g := n, r := r, rel := ρ }
  let e : P.Ring ≃+* Γ(X, U.1) :=
    (Ideal.quotEquivOfEq hρ).trans (φ.toRingHom.quotientKerEquivRange.trans
      ((Subring.equivOfEq (RingHom.range_eq_top_of_surjective _ h₁)).trans Subring.topEquiv))
  exact ⟨U, hx, P, ⟨asIso (toSpecΓ U) ≪≫ Scheme.Spec.mapIso U.1.topIso.op.symm ≪≫
    Scheme.Spec.mapIso e.toCommRingCatIso.op⟩⟩

lemma exists_subring
    {A : CommRingCat.{u}} (f : Spec (.of A) ⟶ S) [LocallyOfFinitePresentation f] :
    ∃ (n : ℕ) (P : Fin n → S.FinitelyPresentedOverAffineOpen)
      (R₀ : Subring (∀ i, (P i).Ring)), Nonempty (A ≅ .of R₀) := by
  /- We find a finite open covering `(i : Fin n) ↦ U (α i)` of `Spec A`
  consisting of finitely presented schemes over an affine open subset of `S`. -/
  choose U hU P e using exists_nhd f
  let iso (x) := (e x).some
  obtain ⟨n, α, hα⟩ : ∃ (n : ℕ) (α : Fin n → Spec (.of A)),
    ⋃ (i : Fin n), (U (α i) : Set (Spec (.of A))) = Set.univ := by
      obtain ⟨s, hs⟩ := CompactSpace.isCompact_univ.elim_finite_subcover _
        (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion_of_mem x (hU x))
      refine ⟨s.card, Subtype.val ∘ (Finset.equivFin s).symm,
        subset_antisymm (by simp) (hs.trans ?_)⟩
      simp only [Function.comp_apply, Set.iUnion_subset_iff]
      exact fun i hi _ _ ↦ Set.mem_iUnion_of_mem ((Finset.equivFin s) ⟨i, hi⟩) (by simpa)
  /- We consider the map `φ : A →+* ∀ i, ((P ∘ α) i).Ring` that is essentially given by
  the restriction to the opens `U (α i)`, and show that it is injective by
  using the sheaf property of the structure sheaf. -/
  let β (i : Fin n) : A →+* ((P ∘ α) i).Ring :=
    (Spec.preimage ((iso (α i)).inv ≫ (U (α i)).ι)).hom
  let φ : A →+* ∀ i, ((P ∘ α) i).Ring := Pi.ringHom β
  have hφ : Function.Injective φ := by
    refine (AddMonoidHom.ker_eq_bot_iff φ.toAddMonoidHom).1 ?_
    ext a
    refine ⟨fun ha ↦ ?_, by rintro rfl; simp⟩
    replace ha (i : Fin n) : β i a = 0 := congr_fun ha i
    obtain ⟨a, rfl⟩ := (ΓSpecIso A).commRingCatIsoToRingEquiv.surjective a
    simp only [AddSubgroup.mem_bot, EmbeddingLike.map_eq_zero_iff]
    refine (openCoverOfIsOpenCover _ (U ∘ α) (.mk (by aesop))).ext_elem _ _ (fun i ↦ ?_)
    replace ha : (ΓSpecIso _).hom (((iso (α i)).inv ≫ (U (α i)).ι).appTop a) = 0 := by
      simpa [← ha] using ConcreteCategory.congr_hom (ΓSpecIso_naturality
        (Spec.preimage ((iso (α i)).inv ≫ (U (α i)).ι))) a
    apply (asIso (iso (α i)).inv.appTop ≪≫
      ΓSpecIso _).commRingCatIsoToRingEquiv.injective
    simpa [-EmbeddingLike.map_eq_zero_iff] using ha
  /- The expected subring is given by the range of `φ`. -/
  exact ⟨n, P ∘ α, RingHom.range φ, ⟨RingEquiv.toCommRingCatIso
    (RingEquiv.ofBijective φ.rangeRestrict
      ⟨(Function.Injective.of_comp_iff Subtype.val_injective _).1 hφ,
        RingHom.rangeRestrict_surjective φ⟩)⟩⟩

end FinitelyPresentedOverAffineOpen

lemma essentiallySmall_costructuredArrow_Spec
    (P : MorphismProperty Scheme.{u}) (hP : P ≤ @LocallyOfFinitePresentation) [P.RespectsIso] :
    EssentiallySmall.{u} (P.CostructuredArrow ⊤ Scheme.Spec S) := by
  /- It suffices to show that there is a `u`-small type which, up to
  isomorphisms, parametrizes all the the possible rings `Z.left.unop` for
  `Z : P.CostructuredArrow ⊤ Scheme.Spec S`. -/
  suffices ∃ (ι : Type u) (R : ι → CommRingCat.{u}),
      ∀ (Z : P.CostructuredArrow ⊤ Scheme.Spec S),
        ∃ (i : ι), Nonempty (R i ≅ Z.left.unop) by
    rw [essentiallySmall_iff_objectPropertyEssentiallySmall_top]
    obtain ⟨ι, R, hR⟩ := this
    let P₀ : ObjectProperty (P.CostructuredArrow ⊤ Scheme.Spec S) :=
      .ofObj (fun (t : Σ (i : ι) (f : Scheme.Spec.obj (op (R i)) ⟶ S), PLift (P f)) ↦
        .mk _ t.2.1 t.2.2.down)
    refine ObjectProperty.EssentiallySmall.of_le (Q := P₀.isoClosure) (fun Z _ ↦ ?_)
    obtain ⟨i, ⟨e⟩⟩ := hR Z
    refine ⟨_, ⟨i, Spec.map e.inv ≫ Z.hom, ⟨RespectsIso.precomp _ _ _ Z.prop⟩⟩, ⟨?_⟩⟩
    exact MorphismProperty.CostructuredArrow.isoMk e.op (by simp) (by simp)
      (by simp [← Spec.map_comp_assoc, e.inv_hom_id])
  /- We use the family given by all the subrings of the finite products
  of finitely presented algebras over the rings of sections of an affine
  open subset of `S`. -/
  refine ⟨Σ (n : ℕ) (P : Fin n → S.FinitelyPresentedOverAffineOpen),
    Subring (∀ i, (P i).Ring), fun ⟨n, P, R₀⟩ ↦ .of R₀, fun Z ↦ ?_⟩
  have : LocallyOfFinitePresentation Z.hom := hP _ Z.prop
  obtain ⟨n, P, R₀, ⟨e⟩⟩ := FinitelyPresentedOverAffineOpen.exists_subring Z.hom
  exact ⟨⟨n, P, R₀⟩, ⟨e.symm⟩⟩

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]

instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
    {ι : Type*} [Small.{u} ι] {C : Type*} [Category C] [HasColimitsOfShape (Discrete ι) C]
    (L : C ⥤ Scheme.{u}) [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape (Discrete ι) :=
  CostructuredArrow.isClosedUnderColimitsOfShape _ (fun _ ↦ coproductIsCoproduct' _)
    (fun _ _ _ _ h ↦ IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)) _

variable [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]

instance : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) where
  out n := by
    have : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
        (Discrete (Fin n)) :=
      IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete _ _
    apply MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape

end

/-- The small affine étale site: The category of affine schemes étale over `S`, whose objects are
commutative rings `R` with an étale structure morphism `Spec R ⟶ S`. -/
def AffineEtale (S : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.CostructuredArrow @Etale.{u} ⊤ Scheme.Spec.{u} S

namespace AffineEtale

/-- Construct an object of the small affine étale site. -/
@[simps!]
protected def mk {R : CommRingCat.{u}} (f : Spec R ⟶ S) [Etale f] : AffineEtale S :=
  MorphismProperty.CostructuredArrow.mk ⊤ f ‹_›

instance : Category S.AffineEtale :=
  inferInstanceAs <| Category (MorphismProperty.CostructuredArrow _ _ _ _)

/-- The `Spec` functor from the small affine étale site of `S` to the small étale site of `S`. -/
@[simps! obj_left obj_hom map_left]
protected noncomputable def Spec (S : Scheme.{u}) : S.AffineEtale ⥤ S.Etale :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

instance : (AffineEtale.Spec S).Faithful :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

instance : (AffineEtale.Spec S).Full :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Full

instance : (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).IsCoverDense
    (smallGrothendieckTopology _)

instance : HasPullbacks S.AffineEtale :=
  inferInstanceAs <| HasPullbacks (MorphismProperty.CostructuredArrow _ _ _ _)

variable (S) in
/-- The topology on the small affine étale site is the topology induced by `Spec` from
the small étale site. -/
def topology : GrothendieckTopology S.AffineEtale :=
  (AffineEtale.Spec S).inducedTopology S.smallEtaleTopology

instance : Functor.IsDenseSubsite (topology S) S.smallEtaleTopology (AffineEtale.Spec S) := by
  dsimp [topology]
  infer_instance

instance : Functor.IsOneHypercoverDense.{u} (AffineEtale.Spec S)
    (topology S) S.smallEtaleTopology :=
  isOneHypercoverDense_toOver_Spec _

instance : EssentiallySmall.{u} S.AffineEtale :=
  essentiallySmall_costructuredArrow_Spec _ (fun _ _ _ _ ↦ inferInstance)

end AffineEtale

section

variable {A : Type u'} [Category.{u} A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

instance : HasSheafify (AffineEtale.topology S) A :=
    hasSheafifyEssentiallySmallSite.{u} _ _

instance : HasSheafify S.smallEtaleTopology A :=
  (AffineEtale.Spec S).hasSheafify_of_isOneHypercoverDense
    (AffineEtale.topology S) S.smallEtaleTopology A

example : HasSheafify (AffineEtale.topology S) (Type u) := by
  infer_instance

example : HasSheafify S.smallEtaleTopology (Type u) := by
  infer_instance

example : Abelian (Sheaf (AffineEtale.topology S) AddCommGrpCat.{u}) := by
  infer_instance

example : Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) := by
  infer_instance

instance :
    Functor.IsEquivalence ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (AffineEtale.topology S) S.smallEtaleTopology) :=
  Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

instance : (AffineEtale.topology S).WEqualsLocallyBijective A :=
  .ofEssentiallySmall (AffineEtale.topology S)

instance : S.smallEtaleTopology.WEqualsLocallyBijective A :=
  .transport  _ _ _
    (Functor.IsDenseSubsite.coverPreserving (AffineEtale.topology S) _
      (AffineEtale.Spec S))

variable (S A)

/-- The category of sheaves on the small affine étale site is equivalent to the category of
sheaves on the small étale site. -/
@[simps! inverse]
noncomputable def AffineEtale.sheafEquiv :
    Sheaf (AffineEtale.topology S) A ≌ Sheaf S.smallEtaleTopology A :=
  ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (topology S) S.smallEtaleTopology).asEquivalence.symm

lemma isGrothendieckAbelian_sheaf_affineEtaleTopology
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf (AffineEtale.topology S) A) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

lemma isGrothendieckAbelian_sheaf_smallEtaleTopology
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology A) :=
  have := isGrothendieckAbelian_sheaf_affineEtaleTopology S A
  IsGrothendieckAbelian.of_equivalence (AffineEtale.sheafEquiv S A)

end

end AlgebraicGeometry.Scheme
