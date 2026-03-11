/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Bicones
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
/-!
# Representably flat functors

We define representably flat functors as functors such that the category of structured arrows
over `X` is cofiltered for each `X`. This concept is also known as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to avoid
confusion with other notions of flatness (e.g. see the notion of flat type-valued
functor in the file `Mathlib/CategoryTheory/Functor/TypeValuedFlat.lean`).

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preservesFiniteLimits`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
  limits, then `F` is flat.
* `preservesFiniteLimits_of_flat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `preservesFiniteLimits_iff_flat`: If `C` has all finite limits,
  then `F` is flat iff `F` is left_exact.
* `lan_preservesFiniteLimits_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
  then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `flat_iff_lan_flat`: If `C`, `D` are small and `C` has all finite limits, then `F` is flat iff
  `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` is flat.
* `preservesFiniteLimits_iff_lanPreservesFiniteLimits`: If `C`, `D` are small and `C` has all
  finite limits, then `F` preserves finite limits iff `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)`
  does.

-/

@[expose] public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace CategoryTheory

section RepresentablyFlat

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A functor `F : C ⥤ D` is representably flat if the comma category `(X/F)` is cofiltered for
each `X : D`.
-/
class RepresentablyFlat (F : C ⥤ D) : Prop where
  cofiltered : ∀ X : D, IsCofiltered (StructuredArrow X F)

/-- A functor `F : C ⥤ D` is representably coflat if the comma category `(F/X)` is filtered for
each `X : D`. -/
class RepresentablyCoflat (F : C ⥤ D) : Prop where
  filtered : ∀ X : D, IsFiltered (CostructuredArrow F X)

attribute [instance] RepresentablyFlat.cofiltered RepresentablyCoflat.filtered

variable (F : C ⥤ D)

instance RepresentablyFlat.of_isRightAdjoint [F.IsRightAdjoint] : RepresentablyFlat F where
  cofiltered _ := IsCofiltered.of_isInitial _ (mkInitialOfLeftAdjoint _ (.ofIsRightAdjoint F) _)

instance RepresentablyCoflat.of_isLeftAdjoint [F.IsLeftAdjoint] : RepresentablyCoflat F where
  filtered _ := IsFiltered.of_isTerminal _ (mkTerminalOfRightAdjoint _ (.ofIsLeftAdjoint F) _)

theorem RepresentablyFlat.id : RepresentablyFlat (𝟭 C) := inferInstance

theorem RepresentablyCoflat.id : RepresentablyCoflat (𝟭 C) := inferInstance

set_option backward.isDefEq.respectTransparency false in
instance RepresentablyFlat.comp (G : D ⥤ E) [RepresentablyFlat F]
    [RepresentablyFlat G] : RepresentablyFlat (F ⋙ G) := by
  refine ⟨fun X => IsCofiltered.of_cone_nonempty.{0} _ (fun {J} _ _ H => ?_)⟩
  obtain ⟨c₁⟩ := IsCofiltered.cone_nonempty (H ⋙ StructuredArrow.pre X F G)
  let H₂ : J ⥤ StructuredArrow c₁.pt.right F :=
    { obj := fun j => StructuredArrow.mk (c₁.π.app j).right
      map := fun {j j'} f =>
        StructuredArrow.homMk (H.map f).right (congrArg CommaMorphism.right (c₁.w f)) }
  obtain ⟨c₂⟩ := IsCofiltered.cone_nonempty H₂
  simp only [H₂] at c₂
  exact ⟨⟨StructuredArrow.mk (c₁.pt.hom ≫ G.map c₂.pt.hom),
    ⟨fun j => StructuredArrow.homMk (c₂.π.app j).right (by simp [← G.map_comp]),
     fun j j' f => by simpa using (c₂.w f).symm⟩⟩⟩

section

variable {F}

/-- Being a representably flat functor is closed under natural isomorphisms. -/
theorem RepresentablyFlat.of_iso [RepresentablyFlat F] {G : C ⥤ D} (α : F ≅ G) :
    RepresentablyFlat G where
  cofiltered _ := IsCofiltered.of_equivalence (StructuredArrow.mapNatIso α)

theorem RepresentablyCoflat.of_iso [RepresentablyCoflat F] {G : C ⥤ D} (α : F ≅ G) :
    RepresentablyCoflat G where
  filtered _ := IsFiltered.of_equivalence (CostructuredArrow.mapNatIso α)

end

theorem representablyCoflat_op_iff : RepresentablyCoflat F.op ↔ RepresentablyFlat F := by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsFiltered (StructuredArrow X F)ᵒᵖ from isCofiltered_of_isFiltered_op _
    apply IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _).symm
  · suffices IsCofiltered (CostructuredArrow F.op (op X))ᵒᵖ from isFiltered_of_isCofiltered_op _
    suffices IsCofiltered (StructuredArrow X F)ᵒᵖᵒᵖ from
      IsCofiltered.of_equivalence (structuredArrowOpEquivalence _ _).op
    apply IsCofiltered.of_equivalence (opOpEquivalence _)

theorem representablyFlat_op_iff : RepresentablyFlat F.op ↔ RepresentablyCoflat F := by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsCofiltered (CostructuredArrow F X)ᵒᵖ from isFiltered_of_isCofiltered_op _
    apply IsCofiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  · suffices IsFiltered (StructuredArrow (op X) F.op)ᵒᵖ from isCofiltered_of_isFiltered_op _
    suffices IsFiltered (CostructuredArrow F X)ᵒᵖᵒᵖ from
      IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).op
    apply IsFiltered.of_equivalence (opOpEquivalence _)

instance [RepresentablyFlat F] : RepresentablyCoflat F.op :=
  (representablyCoflat_op_iff F).2 inferInstance

instance [RepresentablyCoflat F] : RepresentablyFlat F.op :=
  (representablyFlat_op_iff F).2 inferInstance

instance RepresentablyCoflat.comp (G : D ⥤ E) [RepresentablyCoflat F] [RepresentablyCoflat G] :
    RepresentablyCoflat (F ⋙ G) :=
  (representablyFlat_op_iff _).1 <| inferInstanceAs <| RepresentablyFlat (F.op ⋙ G.op)

lemma final_of_representablyFlat [h : RepresentablyFlat F] : F.Final where
  out _ := IsCofiltered.isConnected _

lemma initial_of_representablyCoflat [h : RepresentablyCoflat F] : F.Initial where
  out _ := IsFiltered.isConnected _

end RepresentablyFlat

section HasLimit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

theorem flat_of_preservesFiniteLimits [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] :
    RepresentablyFlat F :=
  ⟨fun X =>
    haveI : HasFiniteLimits (StructuredArrow X F) := by
      apply hasFiniteLimits_of_hasFiniteLimits_of_size.{v₁} (StructuredArrow X F)
      exact fun _ _ _ => HasLimitsOfShape.mk
    IsCofiltered.of_hasFiniteLimits _⟩

theorem coflat_of_preservesFiniteColimits [HasFiniteColimits C] (F : C ⥤ D)
    [PreservesFiniteColimits F] : RepresentablyCoflat F :=
  let _ := preservesFiniteLimits_op F
  (representablyFlat_op_iff _).1 (flat_of_preservesFiniteLimits _)

namespace PreservesFiniteLimitsOfFlat

open StructuredArrow

variable {J : Type v₁} [SmallCategory J] [FinCategory J] {K : J ⥤ C}
variable (F : C ⥤ D) [RepresentablyFlat F] {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))

/-- (Implementation).
Given a limit cone `c : cone K` and a cone `s : cone (K ⋙ F)` with `F` representably flat,
`s` can factor through `F.mapCone c`.
-/
noncomputable def lift : s.pt ⟶ F.obj c.pt :=
  let s' := IsCofiltered.cone (s.toStructuredArrow ⋙ StructuredArrow.pre _ K F)
  s'.pt.hom ≫
    (F.map <|
      hc.lift <|
        (Cone.postcompose
              ({ app := fun _ => 𝟙 _ } :
                (s.toStructuredArrow ⋙ pre s.pt K F) ⋙ proj s.pt F ⟶ K)).obj <|
          (StructuredArrow.proj s.pt F).mapCone s')

set_option backward.isDefEq.respectTransparency false in
theorem fac (x : J) : lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x := by
  simp [lift, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem uniq {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
    (f₁ f₂ : s.pt ⟶ F.obj c.pt) (h₁ : ∀ j : J, f₁ ≫ (F.mapCone c).π.app j = s.π.app j)
    (h₂ : ∀ j : J, f₂ ≫ (F.mapCone c).π.app j = s.π.app j) : f₁ = f₂ := by
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let α₁ : (F.mapCone c).toStructuredArrow ⋙ map f₁ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₁]) }
  let α₂ : (F.mapCone c).toStructuredArrow ⋙ map f₂ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₂]) }
  let c₁ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cone.postcompose (Functor.whiskerRight α₁ (pre s.pt K F) :)).obj
      (c.toStructuredArrowCone F f₁)
  let c₂ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cone.postcompose (Functor.whiskerRight α₂ (pre s.pt K F) :)).obj
      (c.toStructuredArrowCone F f₂)
  -- The two cones can then be combined and we may obtain a cone over the two cones since
  -- `StructuredArrow s.pt F` is cofiltered.
  let c₀ := IsCofiltered.cone (biconeMk _ c₁ c₂)
  let g₁ : c₀.pt ⟶ c₁.pt := c₀.π.app Bicone.left
  let g₂ : c₀.pt ⟶ c₂.pt := c₀.π.app Bicone.right
  -- Then `g₁.right` and `g₂.right` are two maps from the same cone into the `c`.
  have : ∀ j : J, g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j := by
    intro j
    injection c₀.π.naturality (BiconeHom.left j) with _ e₁
    injection c₀.π.naturality (BiconeHom.right j) with _ e₂
    convert e₁.symm.trans e₂ <;> simp [c₁, c₂]
  have : c.extend g₁.right = c.extend g₂.right := by
    unfold Cone.extend
    congr 1
    ext x
    apply this
  -- And thus they are equal as `c` is the limit.
  have : g₁.right = g₂.right := calc
    g₁.right = hc.lift (c.extend g₁.right) := by
      apply hc.uniq (c.extend _)
      simp
    _ = hc.lift (c.extend g₂.right) := by
      congr
    _ = g₂.right := by
      symm
      apply hc.uniq (c.extend _)
      simp
  -- Finally, since `fᵢ` factors through `F(gᵢ)`, the result follows.
  calc
    f₁ = 𝟙 _ ≫ f₁ := by simp
    _ = c₀.pt.hom ≫ F.map g₁.right := g₁.w
    _ = c₀.pt.hom ≫ F.map g₂.right := by rw [this]
    _ = 𝟙 _ ≫ f₂ := g₂.w.symm
    _ = f₂ := by simp

end PreservesFiniteLimitsOfFlat

/-- Representably flat functors preserve finite limits. -/
lemma preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits F := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  intro J _ _; constructor
  intro K; constructor
  intro c hc
  constructor
  exact
    { lift := PreservesFiniteLimitsOfFlat.lift F hc
      fac := PreservesFiniteLimitsOfFlat.fac F hc
      uniq := fun s m h => by
        apply PreservesFiniteLimitsOfFlat.uniq F hc
        · exact h
        · exact PreservesFiniteLimitsOfFlat.fac F hc s }

/-- Representably coflat functors preserve finite colimits. -/
lemma preservesFiniteColimits_of_coflat (F : C ⥤ D) [RepresentablyCoflat F] :
    PreservesFiniteColimits F :=
  letI _ := preservesFiniteLimits_of_flat F.op
  preservesFiniteColimits_of_op _

/-- If `C` is finitely complete, then `F : C ⥤ D` is representably flat iff it preserves
finite limits.
-/
lemma preservesFiniteLimits_iff_flat [HasFiniteLimits C] (F : C ⥤ D) :
    RepresentablyFlat F ↔ PreservesFiniteLimits F :=
  ⟨fun _ ↦ preservesFiniteLimits_of_flat F, fun _ ↦ flat_of_preservesFiniteLimits F⟩

/-- If `C` is finitely cocomplete, then `F : C ⥤ D` is representably coflat iff it preserves
finite colimits. -/
lemma preservesFiniteColimits_iff_coflat [HasFiniteColimits C] (F : C ⥤ D) :
    RepresentablyCoflat F ↔ PreservesFiniteColimits F :=
  ⟨fun _ => preservesFiniteColimits_of_coflat F, fun _ => coflat_of_preservesFiniteColimits F⟩

end HasLimit

section SmallCategory

variable {C D : Type u₁} [SmallCategory C] [SmallCategory D] (E : Type u₂) [Category.{u₁} E]


set_option backward.isDefEq.respectTransparency false in
/-- (Implementation)
The evaluation of `F.lan` at `X` is the colimit over the costructured arrows over `X`.
-/
noncomputable def lanEvaluationIsoColim (F : C ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
    (colimit.isColimit _)) (fun {G₁ G₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
      intro T
      have h₁ := fun (G : C ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
      have h₂ := congr_app (F.lanUnit.naturality φ) T.left
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ ⊢
      simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
      rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
        ι_colimMap, Functor.whiskerLeft_app]
      rfl)

variable {FE : E → E → Type*} {CE : E → Type u₁} [∀ X Y, FunLike (FE X Y) (CE X) (CE Y)]
    [ConcreteCategory E FE] [HasLimits E] [HasColimits E]
variable [ReflectsLimits (forget E)] [PreservesFilteredColimits (forget E)]
variable [PreservesLimits (forget E)]

/-- If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
noncomputable instance lan_preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  haveI : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim _ _ _).symm

instance lan_flat_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    RepresentablyFlat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) :=
  flat_of_preservesFiniteLimits _

variable [HasFiniteLimits C]

instance lan_preservesFiniteLimits_of_preservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] : PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  haveI := flat_of_preservesFiniteLimits F
  infer_instance

theorem flat_iff_lan_flat (F : C ⥤ D) :
    RepresentablyFlat F ↔ RepresentablyFlat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ TypeCat.{u₁}) :=
  ⟨fun _ => inferInstance, fun H => by
    haveI := preservesFiniteLimits_of_flat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ TypeCat.{u₁})
    haveI : PreservesFiniteLimits F := by
      apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
      intros; apply preservesLimit_of_lan_preservesLimit
    apply flat_of_preservesFiniteLimits⟩

/-- If `C` is finitely complete, then `F : C ⥤ D` preserves finite limits iff
`Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves finite limits.
-/
lemma preservesFiniteLimits_iff_lan_preservesFiniteLimits (F : C ⥤ D) :
    PreservesFiniteLimits F ↔ PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ TypeCat.{u₁}) :=
  ⟨fun _ ↦ inferInstance,
    fun _ ↦ preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁} _
      (fun _ _ _ ↦ preservesLimit_of_lan_preservesLimit _ _)⟩

end SmallCategory

section

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E)

attribute [local instance] IsCofiltered.isConnected IsFiltered.isConnected

instance (X : E) [RepresentablyFlat F] : (StructuredArrow.pre X F G).Final :=
  ⟨fun _ ↦ isConnected_of_equivalent (StructuredArrow.preEquivalence _ _).symm⟩

instance (X : E) [RepresentablyCoflat F] : (CostructuredArrow.pre F G X).Initial :=
  ⟨fun _ ↦ isConnected_of_equivalent (CostructuredArrow.preEquivalence _ _).symm⟩

set_option backward.isDefEq.respectTransparency false in
instance (X : E) [RepresentablyFlat F] [IsCofiltered (StructuredArrow X G)] :
    IsCofiltered (StructuredArrow X (F ⋙ G)) := by
  let T := StructuredArrow.pre X F G
  obtain ⟨Y⟩ := IsCofiltered.nonempty (C := StructuredArrow X G)
  obtain ⟨A⟩ := IsCofiltered.nonempty (C := StructuredArrow Y.right F)
  have : Nonempty (StructuredArrow X (F ⋙ G)) := ⟨.mk (Y.hom ≫ G.map A.hom)⟩
  suffices IsCofilteredOrEmpty (StructuredArrow X (F ⋙ G)) by constructor
  refine ⟨fun A B ↦ ?_, fun A B f g ↦ ?_⟩
  · let U := IsCofiltered.min (T.obj A) (T.obj B)
    let A' : StructuredArrow U.right F := .mk (IsCofiltered.minToLeft (T.obj A) (T.obj B)).right
    let B' : StructuredArrow U.right F := .mk (IsCofiltered.minToRight (T.obj A) (T.obj B)).right
    refine ⟨.mk <| U.hom ≫ G.map (IsCofiltered.min A' B').hom, ?_, ?_, trivial⟩
    · refine StructuredArrow.homMk (IsCofiltered.minToLeft A' B').right ?_
      simpa [← Functor.map_comp] using StructuredArrow.w _
    · refine StructuredArrow.homMk (IsCofiltered.minToRight A' B').right ?_
      simpa [← Functor.map_comp] using StructuredArrow.w _
  · let U := IsCofiltered.eq (T.map f) (T.map g)
    let A' : StructuredArrow _ F := .mk (IsCofiltered.eqHom (T.map f) (T.map g)).right
    let B' : StructuredArrow _ F := .mk (IsCofiltered.eqHom (T.map f) (T.map g) ≫ T.map f).right
    let f' : A' ⟶ B' := StructuredArrow.homMk f.right rfl
    let g' : A' ⟶ B' := StructuredArrow.homMk g.right
      congr($(IsCofiltered.eq_condition (T.map f) (T.map g)).right).symm
    refine ⟨.mk <| U.hom ≫ G.map (IsCofiltered.eq f' g').hom, ?_, ?_⟩
    · refine StructuredArrow.homMk (IsCofiltered.eqHom f' g').right ?_
      simpa [← Functor.map_comp] using StructuredArrow.w _
    · ext
      exact congr($(IsCofiltered.eq_condition f' g').right)

instance (X : E) [RepresentablyCoflat F] [h : IsFiltered (CostructuredArrow G X)] :
    IsFiltered (CostructuredArrow (F ⋙ G) X) := by
  rw [← isCofiltered_op_iff_isFiltered, IsCofiltered.iff_of_equivalence
    (costructuredArrowOpEquivalence _ _)] at h ⊢
  exact inferInstanceAs <| IsCofiltered (StructuredArrow (op X) (F.op ⋙ G.op))

instance (G : D ⥤ TypeCat) [RepresentablyFlat F] [IsCofiltered G.Elements] :
    IsCofiltered (F ⋙ G).Elements := by
  suffices h : IsCofiltered (StructuredArrow (PUnit) (F ⋙ G)) from
    .of_equivalence (CategoryOfElements.structuredArrowEquivalence _).symm
  have : IsCofiltered (StructuredArrow (PUnit) G) :=
    .of_equivalence (CategoryOfElements.structuredArrowEquivalence _)
  infer_instance

end

end CategoryTheory
