/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.RegularExtensive
/-!
This is #6877 and #6919.
-/

universe v u w

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

variable {C}

section ExtensiveSheaves

variable [Extensive C]

/-- A presieve is *extensive* if it is finite and its arrows induce an isomorphism from the
coproduct to the target. -/
class _root_.CategoryTheory.Presieve.extensive [HasFiniteCoproducts C] {X : C} (R : Presieve X) :
    Prop where
  /-- `R` consists of a finite collection of arrows that together induce an isomorphism from the
  coproduct of their sources. -/
  arrows_sigma_desc_iso : ∃ (α : Type) (_ : Fintype α) (Z : α → C) (π : (a : α) → (Z a ⟶ X)),
    R = Presieve.ofArrows Z π ∧ IsIso (Sigma.desc π)

instance {X : C} (S : Presieve X) [S.extensive] : S.hasPullbacks where
  has_pullbacks := by
    obtain ⟨_, _, _, _, hS, _⟩ := Presieve.extensive.arrows_sigma_desc_iso (R := S)
    intro _ _ f hf _ hg
    rw [hS] at hf hg
    cases' hg with b
    apply HasPullbacksOfInclusions.has_pullback f

namespace ExtensiveSheafConditionProof

lemma sigma_surjective {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X) :
    Function.Surjective (fun a => ⟨Z a, π a, Presieve.ofArrows.mk a⟩ :
    α → Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f }) :=
  fun ⟨_, ⟨_, hf⟩⟩ ↦ by cases' hf with a _; exact ⟨a, rfl⟩

open Opposite

instance {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} [Fintype α] :
    HasProduct fun (x : Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f }) ↦ (op x.1) :=
  haveI := Finite.of_surjective _ (sigma_surjective π)
  inferInstance

/-- The canonical map from `Equalizer.FirstObj` to a product indexed by `α` -/
noncomputable
def prod_map {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X) (F : Cᵒᵖ ⥤ Type max u v) :
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f })) => F.obj (op f.fst)) ⟶
    ∏ fun a => F.obj (op (Z a)) :=
  Pi.lift (fun a => Pi.π _ ⟨Z a, π a, Presieve.ofArrows.mk a⟩) ≫ 𝟙 _

/-- The inverse to `Equalizer.forkMap F (Presieve.ofArrows Z π)`. -/
noncomputable
def firstObj_to_base {α : Type} [Fintype α] {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X)
  (F : Cᵒᵖ ⥤ Type max u v) [PreservesFiniteProducts F] [IsIso (Sigma.desc π)] :
    Equalizer.FirstObj F (Presieve.ofArrows Z π) ⟶ F.obj (op X) :=
  haveI : PreservesLimit (Discrete.functor fun a => op (Z a)) F :=
    (PreservesFiniteProducts.preserves α).preservesLimit
  (prod_map π F) ≫ ((Limits.PreservesProduct.iso F (fun a => op <| Z a)).inv ≫
    F.map (opCoproductIsoProduct Z).inv ≫ F.map (inv (Sigma.desc π).op))

lemma comp_inv_desc_eq_ι {α : Type} [Fintype α] {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X)
    [IsIso (Sigma.desc π)] (a : α) : π a ≫ inv (Sigma.desc π) = Sigma.ι _ a := by
  simp only [IsIso.comp_inv_eq, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]

@[simp]
lemma PreservesProduct.isoInvCompMap {C : Type u} [Category C] {D : Type v} [Category D] (F : C ⥤ D)
    {J : Type w} {f : J → C} [HasProduct f] [HasProduct (fun j => F.obj (f j))]
    [PreservesLimit (Discrete.functor f) F] (j : J) :
    (PreservesProduct.iso F f).inv ≫ F.map (Pi.π _ j) = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (⟨j⟩ : Discrete J)

instance {α : Type} [Fintype α] {Z : α → C} {F : C ⥤ Type w}
    [PreservesFiniteProducts F] : PreservesLimit (Discrete.functor fun a => (Z a)) F :=
  (PreservesFiniteProducts.preserves α).preservesLimit

instance {X : C} (S : Presieve X) [S.extensive]
    {F : Cᵒᵖ ⥤ Type max u v} [PreservesFiniteProducts F] : IsIso (Equalizer.forkMap F S) := by
  obtain ⟨α, _, Z, π, hS, _⟩ := Presieve.extensive.arrows_sigma_desc_iso (R := S)
  subst hS
  refine' ⟨firstObj_to_base π F,_,_⟩
  · simp only [firstObj_to_base, ← Category.assoc, Functor.map_inv,
      IsIso.comp_inv_eq, Category.id_comp, ← Functor.mapIso_inv, Iso.comp_inv_eq,
      Functor.mapIso_hom, Iso.comp_inv_eq, ← Functor.map_comp,
      desc_op_comp_opCoproductIsoProduct_hom, PreservesProduct.iso_hom, map_lift_piComparison,
      colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    funext s
    ext a
    simp only [prod_map, types_comp_apply, types_id_apply, Types.Limit.lift_π_apply,
      Fan.mk_pt, Equalizer.forkMap, Fan.mk_π_app, Types.pi_lift_π_apply]
  · refine Limits.Pi.hom_ext _ _ (fun f => ?_)
    simp only [Equalizer.forkMap, Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app,
      Category.id_comp]
    obtain ⟨a, ha⟩ := sigma_surjective π f
    rw [firstObj_to_base, Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← op_inv, ← op_comp, ← ha, comp_inv_desc_eq_ι, ← Functor.map_comp,
      opCoproductIsoProduct_inv_comp_ι, PreservesProduct.isoInvCompMap F a]
    simp only [prod_map, Category.comp_id, limit.lift_π, Fan.mk_pt, Fan.mk_π_app]

end ExtensiveSheafConditionProof

open ExtensiveSheafConditionProof in
lemma isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.extensive]
    (F : Cᵒᵖ ⥤ Type max u v) [PreservesFiniteProducts F] :
    Presieve.IsSheafFor F S := by
  refine' (Equalizer.Presieve.sheaf_condition F S).2 _
  rw [Limits.Types.type_equalizer_iff_unique]
  dsimp [Equalizer.FirstObj]
  suffices : IsIso (Equalizer.forkMap F S)
  · intro y _
    refine' ⟨inv (Equalizer.forkMap F S) y, _, fun y₁ hy₁ => _⟩
    · change (inv (Equalizer.forkMap F S) ≫ (Equalizer.forkMap F S)) y = y
      rw [IsIso.inv_hom_id, types_id_apply]
    · replace hy₁ := congr_arg (inv (Equalizer.forkMap F S)) hy₁
      change ((Equalizer.forkMap F S) ≫ inv (Equalizer.forkMap F S)) _ = _ at hy₁
      rwa [IsIso.hom_inv_id, types_id_apply] at hy₁
  infer_instance

end ExtensiveSheaves

section RegularSheaves

open Opposite

/-- A presieve is *regular* if it consists of a single effective epimorphism. -/
class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : ∃ (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) ↦ Y)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f

/--
The map to the explicit equalizer used in the sheaf condition.
-/
def MapToEqualizer (P : Cᵒᵖ ⥤ Type (max u v)) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  fun t ↦ ⟨P.map f.op t, by
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _;
    simp_rw [← P.map_comp, ← op_comp, w] ⟩

/--
The sheaf condition with respect to regular presieves, given the existence of the relavant pullback.
-/
def EqualizerCondition (P : Cᵒᵖ ⥤ Type (max u v)) : Prop :=
  ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], Function.Bijective
    (MapToEqualizer P π (pullback.fst (f := π) (g := π)) (pullback.snd (f := π) (g := π))
    pullback.condition)

/--
The `FirstObj` in the sheaf condition diagram is isomorphic to `F` applied to `X`.
-/
noncomputable
def EqualizerFirstObjIso (F : Cᵒᵖ ⥤ Type (max u v)) {B X : C} (π : X ⟶ B) :
    Equalizer.FirstObj F (Presieve.singleton π) ≅ F.obj (op X) :=
  CategoryTheory.Equalizer.firstObjEqFamily F (Presieve.singleton π) ≪≫
  { hom := fun e ↦ e π (Presieve.singleton_self π)
    inv := fun e _ _ h ↦ by
      induction h with
      | mk => exact e
    hom_inv_id := by
      funext _ _ _ h
      induction h with
      | mk => rfl
    inv_hom_id := by aesop }

instance {B X : C} (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π] :
    (Presieve.singleton π).hasPullbacks where
  has_pullbacks hf _ hg := by
    cases hf
    cases hg
    infer_instance

/--
The `SecondObj` in the sheaf condition diagram is isomorphic to `F` applied to the pullback of `π`
with itself
-/
noncomputable
def EqualizerSecondObjIso (F : Cᵒᵖ ⥤ Type (max u v)) {B X : C} (π : X ⟶ B) [EffectiveEpi π]
    [HasPullback π π] :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Limits.pullback π π)) :=
  Types.productIso.{max u v, max u v} _ ≪≫
  { hom := fun e ↦ e (⟨X, ⟨π, Presieve.singleton_self π⟩⟩, ⟨X, ⟨π, Presieve.singleton_self π⟩⟩)
    inv := fun x ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩ ↦ by
      induction h₁
      induction h₂
      exact x
    hom_inv_id := by
      funext _ ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩
      induction h₁
      induction h₂
      rfl
    inv_hom_id := by aesop }

lemma EqualizerCondition.isSheafFor {B : C} {S : Presieve B} [S.regular] [S.hasPullbacks]
    {F : Cᵒᵖ ⥤ Type (max u v)}
    (hFecs : EqualizerCondition F) : S.IsSheafFor F := by
  obtain ⟨X, π, ⟨hS, πsurj⟩⟩ := Presieve.regular.single_epi (R := S)
  rw [Presieve.ofArrows_pUnit] at hS
  haveI : (Presieve.singleton π).hasPullbacks := by rw [← hS]; infer_instance
  haveI : HasPullback π π :=
    Presieve.hasPullbacks.has_pullbacks (Presieve.singleton.mk) (Presieve.singleton.mk)
  subst hS
  rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
  intro y h
  specialize hFecs X B π
  have hy : F.map (pullback.fst (f := π) (g := π)).op ((EqualizerFirstObjIso F π).hom y) =
      F.map (pullback.snd (f := π) (g := π)).op ((EqualizerFirstObjIso F π).hom y) :=
    calc
      _ = (Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso F π).hom) y := by
          simp [EqualizerSecondObjIso, EqualizerFirstObjIso, Equalizer.Presieve.firstMap]
      _ = (Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom)
          y := by simp only [Equalizer.Presieve.SecondObj, types_comp_apply]; rw [h]
      _ = _ := by
          simp [EqualizerSecondObjIso, EqualizerFirstObjIso, Equalizer.Presieve.secondMap]
  obtain ⟨x, ⟨hx₁, hx₂⟩⟩ : ∃! x, F.map π.op x = (EqualizerFirstObjIso F π).hom y
  · rw [Function.bijective_iff_existsUnique] at hFecs
    specialize hFecs ⟨(EqualizerFirstObjIso F π).hom y, hy⟩
    obtain ⟨x, ⟨hx₁, hx₂⟩⟩ := hFecs
    refine ⟨x, ⟨Subtype.ext_iff.mp hx₁, ?_⟩⟩
    intros
    apply hx₂
    rwa [Subtype.ext_iff]
  have fork_comp : Equalizer.forkMap F (Presieve.singleton π) ≫ (EqualizerFirstObjIso F π).hom =
      F.map π.op := by ext; simp [EqualizerFirstObjIso, Equalizer.forkMap]
  rw [← fork_comp] at hx₁ hx₂
  refine ⟨x, ⟨?_, ?_⟩⟩
  · apply_fun (EqualizerFirstObjIso F π).hom using injective_of_mono (EqualizerFirstObjIso F π).hom
    exact hx₁
  · intro z hz
    apply_fun (EqualizerFirstObjIso F π).hom at hz
    exact hx₂ z hz

lemma IsSheafForRegular.equalizerCondition {F : Cᵒᵖ ⥤ Type (max u v)}
    (hSF : ∀ {B : C} (S : Presieve B) [S.regular] [S.hasPullbacks], S.IsSheafFor F) :
    EqualizerCondition F := by
  intro X B π _ _
  haveI : (Presieve.singleton π).regular :=
    ⟨X, π, ⟨(Presieve.ofArrows_pUnit π).symm, inferInstance⟩⟩
  specialize hSF (Presieve.singleton π)
  rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hSF
  rw [Function.bijective_iff_existsUnique]
  intro ⟨b, hb⟩
  specialize hSF ((EqualizerFirstObjIso F π).inv b) ?_
  · apply_fun (EqualizerSecondObjIso F π).hom using injective_of_mono _
    calc
      _ = F.map (pullback.fst (f := π) (g := π)).op b := by
        simp only [Equalizer.Presieve.SecondObj, EqualizerSecondObjIso, Equalizer.Presieve.firstMap,
          EqualizerFirstObjIso, Iso.trans_inv, types_comp_apply, Equalizer.firstObjEqFamily_inv,
          Iso.trans_hom, Types.productIso_hom_comp_eval_apply, Types.Limit.lift_π_apply', Fan.mk_pt,
          Fan.mk_π_app]; rfl
      _ = F.map (pullback.snd (f := π) (g := π)).op b := hb
      _ = ((EqualizerFirstObjIso F π).inv ≫ Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫
        (EqualizerSecondObjIso F π).hom) b := by
          simp only [EqualizerFirstObjIso, Iso.trans_inv, Equalizer.Presieve.SecondObj,
            Equalizer.Presieve.secondMap, EqualizerSecondObjIso, Iso.trans_hom,
            Types.productIso_hom_comp_eval, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, types_comp_apply,
            Equalizer.firstObjEqFamily_inv, Types.Limit.lift_π_apply']; rfl
  · obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := hSF
    refine ⟨a, ⟨?_, ?_⟩⟩
    · ext
      dsimp [MapToEqualizer]
      apply_fun (EqualizerFirstObjIso F π).hom at ha₁
      simp only [inv_hom_id_apply] at ha₁
      rw [← ha₁]
      simp only [EqualizerFirstObjIso, Equalizer.forkMap, Iso.trans_hom, types_comp_apply,
        Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    · intro y hy
      apply ha₂
      apply_fun (EqualizerFirstObjIso F π).hom using injective_of_mono _
      simp only [inv_hom_id_apply]
      simp only [MapToEqualizer, Set.mem_setOf_eq, Subtype.mk.injEq] at hy
      rw [← hy]
      simp only [EqualizerFirstObjIso, Equalizer.forkMap, Iso.trans_hom, types_comp_apply,
        Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]

lemma isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X]
    (F : Cᵒᵖ ⥤ Type (max u v)) : S.IsSheafFor F := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  let g := Projective.factorThru (𝟙 _) f
  have hfg : g ≫ f = 𝟙 _ := by
    simp only [Projective.factorThru_comp]
  intro y hy
  refine' ⟨F.map g.op <| y f <| Presieve.ofArrows.mk (), fun Z h hZ => _, fun z hz => _⟩
  · cases' hZ with u
    have := hy (f₁ := f) (f₂ := f) (𝟙 Y) (f ≫ g) (Presieve.ofArrows.mk ())
        (Presieve.ofArrows.mk ()) ?_
    · rw [op_id, F.map_id, types_id_apply] at this
      rw [← types_comp_apply (F.map g.op) (F.map f.op), ← F.map_comp, ← op_comp]
      exact this.symm
    · rw [Category.id_comp, Category.assoc, hfg, Category.comp_id]
  · have := congr_arg (F.map g.op) <| hz f (Presieve.ofArrows.mk ())
    rwa [← types_comp_apply (F.map f.op) (F.map g.op), ← F.map_comp, ← op_comp, hfg, op_id,
      F.map_id, types_id_apply] at this

lemma isSheaf_iff_equalizerCondition (F : Cᵒᵖ ⥤ Type (max u v)) [Preregular C] [HasPullbacks C] :
    Presieve.IsSheaf (regularCoverage C).toGrothendieck F ↔ EqualizerCondition F := by
  rw [Presieve.isSheaf_coverage]
  refine ⟨?_, ?_⟩
  · intro h
    apply IsSheafForRegular.equalizerCondition
    intro B S _ _
    apply h S
    obtain ⟨Y, f, rfl, _⟩ := Presieve.regular.single_epi (R := S)
    use Y, f
  · intro h X S ⟨Y, f, hh⟩
    haveI : S.regular := ⟨Y, f, hh⟩
    exact h.isSheafFor

lemma isSheaf_of_projective (F : Cᵒᵖ ⥤ Type (max u v)) [Preregular C] [∀ (X : C), Projective X] :
    Presieve.IsSheaf (regularCoverage C).toGrothendieck F := by
  rw [Presieve.isSheaf_coverage]
  intro X S ⟨Y, f, hh⟩
  haveI : S.regular := ⟨Y, f, hh⟩
  exact isSheafFor_regular_of_projective _ _

end RegularSheaves

end CategoryTheory
