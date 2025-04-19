/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveTopology
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.LocallySurjective
/-!

# Locally surjective morphisms of coherent sheaves

This file characterises locally surjective morphisms of presheaves for the coherent, regular
and extensive topologies.

## Main results

* `regularTopology.isLocallySurjective_iff` A morphism of presheaves `f : F ⟶ G` is locally
  surjective for the regular topology iff for every object `X` of `C`, and every `y : G(X)`, there
  is an effective epimorphism `φ : X' ⟶ X` and an `x : F(X)` such that `f_{X'}(x) = G(φ)(y)`.

* `coherentTopology.isLocallySurjective_iff` a morphism of sheaves for the coherent topology on a
  preregular finitary extensive category is locally surjective if and only if it is
  locally surjective for the regular topology.

* `extensiveTopology.isLocallySurjective_iff` a morphism of sheaves for the extensive topology on a
  finitary extensive category is locally surjective iff it is objectwise surjective.
-/

universe w

open CategoryTheory Sheaf Limits Opposite

namespace CategoryTheory

variable {C : Type*} (D : Type*) [Category C] [Category D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

lemma regularTopology.isLocallySurjective_iff [Preregular C] {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G) :
    Presheaf.IsLocallySurjective (regularTopology C) f ↔
      ∀ (X : C) (y : ToType (G.obj ⟨X⟩)), (∃ (X' : C) (φ : X' ⟶ X) (_ : EffectiveEpi φ)
        (x : ToType (F.obj ⟨X'⟩)),
        f.app ⟨X'⟩ x = G.map ⟨φ⟩ y) := by
  constructor
  · intro ⟨h⟩ X y
    specialize h y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at h
    obtain ⟨X', π, h, h'⟩ := h
    exact ⟨X', π, h, h'⟩
  · intro h
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨X', π, h, h'⟩ := h _ y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
    exact ⟨X', π, h, h'⟩

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
lemma extensiveTopology.surjective_of_isLocallySurjective_sheaf_of_types [FinitaryPreExtensive C]
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      (h : Presheaf.IsLocallySurjective (extensiveTopology C) f) {X : C} :
        Function.Surjective (f.app (op X)) := by
  intro x
  replace h := h.1 x
  rw [mem_sieves_iff_contains_colimit_cofan] at h
  obtain ⟨α, _, Y, π, h, h'⟩ := h
  let y : (a : α) → (F.obj ⟨Y a⟩) := fun a ↦ (h' a).choose
  let _ : Fintype α := Fintype.ofFinite _
  let ht := (Types.productLimitCone (fun a ↦ F.obj ⟨Y a⟩)).isLimit
  let ht' := (Functor.Initial.isLimitWhiskerEquiv (Discrete.opposite α).inverse
    (Cocone.op (Cofan.mk X π))).symm h.some.op
  let i : ((a : α) → (F.obj ⟨Y a⟩)) ≅ (F.obj ⟨X⟩) :=
    ht.conePointsIsoOfNatIso (isLimitOfPreserves F ht')
      (Discrete.natIso (fun _ ↦ (Iso.refl (F.obj ⟨_⟩))))
  refine ⟨i.hom y, ?_⟩
  apply Concrete.isLimit_ext _ (isLimitOfPreserves G ht')
  intro ⟨a⟩
  simp only [Functor.comp_obj, Discrete.opposite_inverse_obj, Functor.op_obj, Discrete.functor_obj,
    Functor.mapCone_pt, Cone.whisker_pt, Cocone.op_pt, Cofan.mk_pt, Functor.const_obj_obj,
    Functor.mapCone_π_app, Cone.whisker_π, Cocone.op_π, whiskerLeft_app, NatTrans.op_app,
    Cofan.mk_ι_app]
  rw [← (h' a).choose_spec]
  erw [← NatTrans.naturality_apply (φ := f)]
  change f.app _ ((i.hom ≫ F.map (π a).op) y) = _
  erw [IsLimit.map_π]
  rfl

@[deprecated (since := "2024-11-26")]
alias extensiveTopology.surjective_of_isLocallySurjective_sheafOfTypes :=
  extensiveTopology.surjective_of_isLocallySurjective_sheaf_of_types

lemma extensiveTopology.presheafIsLocallySurjective_iff [FinitaryPreExtensive C] {F G : Cᵒᵖ ⥤ D}
    (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      [PreservesFiniteProducts (forget D)] : Presheaf.IsLocallySurjective (extensiveTopology C) f ↔
        ∀ (X : C), Function.Surjective (f.app (op X)) := by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget (J := extensiveTopology C)]
    exact fun h _ ↦ surjective_of_isLocallySurjective_sheaf_of_types (whiskerRight f (forget D)) h
  · intro h
    refine ⟨fun {X} y ↦ ?_⟩
    obtain ⟨x, hx⟩ := h X y
    convert (extensiveTopology C).top_mem' X
    rw [← Sieve.id_mem_iff_eq_top]
    simpa [Presheaf.imageSieve] using ⟨x, hx⟩

lemma extensiveTopology.isLocallySurjective_iff [FinitaryExtensive C]
    {F G : Sheaf (extensiveTopology C) D} (f : F ⟶ G)
      [PreservesFiniteProducts (forget D)] : IsLocallySurjective f ↔
        ∀ (X : C), Function.Surjective (f.val.app (op X)) :=
  extensiveTopology.presheafIsLocallySurjective_iff _ f.val

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
lemma regularTopology.isLocallySurjective_sheaf_of_types [Preregular C] [FinitaryPreExtensive C]
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      (h : Presheaf.IsLocallySurjective (coherentTopology C) f) :
        Presheaf.IsLocallySurjective (regularTopology C) f where
  imageSieve_mem y := by
    replace h := h.1 y
    rw [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily] at h
    obtain ⟨α, _, Z, π, h, h'⟩ := h
    rw [mem_sieves_iff_hasEffectiveEpi]
    let x : (a : α) → (F.obj ⟨Z a⟩) := fun a ↦ (h' a).choose
    let _ : Fintype α := Fintype.ofFinite _
    let i' : ((a : α) → (F.obj ⟨Z a⟩)) ≅ (F.obj ⟨∐ Z⟩) := (Types.productIso _).symm ≪≫
      (PreservesProduct.iso F _).symm ≪≫ F.mapIso (opCoproductIsoProduct _).symm
    refine ⟨∐ Z, Sigma.desc π, inferInstance, i'.hom x, ?_⟩
    have := preservesLimitsOfShape_of_equiv (Discrete.opposite α).symm G
    apply Concrete.isLimit_ext _ (isLimitOfPreserves G (coproductIsCoproduct Z).op)
    intro ⟨⟨a⟩⟩
    simp only [Functor.comp_obj, Functor.op_obj, Discrete.functor_obj, Functor.mapCone_pt,
      Cocone.op_pt, Cofan.mk_pt, Functor.const_obj_obj, Functor.mapCone_π_app, Cocone.op_π,
      NatTrans.op_app, Cofan.mk_ι_app, Functor.mapIso_symm, Iso.symm_hom, Iso.trans_hom,
      Functor.mapIso_inv, types_comp_apply, i', ← NatTrans.naturality_apply f (Sigma.ι Z a).op]
    have : f.app ⟨Z a⟩ (x a) = G.map (π a).op y := (h' a).choose_spec
    convert this
    · change F.map _ (F.map _ _) = _
      rw [← FunctorToTypes.map_comp_apply, opCoproductIsoProduct_inv_comp_ι, ← piComparison_comp_π]
      change ((PreservesProduct.iso F _).hom ≫ _) _ = _
      have := Types.productIso_hom_comp_eval (fun a ↦ F.obj (op (Z a))) a
      rw [← Iso.eq_inv_comp] at this
      simp only [types_comp_apply, inv_hom_id_apply, congrFun this x]
    · change G.map _ (G.map _ _) = _
      simp only [← FunctorToTypes.map_comp_apply, ← op_comp, Sigma.ι_desc]

@[deprecated (since := "2024-11-26")] alias regularTopology.isLocallySurjective_sheafOfTypes :=
regularTopology.isLocallySurjective_sheaf_of_types

lemma coherentTopology.presheafIsLocallySurjective_iff {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G)
    [Preregular C] [FinitaryPreExtensive C] [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      [PreservesFiniteProducts (forget D)] :
        Presheaf.IsLocallySurjective (coherentTopology C) f ↔
          Presheaf.IsLocallySurjective (regularTopology C) f := by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget,
      Presheaf.isLocallySurjective_iff_whisker_forget (J := regularTopology C)]
    exact regularTopology.isLocallySurjective_sheaf_of_types _
  · refine Presheaf.isLocallySurjective_of_le (J := regularTopology C) ?_ _
    rw [← extensive_regular_generate_coherent]
    exact (Coverage.gi _).gc.monotone_l le_sup_right

lemma coherentTopology.isLocallySurjective_iff [Preregular C] [FinitaryExtensive C]
    {F G : Sheaf (coherentTopology C) D} (f : F ⟶ G) [PreservesFiniteProducts (forget D)] :
      IsLocallySurjective f ↔ Presheaf.IsLocallySurjective (regularTopology C) f.val :=
  presheafIsLocallySurjective_iff _ f.val

end CategoryTheory
