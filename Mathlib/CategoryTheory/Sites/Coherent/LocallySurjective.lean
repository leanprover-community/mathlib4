import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveTopology
import Mathlib.CategoryTheory.Sites.EpiMono

universe v u w

open CategoryTheory Sheaf Limits Opposite

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category.{v} D] [ConcreteCategory.{v} D]

variable [Preregular C]

lemma regularTopology.isLocallySurjective_iff {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G) :
    Presheaf.IsLocallySurjective (regularTopology C) f ↔
      ∀ (S : C) (y : G.obj ⟨S⟩), (∃ (S' : C) (φ : S' ⟶ S) (_ : EffectiveEpi φ) (x : F.obj ⟨S'⟩),
        f.app ⟨S'⟩ x = G.map ⟨φ⟩ y) := by
  constructor
  · intro ⟨h⟩ S y
    specialize h y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at h
    obtain ⟨S', π, h, h'⟩ := h
    exact ⟨S', π, h, h'⟩
  · intro h
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨S', π, h, h'⟩ := h _ y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
    exact ⟨S', π, h, h'⟩

variable [FinitaryExtensive C]

lemma regularTopology.isLocallySurjective_sheafOfTypes
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
    have := preservesLimitsOfShapeOfEquiv (Discrete.opposite α).symm G
    apply Concrete.isLimit_ext _ (isLimitOfPreserves G (coproductIsCoproduct Z).op)
    intro ⟨⟨a⟩⟩
    simp only [Functor.comp_obj, Functor.op_obj, Discrete.functor_obj, Functor.mapCone_pt,
      Cocone.op_pt, Cofan.mk_pt, Functor.const_obj_obj, Functor.mapCone_π_app, Cocone.op_π,
      NatTrans.op_app, Cofan.mk_ι_app, Functor.mapIso_symm, Iso.symm_hom, Iso.trans_hom,
      Functor.mapIso_inv, types_comp_apply, i', ← NatTrans.naturality_apply]
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

variable (A : Type*) [Category.{v} A] [ConcreteCategory.{v} A] [PreservesFiniteProducts (forget A)]
variable {F G : Sheaf (coherentTopology C) A} (f : F ⟶ G)

noncomputable instance (F : Sheaf (coherentTopology C) A) : PreservesFiniteProducts F.val :=
  ((Presheaf.isSheaf_iff_preservesFiniteProducts F.val).1
    ((Presheaf.isSheaf_coherent_iff_regular_and_extensive F.val).mp F.cond).1).some

lemma coherentTopology.isLocallySurjective_iff : IsLocallySurjective f ↔
    Presheaf.IsLocallySurjective (regularTopology C) f.val := by
  constructor
  · rw [Sheaf.IsLocallySurjective, Presheaf.isLocallySurjective_iff_whisker_forget,
      Presheaf.isLocallySurjective_iff_whisker_forget (J := regularTopology C)]
    exact regularTopology.isLocallySurjective_sheafOfTypes _
  · refine Presheaf.isLocallySurjectiveMono (J := regularTopology C) ?_ _
    rw [← extensive_regular_generate_coherent]
    exact (Coverage.gi _).gc.monotone_l le_sup_right

variable {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]

lemma extensiveTopology.surjective_of_isLocallySurjective_sheafOfTypes
    (h : Presheaf.IsLocallySurjective (extensiveTopology C) f) {X : C} :
      Function.Surjective (f.app (op X)) := by
  intro x
  replace h := h.1 x
  rw [mem_sieves_iff_contains_colimit_cofan] at h
  obtain ⟨α, _, Y, π, h, h'⟩ := h
  let y : (a : α) → (F.obj ⟨Y a⟩) := fun a ↦ (h' a).choose
  let _ : Fintype α := Fintype.ofFinite _
  have := preservesLimitsOfShapeOfEquiv (Discrete.opposite α).symm F
  let ht := (Types.productLimitCone (fun a ↦ F.obj ⟨Y a⟩)).isLimit
  let ht' := (Functor.Initial.isLimitWhiskerEquiv (Discrete.opposite α).inverse
    (Cocone.op (Cofan.mk X π))).symm h.some.op
  let i : ((a : α) → (F.obj ⟨Y a⟩)) ≅ (F.obj ⟨X⟩) :=
    ht.conePointsIsoOfNatIso (isLimitOfPreserves F ht')
      (Discrete.natIso (fun _ ↦ (Iso.refl (F.obj ⟨_⟩))))
  refine ⟨i.hom y, ?_⟩
  have := preservesLimitsOfShapeOfEquiv (Discrete.opposite α).symm G
  apply Concrete.isLimit_ext _ (isLimitOfPreserves G ht')
  intro ⟨a⟩
  simp only [Functor.comp_obj, Discrete.opposite_inverse_obj, Functor.op_obj, Discrete.functor_obj,
    Functor.mapCone_pt, Cone.whisker_pt, Cocone.op_pt, Cofan.mk_pt, Functor.const_obj_obj,
    Functor.mapCone_π_app, Cone.whisker_π, Cocone.op_π, whiskerLeft_app, NatTrans.op_app,
    Cofan.mk_ι_app]
  have : f.app ⟨Y a⟩ (y a) = G.map (π a).op x := (h' a).choose_spec
  change _ = G.map (π a).op x
  erw [← this, ← NatTrans.naturality_apply (φ := f)]
  apply congrArg
  change (i.hom ≫ F.map (π a).op) y = _
  erw [IsLimit.map_π]
  rfl

variable {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
    [PreservesFiniteProducts (forget A)]

lemma extensiveTopology.presheafIsLocallySurjective_iff :
    Presheaf.IsLocallySurjective (extensiveTopology C) f ↔
      ∀ (X : C), Function.Surjective (f.app (op X)) := by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget (J := extensiveTopology C)]
    exact fun h _ ↦ surjective_of_isLocallySurjective_sheafOfTypes (whiskerRight f (forget A)) h
  · intro h
    refine ⟨fun {X} y ↦ ?_⟩
    obtain ⟨x, hx⟩ := h X y
    convert (extensiveTopology C).top_mem' X
    rw [← Sieve.id_mem_iff_eq_top]
    simp [Presheaf.imageSieve]
    exact ⟨x, hx⟩

variable {F G : Sheaf (extensiveTopology C) A} (f : F ⟶ G)  [PreservesFiniteProducts (forget A)]

lemma extensiveTopology.isLocallySurjective_iff :
    IsLocallySurjective f ↔
      ∀ (X : C), Function.Surjective (f.val.app (op X)) :=
  extensiveTopology.presheafIsLocallySurjective_iff _ f.val

end CategoryTheory
