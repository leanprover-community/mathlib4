import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Condensed.Module

universe u w

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.hasCoeToSort
  CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory Sheaf Limits Opposite

namespace CategoryTheory

universe v₁ u₁

variable {C D : Type*} [Category C] [Category.{v₁} D] [ConcreteCategory.{v₁} D]
  [PreservesFiniteProducts (forget D)]
  (F : Cᵒᵖ ⥤ D) [PreservesFiniteProducts F]
  {α : Type} [Finite α] (Z : α → C) (c : Cofan Z) (hc : IsColimit c)

lemma presheaf_preserves_ext (x y : F.obj (op c.pt))
    (h : ∀ a, F.map (c.inj a).op x = F.map (c.inj a).op y) :
    x = y := by
  let _ : Fintype α := Fintype.ofFinite _
  apply Concrete.isLimit_ext _ (isLimitOfPreserves F (Cofan.IsColimit.op hc))
  exact fun ⟨a⟩ ↦ h a

lemma isLocallySurjectiveMono {J K : GrothendieckTopology C} (hJK : J ≤ K) {F G : Cᵒᵖ ⥤ D}
    (f : F ⟶ G) (h : Presheaf.IsLocallySurjective J f) : Presheaf.IsLocallySurjective K f where
  imageSieve_mem s := by apply hJK; exact h.1 _

variable [Preregular C] [FinitaryExtensive C]

lemma coherentTopology.isLocallySurjective_sheafOfTypes
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
    (h : Presheaf.IsLocallySurjective (coherentTopology C) f) :
    Presheaf.IsLocallySurjective (regularTopology C) f := by
  obtain ⟨h⟩ := h
  constructor
  intro S y
  specialize h y
  rw [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily] at h
  obtain ⟨α, _, Z, π, h, h'⟩ := h
  rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
  refine ⟨∐ Z, Sigma.desc π, inferInstance, ?_⟩
  let x : (a : α) → (F.obj ⟨Z a⟩) := fun a ↦ (h' a).choose
  let i : ((a : α) → (F.obj ⟨Z a⟩)) ≅ (∏ᶜ (fun (a : α) ↦ F.obj ⟨Z a⟩)) :=
    (Types.productIso _).symm
  let _ : Fintype α := Fintype.ofFinite _
  let i' : (∏ᶜ (fun (a : α) ↦ F.obj ⟨Z a⟩)) ≅ (F.obj ⟨∐ Z⟩) :=
    (PreservesProduct.iso F _).symm ≪≫ F.mapIso (opCoproductIsoProduct _).symm
  use i'.hom (i.hom x)
  apply presheaf_preserves_ext G Z _ (coproductIsCoproduct Z)
  intro a
  simp only [Cofan.mk_pt, cofan_mk_inj, Functor.mapIso_symm, Iso.symm_hom, Iso.trans_hom,
    Functor.mapIso_inv, types_comp_apply, i', i]
  rw [← NatTrans.naturality_apply]
  have : f.app ⟨Z a⟩ (x a) = G.map (π a).op y := (h' a).choose_spec
  convert this
  · change F.map _ (F.map _ _) = _
    rw [← FunctorToTypes.map_comp_apply, opCoproductIsoProduct_inv_comp_ι]
    rw [← piComparison_comp_π F (fun a ↦ ⟨Z a⟩) a]
    have h : (piComparison F fun a ↦ { unop := Z a }) =
      (PreservesProduct.iso F _).hom := rfl
    rw [h]
    simp only [types_comp_apply, inv_hom_id_apply]
    have := Types.productIso_hom_comp_eval (fun a ↦ F.obj (op (Z a))) a
    rw [← Iso.eq_inv_comp] at this
    have := congrFun this x
    rw [this]
    rfl
  · change G.map _ (G.map _ _) = _
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp, Sigma.ι_desc]


variable (A : Type*) [Category.{v₁} A] [ConcreteCategory.{v₁} A] [HasFiniteProducts A]
  [PreservesFiniteProducts (forget A)]
variable {F G : Sheaf (coherentTopology C) A} (f : F ⟶ G)

noncomputable instance (F : Sheaf (coherentTopology C) A) : PreservesFiniteProducts F.val :=
  ((Presheaf.isSheaf_iff_preservesFiniteProducts F.val).1
    ((Presheaf.isSheaf_coherent_iff_regular_and_extensive F.val).mp F.cond).1).some

lemma coherentTopology.isLocallySurjective_iff : IsLocallySurjective f ↔
    Presheaf.IsLocallySurjective (regularTopology C) f.val := by
  constructor
  · rw [Sheaf.IsLocallySurjective, Presheaf.isLocallySurjective_iff_whisker_forget,
      Presheaf.isLocallySurjective_iff_whisker_forget (J := regularTopology C)]
    exact coherentTopology.isLocallySurjective_sheafOfTypes _
  · have : regularTopology C ≤ coherentTopology C := by
      rw [← extensive_regular_generate_coherent]
      exact (Coverage.gi _).gc.monotone_l le_sup_right
    exact isLocallySurjectiveMono this _

end CategoryTheory

namespace CondensedSet

variable {X Y : CondensedSet.{u}} (f : X ⟶ Y)

lemma isLocallySurjective_iff_epi : IsLocallySurjective f ↔ Epi f  :=
  Sheaf.isLocallySurjective_iff_epi f

lemma epi_iff_exists_local_surjection : Epi f ↔
    ∀ (S : CompHaus) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi, coherentTopology.isLocallySurjective_iff]
  constructor
  · intro ⟨h⟩ S y
    specialize h y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at h
    obtain ⟨S', π, h, h'⟩ := h
    refine ⟨S', π, ?_, h'⟩
    rwa [← ((CompHaus.effectiveEpi_tfae _).out 0 2 :)]
  · intro h
    constructor
    intro S y
    obtain ⟨S', φ, hφ, h⟩ := h S y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
    refine ⟨S', φ, ?_, h⟩
    rwa [((CompHaus.effectiveEpi_tfae _).out 0 2 :)]

end CondensedSet

namespace CondensedMod

variable (R : Type (u+1)) [Ring R] {X Y : CondensedMod.{u} R} (f : X ⟶ Y)

lemma isLocallySurjective_iff_epi :
    IsLocallySurjective f ↔ Epi f  :=
  Sheaf.isLocallySurjective_iff_epi' _ f

lemma epi_iff_exists_local_surjection : Epi f ↔
    ∀ (S : CompHaus) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi, coherentTopology.isLocallySurjective_iff]
  constructor
  · intro ⟨h⟩ S y
    specialize h y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at h
    obtain ⟨S', π, h, h'⟩ := h
    refine ⟨S', π, ?_, h'⟩
    rwa [← ((CompHaus.effectiveEpi_tfae _).out 0 2 :)]
  · intro h
    constructor
    intro S y
    obtain ⟨S', φ, hφ, h⟩ := h S y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
    refine ⟨S', φ, ?_, h⟩
    rwa [((CompHaus.effectiveEpi_tfae _).out 0 2 :)]

end CondensedMod
