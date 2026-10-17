/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Internal hom for sheaves

The internal hom of presheaves of modules is a sheaf whenever its target is a sheaf.
We glue the underlying morphisms of abelian presheaves and check scalar linearity locally.
This defines `SheafOfModulesOfCommRing.internalHomFunctor` for sheaves of modules over a sheaf of
commutative rings. Using the presheaf closed monoidal structure and the sheafification
adjunction, we show that this internal hom is right adjoint to tensoring on the left.

The lemmas below compare currying, uncurrying, evaluation and coevaluation with their presheaf
counterparts through the tensor comparison map of the forgetful functor.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace PresheafOfModulesOfCommRing

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Cᵒᵖ ⥤ CommRingCat.{u}} (F G : PresheafOfModulesOfCommRing.{u} R)

/-- Forget the linearity of local morphisms of presheaves of modules. -/
@[implicit_reducible, simps]
def internalHomToPresheafHom :
    (F ⟶[_] G).presheaf ⋙ forget AddCommGrpCat ⟶
      presheafHom F.presheaf G.presheaf where
  app U := ↾fun φ ↦ (PresheafOfModules.toPresheaf _).map φ
  naturality := by intros; rfl

lemma internalHomToPresheafHom_app_injective (U : Cᵒᵖ) :
    Function.Injective ((internalHomToPresheafHom F G).app U) :=
  (PresheafOfModules.toPresheaf _).map_injective

variable {F G}

/-- A morphism of abelian presheaves over `X` is linear if it is linear on a covering sieve
and its target is a sheaf. In particular, gluing local module morphisms preserves linearity. -/
lemma presheafHom_app_smul_of_locally
    (hG : Presheaf.IsSheaf J G.presheaf) {X : C} {S : Sieve X} (hS : S ∈ J X)
    (φ : (Over.forget X).op ⋙ F.presheaf ⟶ (Over.forget X).op ⋙ G.presheaf)
    (hφ : ∀ (Y : C) (f : Y ⟶ X), S f → ∀ (r : R.obj (op Y)) (x : F.obj (op Y)),
      φ.app (op (Over.mk f)) (r • x) = r • (dsimp% φ.app (op (Over.mk f)) x))
    (W : (Over X)ᵒᵖ) (r : R.obj (op W.unop.left)) (x : F.obj (op W.unop.left)) :
    φ.app W (r • x) = r • (dsimp% φ.app W x) := by
  apply hG.isSeparated _ _ (J.pullback_stable W.unop.hom hS)
  intro Y p hp
  let f : Over.mk (p ≫ W.unop.hom) ⟶ W.unop := Over.homMk p
  have h (x : F.obj (op W.unop.left)) :
      φ.app (op (Over.mk (p ≫ W.unop.hom))) (F.map p.op x) = G.map p.op (φ.app W x) :=
    ConcreteCategory.congr_hom (φ.naturality f.op) x
  erw [← h, G.map_smul, ← h, F.map_smul, hφ Y (p ≫ W.unop.hom) hp]
  rfl

variable (F) in
/-- The internal hom into a sheaf of modules is a sheaf. -/
lemma isSheaf_ihom (hG : Presheaf.IsSheaf J G.presheaf) :
    Presheaf.IsSheaf J (F ⟶[_] G).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat)
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS x hx
  let ι := internalHomToPresheafHom F G
  obtain ⟨y, hy, hy_unique⟩ :=
    (hG.hom F.presheaf).isSheafFor S hS (x.map ι) (hx.map ι)
  have hy' := (PresheafHom.isAmalgamation_iff S _ (hx.map ι) y).1 hy
  let φ : F.over X ⟶ G.over X := PresheafOfModules.homMk y
    (presheafHom_app_smul_of_locally hG hS y (by
      intro Y f hf r m
      rw [hy' Y f hf]
      exact ((x f hf).app (op (Over.mk (𝟙 Y)))).hom.map_smul r m))
  refine ⟨φ, ?_, ?_⟩
  · intro Y f hf
    apply internalHomToPresheafHom_app_injective F G (op Y)
    exact (NatTrans.naturality_apply ι f.op φ).trans (hy f hf)
  · intro z hz
    apply internalHomToPresheafHom_app_injective F G (op X)
    exact hy_unique _ (hz.map ι)

end PresheafOfModulesOfCommRing

namespace SheafOfModulesOfCommRing

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

/-- The internal hom functor on sheaves of modules. -/
@[implicit_reducible, simps obj map_val]
def internalHomFunctor (F : SheafOfModulesOfCommRing.{u} R) :
    SheafOfModulesOfCommRing.{u} R ⥤ SheafOfModulesOfCommRing.{u} R where
  obj G := {
    val := F.val ⟶[_] G.val
    isSheaf := PresheafOfModulesOfCommRing.isSheaf_ihom F.val G.isSheaf }
  map f := { val := (ihom F.val).map f.val }

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [(W R).IsMonoidal]

/-- The tensor–internal hom adjunction on sheaves of modules. -/
def internalHomAdjunction (F : SheafOfModulesOfCommRing.{u} R) :
    MonoidalCategory.tensorLeft F ⊣ internalHomFunctor F :=
  let adj := PresheafOfModulesOfCommRing.sheafificationAdjunction.{u} R
  (Monoidal.Reflective.closed adj F).adj.ofNatIsoRight
    (Functor.isoWhiskerLeft (internalHomFunctor F) (asIso adj.counit) ≪≫
      (internalHomFunctor F).rightUnitor)

/-- Sheaves of modules form a closed monoidal category. -/
instance : MonoidalClosed (SheafOfModulesOfCommRing.{u} R) where
  closed F := { rightAdj := internalHomFunctor F, adj := internalHomAdjunction F }

@[simp]
lemma ihom_val (F G : SheafOfModulesOfCommRing.{u} R) :
    (F ⟶[_] G).val = F.val ⟶[_] G.val := rfl

@[simp]
lemma ihom_map_val (F : SheafOfModulesOfCommRing.{u} R)
    {G H : SheafOfModulesOfCommRing.{u} R} (f : G ⟶ H) :
    ((ihom F).map f).val = (ihom F.val).map f.val := rfl

open MonoidalCategory MonoidalClosed Functor.LaxMonoidal

set_option backward.isDefEq.respectTransparency false in
/-- Sheaf coevaluation is presheaf coevaluation followed by the tensor comparison map. -/
@[simp]
lemma ihom_coev_app_val (F M : SheafOfModulesOfCommRing.{u} R) :
    ((ihom.coev F).app M).val = (ihom.coev F.val).app M.val ≫
      (ihom F.val).map (μ (forget R) F M) := by
  let adj := PresheafOfModulesOfCommRing.sheafificationAdjunction.{u} R
  change (forget R).map ((Monoidal.Reflective.closed adj F).adj.unit.app M) ≫
    (forget R).map (adj.counit.app ((internalHomFunctor F).obj (F ⊗ M)) ≫ 𝟙 _) = _
  simp +instances only [Monoidal.Reflective.closed, Category.comp_id,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Functor.Monoidal.μIso_inv, Functor.comp_map, Category.assoc]
  erw [adj.right_triangle_components ((internalHomFunctor F).obj (F ⊗ M))]
  erw [Category.comp_id, ← Functor.map_comp]
  rw [Adjunction.IsMonoidal.leftAdjoint_μ (adj := adj)]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma monoidalClosed_curry_val {F M G : SheafOfModulesOfCommRing.{u} R}
    (f : F ⊗ M ⟶ G) :
    (curry f).val = curry (μ (forget R) F M ≫ f.val) := by
  rw [curry_eq, SheafOfModules.comp_val, ihom_map_val, ihom_coev_app_val]
  exact (curry_natural_right (μ (forget R) F M) f.val).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma μ_monoidalClosed_uncurry_val {F M G : SheafOfModulesOfCommRing.{u} R}
    (f : M ⟶ F ⟶[_] G) :
    μ (forget R) F M ≫ (uncurry f).val = uncurry f.val := by
  apply curry_injective
  rw [← monoidalClosed_curry_val, curry_uncurry, curry_uncurry]

set_option backward.isDefEq.respectTransparency false in
/-- Sheaf evaluation agrees with presheaf evaluation on the tensor comparison map. -/
@[reassoc (attr := simp)]
lemma μ_ihom_ev_app_val (F G : SheafOfModulesOfCommRing.{u} R) :
    μ (forget R) F (F ⟶[_] G) ≫ ((ihom.ev F).app G).val =
      (ihom.ev F.val).app G.val := by
  simpa only [uncurry_id_eq_ev] using
    (μ_monoidalClosed_uncurry_val (𝟙 (F ⟶[_] G))).trans
      (uncurry_id_eq_ev (C := PresheafOfModulesOfCommRing R.obj) F.val G.val)

end SheafOfModulesOfCommRing
