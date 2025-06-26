/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kenny Lau
-/

import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Formal Coproducts

In this file we construct the category of formal coproducts given a category.

## Main definitions

* `FormalCoproduct`: the category of formal coproducts, which are indexed sets of objects in a
  category. A morphism `∐ i : X.I, X.obj i ⟶ ∐ j : Y.I, Y.obj j` is given by a function
  `f : X.I → Y.I` and maps `X.obj i ⟶ Y.obj (f i)` for each `i : X.I`.
* `FormalCoproduct.eval : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct C)ᵒᵖ ⥤ A)`:
  the universal property that a presheaf on `C` where the target category has arbitrary coproducts,
  can be extended to a presheaf on `FormalCoproduct C`.

-/


universe w w₁ w₂ w₃ v v₁ v₂ v₃ u u₁ u₂ u₃

open Opposite

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] (A : Type u₁) [Category.{v₁} A]

variable (C) in
/-- A formal coproduct is an indexed set of objects. -/
structure FormalCoproduct where
  I : Type w
  obj (i : I) : C

namespace FormalCoproduct

structure Hom (X Y : FormalCoproduct.{w} C) where
  f : X.I → Y.I
  φ (i : X.I) : X.obj i ⟶ Y.obj (f i)

-- this category identifies to the fullsubcategory of the category of
-- presheaves of sets on `C` which are coproducts of representable presheaves
@[simps!] instance category : Category (FormalCoproduct.{w} C) where
  Hom := Hom
  id X := { f := id, φ := fun _ ↦ 𝟙 _ }
  comp α β := { f := β.f ∘ α.f, φ := fun _ ↦ α.φ _ ≫ β.φ _ }

@[ext (iff := false)]
lemma hom_ext {X Y : FormalCoproduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f)
    (h₂ : ∀ (i : X.I), f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i) : f = g := by
  obtain ⟨f, F⟩ := f
  obtain ⟨g, G⟩ := g
  obtain rfl : f = g := h₁
  obtain rfl : F = G := by ext i; simpa using h₂ i
  rfl

lemma hom_ext_iff {X Y : FormalCoproduct.{w} C} (f g : X ⟶ Y) :
    f = g ↔ ∃ h₁ : f.f = g.f, ∀ (i : X.I), f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i :=
  ⟨(· ▸ by simp), fun ⟨h₁, h₂⟩ ↦ hom_ext h₁ h₂⟩

@[simps!] def isoOfComponents {X Y : FormalCoproduct.{w} C} (e : X.I ≃ Y.I)
    (h : ∀ i, X.obj i ≅ Y.obj (e i)) : X ≅ Y where
  hom := { f := e, φ := fun i ↦ (h i).hom }
  inv := { f := e.symm, φ := fun i ↦ eqToHom (by simp) ≫ (h (e.symm i)).inv }
  hom_inv_id := by ext <;> aesop
  inv_hom_id := by ext <;> aesop

variable (C) in
@[simps!] def of : C ⥤ FormalCoproduct.{w} C where
  obj X := ⟨PUnit, fun _ ↦ X⟩
  map f := ⟨fun _ ↦ PUnit.unit, fun _ ↦ f⟩

-- This is probably some form of adjunction.
@[simps!] def ofHomEquiv (X : C) (Y : FormalCoproduct.{w} C) :
    ((of C).obj X ⟶ Y) ≃ (i : Y.I) × (X ⟶ Y.obj i) where
  toFun f := ⟨f.f PUnit.unit, f.φ PUnit.unit⟩
  invFun f := ⟨fun _ ↦ f.fst, fun _ ↦ f.snd⟩
  left_inv f := hom_ext rfl (by simp)
  right_inv f := Sigma.ext rfl (by simp)

instance : (of C).FullyFaithful where
  preimage f := f.φ PUnit.unit

@[simps!] def coproduct (𝒜 : Type w) (f : 𝒜 → FormalCoproduct.{w} C) :
    ColimitCocone (Discrete.functor f) where
  cocone := {
    pt := ⟨(i : 𝒜) × (f i).I, fun p ↦ (f p.1).obj p.2⟩
    ι := {
      app i := ⟨fun j ↦ ⟨i.as, j⟩, fun j ↦ 𝟙 ((f i.as).obj j)⟩,
      naturality := by rintro ⟨i⟩ ⟨j⟩ ⟨⟨f⟩⟩; cases f; rfl
    }
  }
  isColimit := {
    desc s := ⟨fun p ↦ (s.ι.app ⟨p.1⟩).f p.2, fun p ↦ (s.ι.app ⟨p.1⟩).φ p.2⟩
    uniq s m h := hom_ext (funext fun p ↦ congr_fun (congr_arg Hom.f (h ⟨p.1⟩)) p.2)
      fun p ↦ by obtain ⟨h₁, h₂⟩ := (hom_ext_iff _ _).1 (h ⟨p.1⟩); simpa using h₂ p.2
    fac s i := hom_ext (by ext; simp) (by simp)
  }

instance : HasCoproducts.{w} (FormalCoproduct.{w} C) := by
  refine fun 𝒜 ↦ ⟨fun f ↦ ⟨⟨?_⟩⟩⟩
  convert coproduct 𝒜 (f.obj ∘ Discrete.mk)
  exact Functor.ext (fun i ↦ rfl) (fun ⟨i⟩ ⟨j⟩ ⟨⟨f⟩⟩ ↦ by cases f; simp)

@[simps!] noncomputable def coproductIsoCoproduct {J : Type w} (f : J → FormalCoproduct.{w} C) :
    (∐ fun i : J ↦ f i) ≅ (coproduct J f).cocone.pt :=
  colimit.isoColimitCocone (coproduct _ _)

@[simps!] def coproductCoconeIsoSelf (X : FormalCoproduct.{w} C) :
    (coproduct X.I ((of C).obj ∘ X.obj)).cocone.pt ≅ X :=
  isoOfComponents (Equiv.sigmaPUnit X.I) fun i ↦ Iso.refl (X.obj i.fst)

@[simps!] noncomputable def coproductIsoSelf (X : FormalCoproduct.{w} C) :
    ∐ (of C).obj ∘ X.obj ≅ X :=
  coproductIsoCoproduct _ ≪≫ coproductCoconeIsoSelf X

@[simp] lemma comp_coproductIsoSelf (X : FormalCoproduct.{w} C) (i : X.I) :
    Sigma.ι _ i ≫ (coproductIsoSelf X).hom = (ofHomEquiv _ _).symm ⟨i, 𝟙 (X.obj i)⟩ :=
  (colimit.isoColimitCocone_ι_hom_assoc _ _ _).trans (by ext <;> simp [ofHomEquiv])

noncomputable
instance [HasTerminal C] (X : FormalCoproduct.{w} C) : Unique (X ⟶ (of C).obj (⊤_ C)) :=
  ⟨⟨⟨fun _ ↦ PUnit.unit, fun _ ↦ terminal.from _⟩⟩,
  fun j ↦ hom_ext (funext fun _ ↦ rfl) (by aesop)⟩

instance [HasTerminal C] : HasTerminal (FormalCoproduct.{w} C) :=
  (IsTerminal.ofUnique <| (of C).obj (⊤_ C)).hasTerminal

noncomputable
def pullback [HasPullbacks C] (X Y Z : FormalCoproduct.{w} C) (f : X ⟶ Z) (g : Y ⟶ Z) :
    FormalCoproduct.{w} C :=
  ⟨Function.Pullback f.f g.f, fun xy ↦
    Limits.pullback (f.φ xy.1.1 ≫ eqToHom (by rw [xy.2])) (g.φ xy.1.2)⟩

@[simps!] noncomputable
def pullbackCone [HasPullbacks C] (X Y Z : FormalCoproduct.{w} C)
    (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  .mk (W := pullback X Y Z f g)
    ⟨fun i ↦ i.1.1, fun i ↦ pullback.fst _ _⟩
    ⟨fun i ↦ i.1.2, fun i ↦ pullback.snd _ _⟩
    (hom_ext (funext fun i ↦ i.2) (by simp [pullback.condition]))

noncomputable def isLimitPullback [HasPullbacks C] (X Y Z : FormalCoproduct.{w} C)
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit (pullbackCone X Y Z f g) := by
  refine PullbackCone.IsLimit.mk _
    (fun s ↦ ⟨fun i ↦ ⟨(s.fst.f i, s.snd.f i), congrFun (congrArg Hom.f s.condition) i⟩,
      fun i ↦ pullback.lift (s.fst.φ i) (s.snd.φ i) ?_⟩)
    (fun s ↦ by ext <;> simp)
    (fun s ↦ by ext <;> simp)
    (fun s m h₁ h₂ ↦ ?_)
  · obtain ⟨h₁, h₂⟩ := (hom_ext_iff _ _).1 s.condition
    simpa using h₂ i
  · obtain ⟨h₁₁, h₁₂⟩ := (hom_ext_iff _ _).1 h₁
    obtain ⟨h₂₁, h₂₂⟩ := (hom_ext_iff _ _).1 h₂
    obtain ⟨hs₁, hs₂⟩ := (hom_ext_iff _ _).1 s.condition
    obtain ⟨f, φ⟩ := m
    have hf (i) : f i = ⟨(s.fst.f i, s.snd.f i), congrFun hs₁ i⟩ :=
      Subtype.ext (Prod.ext (congrFun h₁₁ i) (congrFun h₂₁ i))
    refine hom_ext (funext hf) (fun i ↦ ?_)
    replace hf := hf i
    refine pullback.hom_ext ?_ ?_
    · simp only [category_comp_f, category_comp_φ, Category.assoc, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app] at h₁₂ ⊢
      convert h₁₂ i using 2
      refine eq_of_heq ((eqToHom_comp_heq_iff _ _ _).2 ((heq_comp_eqToHom_iff _ _ _).2 ?_))
      congr 1
      · rw [hf]
      · rw [hf]
      · rw [hf]
      · exact (comp_eqToHom_heq_iff _ _ _).2 ((heq_comp_eqToHom_iff _ _ _).2 (by rw [hf]))
      · rw [hf]
      · generalize_proofs; simp [*]
    · simp only [category_comp_f, category_comp_φ, Category.assoc, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app] at h₂₂ ⊢
      convert h₂₂ i using 2
      refine eq_of_heq ((eqToHom_comp_heq_iff _ _ _).2 ((heq_comp_eqToHom_iff _ _ _).2 ?_))
      congr 1
      · rw [hf]
      · rw [hf]
      · rw [hf]
      · exact (comp_eqToHom_heq_iff _ _ _).2 ((heq_comp_eqToHom_iff _ _ _).2 (by rw [hf]))
      · rw [hf]
      · generalize_proofs; simp [*]


section HasCoproducts

variable [HasCoproducts.{w} A]

variable (C) in
@[simps] noncomputable def eval : (C ⥤ A) ⥤ (FormalCoproduct.{w} C ⥤ A) where
  obj F :=
    { obj X := ∐ fun (i : X.I) ↦ F.obj (X.obj i)
      map {X Y} f := Sigma.desc fun i ↦ F.map (f.φ i) ≫ Sigma.ι (F.obj ∘ Y.obj) (f.f i)
      map_comp _ _ := Sigma.hom_ext _ _ (fun _ ↦ by simp [Sigma.ι_desc]) }
  map α := { app f := Sigma.map fun i ↦ α.app (f.obj i) }

noncomputable def evalOf : eval C A ⋙ (whiskeringLeft _ _ A).obj (of C) ≅ Functor.id (C ⥤ A) :=
  NatIso.ofComponents fun F ↦ NatIso.ofComponents
    (fun x ↦ ⟨Sigma.desc fun _ ↦ 𝟙 _, Sigma.ι (fun _ ↦ F.obj x) PUnit.unit, by aesop, by simp⟩)
    (fun f ↦ Sigma.hom_ext _ _ (by simp [Sigma.ι_desc]))

variable {A} in
@[simps!] noncomputable
def evalCoproductIso (F : C ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    ((eval C A).obj F).obj (coproduct J f).cocone.pt ≅ ∐ fun j ↦ ((eval C A).obj F).obj (f j) :=
  (sigmaSigmaIso (fun j ↦ (f j).I) (fun j x ↦ F.obj ((f j).obj x))).symm

lemma comp_evalCoproductIso (F : C ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C)
    (j : J) (x : (f j).I) :
    ((eval C A).obj F).map ((ofHomEquiv ((f j).obj x) _).2 ⟨Sigma.mk j x, 𝟙 _⟩) ≫
        (evalCoproductIso F f).hom =
      Sigma.desc fun _ ↦ Sigma.ι (fun i ↦ F.obj ((f j).obj i)) x ≫
        Sigma.ι (fun b ↦ ∐ fun i ↦ F.obj ((f b).obj i)) j :=
  Sigma.hom_ext _ _ fun _ ↦ by simp [ofHomEquiv, Sigma.ι_desc]

lemma sigmaComparison_eq (F : C ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    sigmaComparison ((eval C A).obj F) f =
      (evalCoproductIso F f).inv ≫ ((eval C A).obj F).map (coproductIsoCoproduct f).inv := by
  refine Sigma.hom_ext _ _ fun j ↦ Sigma.hom_ext _ _ fun x ↦ ?_
  rw [ι_comp_sigmaComparison, ← Functor.mapIso_inv, ← Category.assoc, ← Category.assoc,
    Iso.eq_comp_inv, evalCoproductIso, Iso.symm_inv, sigmaSigmaIso_hom, Category.assoc,
    Category.assoc, Sigma.ι_desc, Sigma.ι_desc, Functor.mapIso_hom, ← Functor.map_comp,
    coproductIsoCoproduct_hom, colimit.ι_desc]
  simp [coproduct]
  rfl

variable {A} in
theorem preservesCoproductEval (F : C ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    PreservesColimit (Discrete.functor f) ((eval.{w} C A).obj F) := by
  refine CategoryTheory.Limits.PreservesCoproduct.of_iso_comparison _ _ (i := ?_)
  rw [sigmaComparison_eq, ← Functor.mapIso_inv, ← Iso.trans_inv, ← Iso.symm_hom]
  infer_instance

end HasCoproducts


section HasProducts

variable [HasProducts.{w} A]

variable (C) in
@[simps] noncomputable
def evalOp : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct.{w} C)ᵒᵖ ⥤ A) where
  obj F :=
    { obj X := ∏ᶜ fun (i : X.unop.I) ↦ F.obj (op (X.unop.obj i))
      map f := Pi.lift fun i ↦ Pi.π _ (f.unop.f i) ≫ F.map (f.unop.φ i).op }
  map α := { app f := Pi.map fun i ↦ α.app (op (f.unop.obj i)) }

variable {A} in
noncomputable def evalOpOf :
    evalOp C A ⋙ (whiskeringLeft _ _ A).obj (of C).op ≅ Functor.id (Cᵒᵖ ⥤ A) :=
  NatIso.ofComponents fun F ↦ NatIso.ofComponents fun x ↦
    ⟨Pi.π _ PUnit.unit, Pi.lift fun _ ↦ 𝟙 _, by aesop, by simp⟩

variable {A} in
@[simps!] noncomputable
def evalOpCoproductIso (F : Cᵒᵖ ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    ((evalOp C A).obj F).obj (op (coproduct J f).cocone.pt) ≅
      ∏ᶜ fun j ↦ ((evalOp C A).obj F).obj (op (f j)) :=
  (piPiIso (fun j ↦ (f j).I) (fun j x ↦ F.obj (op ((f j).obj x)))).symm

lemma evalOpCoproductIso_comp (F : Cᵒᵖ ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) (j : J) :
    (evalOpCoproductIso F f).hom ≫ Pi.π _ j =
      ((evalOp C A).obj F).map (op ((coproduct J f).cocone.ι.app ⟨j⟩)) :=
  (Pi.lift_π _ _).trans (by simp [coproduct])

lemma π_eq {J : Type w} (f : J → FormalCoproduct.{w} C) (j : J) :
    Pi.π (op ∘ f) j = (opCoproductIsoProduct _).inv ≫ op (colimit.ι _ _) :=
  (opCoproductIsoProduct_inv_comp_ι _ _).symm

lemma piComparison_eq (F : Cᵒᵖ ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    piComparison ((evalOp C A).obj F) (op ∘ f) =
      ((evalOp C A).obj F).map ((opCoproductIsoProduct _).inv ≫ (coproductIsoCoproduct _).op.inv) ≫
        (evalOpCoproductIso F f).hom := by
  refine Pi.hom_ext _ _ fun j ↦ Pi.hom_ext _ _ fun x ↦ ?_
  rw [piComparison_comp_π, evalOp_obj_map, Pi.lift_π, evalOp_obj_map, evalOpCoproductIso_hom,
    Category.assoc, Category.assoc]
  conv => enter [2,2]; rw [← Category.assoc]; enter [1]; exact Pi.lift_π _ _
  conv => enter [2,2]; exact Pi.lift_π _ _
  refine Eq.symm ((Pi.lift_π _ _).trans ?_)
  congr 1
  · congr 3; simp [π_eq]
  · congr 1; simp [π_eq]
  · congr 1
    · rw [π_eq]; rfl
    · rw [π_eq]; rfl

variable {A} in
theorem preservesProductEvalOp (F : Cᵒᵖ ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    PreservesLimit (Discrete.functor (op ∘ f)) ((evalOp.{w} C A).obj F) := by
  refine CategoryTheory.Limits.PreservesProduct.of_iso_comparison _ _ (i := ?_)
  rw [piComparison_eq, ← Iso.trans_inv, ← Functor.mapIso_inv, ← Iso.symm_hom]
  infer_instance

end HasProducts


def arrowOfMaps (X : C) {J : Type w} (f : (j : J) → C) (φ : (j : J) → f j ⟶ X) :
    FormalCoproduct.mk _ f ⟶ (of C).obj X :=
  ⟨fun _ ↦ PUnit.unit, φ⟩


end FormalCoproduct

end Limits

end CategoryTheory
