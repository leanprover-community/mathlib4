/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kenny Lau
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

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

## TODO

* `FormalCoproduct.incl C : C ⥤ FormalCoproduct.{w} C` probably preserves every limit?

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe w w₁ w₂ w₃ v v₁ v₂ v₃ u u₁ u₂ u₃

open Opposite CategoryTheory Functor

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] (A : Type u₁) [Category.{v₁} A]

variable (C) in
/-- A formal coproduct is an indexed set of objects, where ⟨I, f⟩ corresponds to the "formal
coproduct" `⨿ (i : I), f i`, where `f i : C` is the `i`ᵗʰ component. -/
structure FormalCoproduct where
  /-- The indexing type. -/
  I : Type w
  /-- The object in the original category indexed by `x : I`. -/
  obj (i : I) : C

namespace FormalCoproduct

/-- A morphism `(⨿ (i : X.I), X.obj i) ⟶ (⨿ (j : Y.I), Y.obj i)` is given by first a function
on the indexing sets `f : X.I → Y.I`, and then for each `i : X.I` a morphism
`X.obj i ⟶ Y.obj (f i)`. -/
structure Hom (X Y : FormalCoproduct.{w} C) where
  /-- The function on the indexing sets. -/
  f : X.I → Y.I
  /-- The map on each component. -/
  φ (i : X.I) : X.obj i ⟶ Y.obj (f i)

-- this category identifies to the full subcategory of the category of
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

lemma hom_ext_iff' {X Y : FormalCoproduct.{w} C} (f g : X ⟶ Y) :
    f = g ↔ ∀ i : X.I, ∃ h₁ : f.f i = g.f i, f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i :=
  ⟨(· ▸ by simp), fun h ↦ hom_ext (funext fun i ↦ (h i).fst) fun i ↦ (h i).snd⟩

/-- A way to create isomorphisms in the category of formal coproducts, by creating an `Equiv`
between the indexing sets, and then correspondingly isomorphisms of each component. -/
@[simps!] def isoOfComponents {X Y : FormalCoproduct.{w} C} (e : X.I ≃ Y.I)
    (h : ∀ i, X.obj i ≅ Y.obj (e i)) : X ≅ Y where
  hom := { f := e, φ := fun i ↦ (h i).hom }
  inv := { f := e.symm, φ := fun i ↦ eqToHom (by simp) ≫ (h (e.symm i)).inv }
  hom_inv_id := by ext <;> aesop
  inv_hom_id := by ext <;> aesop

variable (C) in
/-- An object of the original category produces a formal coproduct on that object only, so indexed
by `PUnit`, the type with one element. -/
@[simps!] def incl : C ⥤ FormalCoproduct.{w} C where
  obj X := ⟨PUnit, fun _ ↦ X⟩
  map f := ⟨fun _ ↦ PUnit.unit, fun _ ↦ f⟩

section fromIncl

variable {X : C} {Y : FormalCoproduct.{w} C}

/-- A map `incl(X) ⟶ Y` is specified by an element of `Y`'s indexing set, and then a morphism
`X ⟶ Y.obj i` in the original category. -/
@[simps!] def Hom.fromIncl (i : Y.I) (f : X ⟶ Y.obj i) : (incl C).obj X ⟶ Y :=
  ⟨fun _ ↦ i, fun _ ↦ f⟩

/-- A map `incl(X) ⟶ Y` is specified by an element of `Y`'s indexing set, and then a morphism
`X ⟶ Y.obj i` in the original category. -/
def Hom.asSigma (f : (incl C).obj X ⟶ Y) : Σ (i : Y.I), X ⟶ Y.obj i :=
  ⟨f.f PUnit.unit, f.φ PUnit.unit⟩

set_option backward.isDefEq.respectTransparency false in
lemma Hom.fromIncl_asSigma (f : (incl C).obj X ⟶ Y) :
    Hom.fromIncl f.asSigma.fst f.asSigma.snd = f := by
  ext <;> aesop

end fromIncl

-- This is probably some form of adjunction?
/-- A map `incl(X) ⟶ Y` is specified by an element of `Y`'s indexing set, and then a morphism
`X ⟶ Y.obj i` in the original category. -/
@[simps!] def inclHomEquiv (X : C) (Y : FormalCoproduct.{w} C) :
    ((incl C).obj X ⟶ Y) ≃ (i : Y.I) × (X ⟶ Y.obj i) where
  toFun f := f.asSigma
  invFun f := .fromIncl f.1 f.2
  left_inv f := f.fromIncl_asSigma
  right_inv _ := rfl

/-- `incl` is fully faithful, which means that `(X ⟶ Y) ≃ (incl(X) ⟶ incl(Y))`. -/
@[simps!] def fullyFaithfulIncl : (incl C).FullyFaithful where
  preimage f := f.φ PUnit.unit

instance : (incl C).Full :=
  fullyFaithfulIncl.full

instance : (incl C).Faithful :=
  fullyFaithfulIncl.faithful

/-- A family of maps with the same target can be turned into one arrow in the category of formal
coproducts. This is used in Čech cohomology. -/
@[simps!] def homOfPiHom (X : C) {J : Type w} (f : (j : J) → C) (φ : (j : J) → f j ⟶ X) :
    FormalCoproduct.mk _ f ⟶ (incl C).obj X :=
  ⟨fun _ ↦ PUnit.unit, φ⟩

section Coproduct

variable (𝒜 : Type w) (f : 𝒜 → FormalCoproduct.{w} C) (t X : FormalCoproduct.{w} C)

/-- We construct explicitly the data that specify the coproduct of a given family of formal
coproducts. -/
def cofan : Cofan f :=
  Cofan.mk ⟨(i : 𝒜) × (f i).I, fun p ↦ (f p.1).obj p.2⟩
    fun i ↦ ⟨fun x ↦ ⟨i, x⟩, fun x ↦ 𝟙 ((f i).obj x)⟩

section simp_lemmas

variable {𝒜 f}

theorem cofan_inj (i : 𝒜) : (cofan 𝒜 f).inj i = ⟨fun x ↦ ⟨i, x⟩, fun x ↦ 𝟙 ((f i).obj x)⟩ := rfl

@[simp] lemma cofan_inj_f_fst (i : 𝒜) (x) : (((cofan 𝒜 f).inj i).f x).1 = i := rfl

@[simp] lemma cofan_inj_f_snd (i : 𝒜) (x) : (((cofan 𝒜 f).inj i).f x).2 = x := rfl

@[simp] lemma cofan_inj_φ (i : 𝒜) (x) : ((cofan 𝒜 f).inj i).φ x = 𝟙 ((f i).obj x) := rfl

end simp_lemmas

set_option backward.isDefEq.respectTransparency false in
/-- The explicit `Equiv` between maps from the constructed coproduct `cofan 𝒜 f` and families of
maps from each component, which is the universal property of coproducts. -/
@[simps!] def cofanHomEquiv :
    ((cofan 𝒜 f).pt ⟶ t) ≃ ((i : 𝒜) → (f i ⟶ t)) where
  toFun m i := (cofan 𝒜 f).inj i ≫ m
  invFun s := ⟨fun p ↦ (s p.1).f p.2, fun p ↦ (s p.1).φ p.2⟩
  left_inv m := hom_ext rfl (fun ⟨i, x⟩ ↦ by simp [cofan_inj])
  right_inv p := by ext <;> simp

/-- `cofan 𝒜 f` is a coproduct of `f`. -/
@[simps!] def isColimitCofan : IsColimit (cofan 𝒜 f) :=
  mkCofanColimit (cofan 𝒜 f) (fun t ↦ (cofanHomEquiv _ _ _).symm t.inj)
    (fun t i ↦ congrFun ((cofanHomEquiv _ _ _).right_inv t.inj) i)
    (fun _ _ h ↦ (Equiv.eq_symm_apply _).2 (funext h))

instance : HasCoproducts.{w} (FormalCoproduct.{w} C) :=
  hasCoproducts_of_colimit_cofans _ (isColimitCofan _)

/-- The arbitrary choice of the coproduct is isomorphic to our constructed coproduct `cofan 𝒜 f`.
-/
noncomputable def coproductIsoCofanPt : ∐ f ≅ (cofan 𝒜 f).pt :=
  colimit.isoColimitCocone ⟨_, isColimitCofan _ _⟩

variable {𝒜 f} in
@[reassoc (attr := simp)] lemma ι_comp_coproductIsoCofanPt (i) :
    Sigma.ι f i ≫ (coproductIsoCofanPt 𝒜 f).hom = (cofan 𝒜 f).inj i :=
  colimit.isoColimitCocone_ι_hom _ _

/-- Each `X : FormalCoproduct.{w} C` is actually itself a coproduct of objects of the original
category (after coercion using `incl C`). This is the function that specifies the family for which
`X` is a coproduct of. -/
def toFun (X : FormalCoproduct.{w} C) : X.I → FormalCoproduct.{w} C :=
  (incl C).obj ∘ X.obj

/-- The witness that each `X : FormalCoproduct.{w} C` is itself a coproduct of objects of the
original category (after coercion using `incl C`), specified by `X.toFun`. -/
def cofanPtIsoSelf : (cofan X.I X.toFun).pt ≅ X :=
  isoOfComponents (Equiv.sigmaPUnit X.I) fun i ↦ Iso.refl (X.obj i.fst)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inj_comp_cofanPtIsoSelf_hom (i : X.I) :
    (cofan X.I X.toFun).inj i ≫ (cofanPtIsoSelf X).hom = .fromIncl i (𝟙 (X.obj i)) :=
  hom_ext rfl (fun i => by aesop)

@[reassoc (attr := simp)]
lemma fromIncl_comp_cofanPtIsoSelf_inv (i : X.I) :
    Hom.fromIncl i (𝟙 (X.obj i)) ≫ (cofanPtIsoSelf X).inv = (cofan X.I X.toFun).inj i :=
  (Iso.comp_inv_eq _).2 (inj_comp_cofanPtIsoSelf_hom _ _).symm

/-- The isomorphism between the coproduct of `X.toFun` and the object `X` itself. -/
@[simps!] noncomputable def coproductIsoSelf :
    ∐ X.toFun ≅ X :=
  coproductIsoCofanPt _ _ ≪≫ cofanPtIsoSelf X

@[reassoc (attr := simp)] lemma ι_comp_coproductIsoSelf_hom (i : X.I) :
    Sigma.ι _ i ≫ (coproductIsoSelf X).hom = .fromIncl i (𝟙 (X.obj i)) := by
  simp [coproductIsoSelf]

@[reassoc (attr := simp)] lemma fromIncl_comp_coproductIsoSelf_inv (i : X.I) :
    Hom.fromIncl i (𝟙 (X.obj i)) ≫ (coproductIsoSelf X).inv = Sigma.ι X.toFun i :=
  (Iso.comp_inv_eq _).2 (ι_comp_coproductIsoSelf_hom _ _).symm

end Coproduct

section Terminal

/-- Given a terminal object `T` in the original category, we show that `incl(T)` is a terminal
object in the category of formal coproducts. -/
def isTerminalIncl (T : C) (ht : IsTerminal T) : IsTerminal ((incl C).obj T) :=
  IsTerminal.ofUniqueHom (fun _ ↦ ⟨fun _ ↦ PUnit.unit, fun _ ↦ ht.from _⟩)
    (fun _ _ ↦ hom_ext (funext fun _ ↦ rfl) (fun _ ↦ ht.hom_ext _ _))

instance [HasTerminal C] : HasTerminal (FormalCoproduct.{w} C) :=
  (isTerminalIncl (⊤_ C) terminalIsTerminal).hasTerminal

end Terminal

section Pullback

variable {X Y Z : FormalCoproduct.{w} C} (f : X ⟶ Z) (g : Y ⟶ Z)
  (pb : ∀ i : Function.Pullback f.f g.f,
    PullbackCone (f.φ i.1.1 ≫ eqToHom (by rw [i.2])) (g.φ i.1.2))
  (hpb : ∀ i, IsLimit (pb i))
  (T : FormalCoproduct.{w} C)

/-- Given two morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`, given pullback in `C` over each component,
construct the pullback in `FormalCategory.{w} C`. -/
def pullbackCone : PullbackCone f g :=
  .mk (W := ⟨Function.Pullback f.f g.f, fun i ↦ (pb i).pt⟩)
    ⟨fun i ↦ i.1.fst, fun i ↦ (pb i).fst⟩
    ⟨fun i ↦ i.1.snd, fun i ↦ (pb i).snd⟩
    (hom_ext (funext fun i ↦ i.2) (fun i ↦ by simp [(pb i).condition]))

section simp_lemmas

@[simp] lemma pullbackCone_fst_f (i) : (pullbackCone f g pb).fst.f i = i.1.1 := rfl

@[simp] lemma pullbackCone_fst_φ (i) : (pullbackCone f g pb).fst.φ i = (pb i).fst := rfl

@[simp] lemma pullbackCone_snd_f (i) : (pullbackCone f g pb).snd.f i = i.1.2 := rfl

@[simp] lemma pullbackCone_snd_φ (i) : (pullbackCone f g pb).snd.φ i = (pb i).snd := rfl

@[simp] lemma pullbackCone_condition :
    (pullbackCone f g pb).fst ≫ f = (pullbackCone f g pb).snd ≫ g :=
  PullbackCone.condition _

end simp_lemmas

set_option backward.isDefEq.respectTransparency false in
/-- The `Equiv` that witnesses that `pullbackCone f g pb` is actually a pullback. This is the
universal property of pullbacks. -/
@[simps!] def homPullbackEquiv : (T ⟶ (pullbackCone f g pb).pt) ≃
    { p : (T ⟶ X) × (T ⟶ Y) // p.1 ≫ f = p.2 ≫ g } where
  toFun m := ⟨⟨m ≫ (pullbackCone f g pb).fst, m ≫ (pullbackCone f g pb).snd⟩, by simp⟩
  invFun s := ⟨fun i ↦ ⟨(s.1.1.f i, s.1.2.f i), congrFun (congrArg Hom.f s.2) i⟩,
    fun i ↦ (hpb _).lift (PullbackCone.mk (s.1.1.φ i) (s.1.2.φ i)
      (by simpa using ((hom_ext_iff _ _).1 s.2).2 i))⟩
  left_inv m := hom_ext rfl (fun i ↦ by
    simp only [category_comp_f, category_comp_φ, eqToHom_refl, Category.comp_id]
    exact (hpb _).hom_ext ((pb _).equalizer_ext (by aesop) (by aesop)))
  right_inv s := by ext <;> simp

/-- `pullbackCone f g pb` is a pullback. -/
def isLimitPullbackCone : IsLimit (pullbackCone f g pb) := by
  refine PullbackCone.IsLimit.mk
    (fst := (pullbackCone f g pb).fst) (snd := (pullbackCone f g pb).snd) _
    (fun s ↦ (homPullbackEquiv f g pb hpb s.pt).2 ⟨(s.fst, s.snd), s.condition⟩)
    (fun s ↦ congrArg (·.1.fst)
      ((homPullbackEquiv f g pb hpb s.pt).right_inv ⟨(s.fst, s.snd), s.condition⟩))
    (fun s ↦ congrArg (·.1.snd)
      ((homPullbackEquiv f g pb hpb s.pt).right_inv ⟨(s.fst, s.snd), s.condition⟩))
    (fun s m h₁ h₂ ↦ ?_)
  convert ((homPullbackEquiv f g pb hpb s.pt).left_inv m).symm using 3
  rw [← h₁, ← h₂]; rfl

-- Arguments cannot be inferred.
include pb hpb in
theorem hasPullback_of_pullbackCone : HasPullback f g :=
  ⟨⟨⟨_, isLimitPullbackCone f g pb hpb⟩⟩⟩

include hpb in
lemma isPullback : IsPullback (pullbackCone f g pb).fst (pullbackCone f g pb).snd f g :=
  ⟨⟨pullbackCone_condition f g pb⟩, ⟨isLimitPullbackCone f g pb hpb⟩⟩

omit pb
variable [HasPullbacks C]

instance : HasPullback f g :=
  hasPullback_of_pullbackCone f g (fun _ ↦ pullback.cone _ _) (fun _ ↦ pullback.isLimit _ _)

instance : HasPullbacks (FormalCoproduct.{w} C) :=
  hasPullbacks_of_hasLimit_cospan _

end Pullback

noncomputable section HasCoproducts

variable [HasCoproducts.{w} A] (C) (J : Type w) (f : J → FormalCoproduct.{w} C) (F : C ⥤ A)

set_option backward.isDefEq.respectTransparency false in
/-- A copresheaf valued in a category `A` with arbitrary coproducts, can be extended to the category
of formal coproducts. -/
@[simps!] def eval : (C ⥤ A) ⥤ (FormalCoproduct.{w} C ⥤ A) where
  obj F :=
    { obj X := ∐ fun (i : X.I) ↦ F.obj (X.obj i)
      map {X Y} f := Sigma.desc fun i ↦ F.map (f.φ i) ≫ Sigma.ι (F.obj ∘ Y.obj) (f.f i)
      map_comp _ _ := Sigma.hom_ext _ _ (fun _ ↦ by simp [Sigma.ι_desc]) }
  map α := { app f := Sigma.map fun i ↦ α.app (f.obj i) }

set_option backward.isDefEq.respectTransparency false in
/-- `eval(F)` restricted to the original category (via `incl`) is the original copresheaf `F`. -/
@[simps!] def evalCompInclIsoId :
    eval C A ⋙ (whiskeringLeft _ _ A).obj (incl C) ≅ Functor.id (C ⥤ A) :=
  NatIso.ofComponents fun F ↦ NatIso.ofComponents
    (fun x ↦ ⟨Sigma.desc fun _ ↦ 𝟙 _, Sigma.ι (fun _ ↦ F.obj x) PUnit.unit, by aesop, by simp⟩)
    (fun f ↦ Sigma.hom_ext _ _ (by simp [Sigma.ι_desc]))

variable {C A}

set_option backward.isDefEq.respectTransparency false in
/-- `eval(F)` preserves arbitrary coproducts. -/
def isColimitEvalMapCoconeCofan : IsColimit (((eval.{w} C A).obj F).mapCocone (cofan.{w} J f)) where
  desc s := Sigma.desc fun i ↦ Sigma.ι (F.obj ∘ (f i.1).obj) i.2 ≫ s.ι.app ⟨i.1⟩
  fac s i := Sigma.hom_ext _ _ fun i ↦ by simp [cofan, Function.comp_def]
  uniq s m h := Sigma.hom_ext _ _ fun ⟨i₁, i₂⟩ ↦ by simp [← h, cofan, Function.comp_def]

instance : PreservesColimit (Discrete.functor f) ((eval.{w} C A).obj F) :=
  ⟨fun hc ↦ ⟨IsColimit.ofIsoColimit (isColimitEvalMapCoconeCofan J f F)
    ((Cocone.functoriality _ _).mapIso ((isColimitCofan J f).uniqueUpToIso hc))⟩⟩

instance : PreservesColimitsOfShape (Discrete J) ((eval.{w} C A).obj F) :=
  preservesColimitsOfShape_of_discrete _

end HasCoproducts

noncomputable section HasProducts

variable [HasProducts.{w} A] (C) (J : Type w) (f : J → FormalCoproduct.{w} C) (F : Cᵒᵖ ⥤ A)

set_option backward.isDefEq.respectTransparency false in
/-- A presheaf valued in a category `A` with arbitrary products can be extended to the category of
formal coproducts. -/
@[simps!] def evalOp : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct.{w} C)ᵒᵖ ⥤ A) where
  obj F :=
    { obj X := ∏ᶜ fun (i : X.unop.I) ↦ F.obj (op (X.unop.obj i))
      map f := Pi.lift fun i ↦ Pi.π _ (f.unop.f i) ≫ F.map (f.unop.φ i).op }
  map α := { app f := Pi.map fun i ↦ α.app (op (f.unop.obj i)) }

set_option backward.isDefEq.respectTransparency false in
/-- `evalOp(F)` restricted to the original category (via `incl`) is the original presheaf `F`. -/
@[simps!] def evalOpCompInlIsoId :
    evalOp C A ⋙ (whiskeringLeft _ _ A).obj (incl C).op ≅ Functor.id (Cᵒᵖ ⥤ A) :=
  NatIso.ofComponents fun F ↦ NatIso.ofComponents fun x ↦
    ⟨Pi.π _ PUnit.unit, Pi.lift fun _ ↦ 𝟙 _, by aesop, by simp⟩

variable {C A}

set_option backward.isDefEq.respectTransparency false in
/-- `evalOp(F)` preserves arbitrary products. -/
def isLimitEvalMapConeCofanOp : IsLimit (((evalOp.{w} C A).obj F).mapCone (cofan.{w} J f).op) where
  lift s := Pi.lift fun i ↦ s.π.app ⟨i.1⟩ ≫ Pi.π _ i.2
  fac s i := Pi.hom_ext _ _ fun i ↦ by simp [cofan]
  uniq s m h := Pi.hom_ext _ _ fun ⟨i₁, i₂⟩ ↦ by simp [← h, cofan]

instance : PreservesLimit (Discrete.functor (op ∘ f)) ((evalOp.{w} C A).obj F) :=
  ⟨fun hc ↦ ⟨IsLimit.ofIsoLimit (isLimitEvalMapConeCofanOp J f F) ((Cone.functoriality _ _).mapIso
    ((Cofan.IsColimit.op (isColimitCofan J f)).uniqueUpToIso hc))⟩⟩

end HasProducts

end FormalCoproduct

end Limits

end CategoryTheory
