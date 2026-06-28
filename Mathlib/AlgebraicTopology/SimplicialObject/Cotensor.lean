/-
Copyright (c) 2026 Robin Carlier, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Christian Merten
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Bracket and hypercovers

In this file we define a bracket operation `X[K]` for a semi-simplicial object `X`
and a nonsingular simplicial set `K`. Using this we define the notion of
a hypercover.

This is a rough draft
-/

open CategoryTheory Limits SimplicialObject
  Simplicial

universe w v u

variable {C : Type*} [Category* C] (X : SimplicialObject C) (K : SSet.{w})

namespace CategoryTheory

lemma uliftYonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Cᵒᵖ ⥤ Type (max w _))
    (x : F.obj ⟨X⟩) :
    uliftYoneda.{w}.map f ≫ uliftYonedaEquiv.{w}.symm x =
      uliftYonedaEquiv.{w}.symm ((F.map f.op) x) := by
  apply uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv]

lemma IsConnected.of_forall_nonempty_hom {C : Type*} [Category* C] (X : C)
    (h : ∀ (U : C), Nonempty (U ⟶ X)) :
    IsConnected C := by
  have : Nonempty C := ⟨X⟩
  exact zigzag_isConnected fun A B ↦ (Zigzag.of_hom (h _).some).trans (.of_inv (h _).some)

lemma IsConnected.of_forall_zigzag {C : Type*} [Category* C] (X : C)
    (h : ∀ (U : C), Zigzag U X) :
    IsConnected C := by
  have : Nonempty C := ⟨X⟩
  exact zigzag_isConnected fun A B ↦ (h _).trans (h _).symm

end CategoryTheory

namespace SemiSimplexCategory

-- TODO: show it is also final
set_option backward.isDefEq.respectTransparency false in
instance : toSimplexCategory.Initial := by
  constructor
  rintro ⟨n⟩
  let U : CostructuredArrow toSimplexCategory ⦋n⦌ := CostructuredArrow.mk (Y := ⦋n⦌ₛ) (𝟙 _)
  refine IsConnected.of_forall_zigzag U fun ⟨⟨na⟩, _, homa⟩ ↦ ?_
  obtain ⟨⟨⟨⟨ma⟩, τa, πa, rfl⟩, h⟩⟩ := HasStrongEpiMonoFactorisations.has_fac homa
  dsimp at τa πa
  have : Epi πa := ‹StrongEpi πa›.epi
  have : IsSplitEpi πa := isSplitEpi_of_epi πa
  let s := section_ πa
  let m : CostructuredArrow toSimplexCategory ⦋n⦌ := .mk τa
  refine .trans (j₂ := m) ?_ ?_
  · exact .of_inv <| CostructuredArrow.homMk (homOfMono s) <| IsSplitEpi.id_assoc πa τa
  · exact .of_hom <| CostructuredArrow.homMk (homOfMono τa) (by simp [U, m])

set_option backward.isDefEq.respectTransparency false in
@[simps]
def lift {C : Type*} [Category* C] (F : C ⥤ SimplexCategory)
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Mono (F.map f) := by infer_instance) :
    C ⥤ SemiSimplexCategory where
  obj X := .mk (F.obj X).len
  map f :=
    haveI : Mono (F.map f) := h f
    homOfMono (F.map f)

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def liftComp {C : Type*} [Category* C] (F : C ⥤ SimplexCategory)
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Mono (F.map f) := by infer_instance) :
    lift F h ⋙ toSimplexCategory ≅ F :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
lemma homOfMono_id (n : ℕ) :
    homOfMono (𝟙 <| toSimplexCategory.obj ⦋n⦌ₛ) = 𝟙 (⦋n⦌ₛ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
def δ {n} (i : Fin (n + 2)) : ⦋n⦌ₛ ⟶ ⦋n + 1⦌ₛ :=
  homOfMono (SimplexCategory.δ i)

@[simp]
lemma toSimplexCategory_map_δ {n} (i : Fin (n + 2)) :
    toSimplexCategory.map (δ i) = SimplexCategory.δ i :=
  rfl

end SemiSimplexCategory

namespace CategoryTheory

abbrev SemisimplicialObject (C : Type*) [Category* C] : Type _ :=
  SemiSimplexCategoryᵒᵖ ⥤ C

set_option quotPrecheck false in
/-- `X _⦋n⦌` denotes the `n`th-term of the simplicial object X -/
scoped[Simplicial]
  notation3:1000 X " _⦋" n "⦌ₛ" =>
      (X : CategoryTheory.SemisimplicialObject _).obj (Opposite.op (SemiSimplexCategory.mk n))

def SemisimplicialObject.δ (X : SemisimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    X _⦋n + 1⦌ₛ ⟶ X _⦋n⦌ₛ :=
  X.map (SemiSimplexCategory.δ i).op

end CategoryTheory

namespace SSet

variable {K} in
noncomputable def N.Hom.hom {x y : K.N} (f : x ⟶ y) : ⦋x.dim⦌ ⟶ ⦋y.dim⦌ :=
  (SSet.N.le_iff_exists_mono.mp <| leOfHom f).choose

variable {K} in
instance {x y : K.N} (f : x ⟶ y) : Mono (N.Hom.hom f) :=
  (SSet.N.le_iff_exists_mono.mp <| leOfHom f).choose_spec.choose

variable {K} in
@[simp]
lemma N.Hom.hom_spec {x y : K.N} (f : x ⟶ y) : K.map (N.Hom.hom f).op y.simplex = x.simplex :=
  (SSet.N.le_iff_exists_mono.mp <| leOfHom f).choose_spec.choose_spec

abbrev nonDegenerateElements : ObjectProperty K.Elements :=
  fun x ↦ x.snd ∈ K.nonDegenerate _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps!]
def nonDegenerateElementsMap {K L : SSet.{u}} (f : K ⟶ L) [Mono f] :
    K.nonDegenerateElements.FullSubcategory ⥤ L.nonDegenerateElements.FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ CategoryOfElements.map f) <| by
    intro ⟨x, hx⟩
    dsimp
    simp only [nonDegenerateElements, CategoryOfElements.map_obj_fst, SimplexCategory.mk_len,
      Opposite.op_unop, CategoryOfElements.map_obj_snd]
    rwa [nonDegenerate_iff_of_mono]

def nonDegenerateElementsMapCompι {K L : SSet.{u}} (f : K ⟶ L) [Mono f] :
    nonDegenerateElementsMap f ⋙ L.nonDegenerateElements.ι ≅
      ObjectProperty.ι _ ⋙ CategoryOfElements.map f :=
  Iso.refl _

lemma ext_of_nonsingular [K.Nonsingular] {n : ℕ} (x : K _⦋n⦌) (hx : x ∈ K.nonDegenerate n)
    {m : SimplexCategory} {f g : m ⟶ ⦋n⦌} (h : K.map f.op x = K.map g.op x) : f = g := by
  have : Mono (uliftYonedaEquiv.symm x) := Nonsingular.mono' _ hx
  apply uliftYoneda.map_injective
  rw [← cancel_mono (uliftYonedaEquiv.symm x)]
  simp [uliftYonedaEquiv_symm_naturality_left, congr(uliftYonedaEquiv.symm $h)]

instance [K.Nonsingular] : Quiver.IsThin K.nonDegenerateElements.FullSubcategory := by
  intro x ⟨⟨⟨⟨n⟩⟩, val⟩, hy⟩
  refine ⟨fun f g ↦ ?_⟩
  ext : 2
  exact Opposite.unop_injective <| ext_of_nonsingular K _ x.property (f.1.2.trans g.1.2.symm)

@[ext (iff := false)]
lemma N.Hom.ext [K.Nonsingular] {x y : K.N} {f g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌}
    (hf : K.map f.op y.simplex = x.simplex) (hg : K.map g.op y.simplex = x.simplex) :
    f = g := by
  apply ext_of_nonsingular K y.simplex y.2
  rw [hf, hg]

variable {K} in
@[reassoc (attr := simp)]
lemma N.Hom.hom_comp [K.Nonsingular] {x y z : K.N} (f : x ⟶ y) (g : y ⟶ z) :
    N.Hom.hom (f ≫ g) = N.Hom.hom f ≫ N.Hom.hom g := by
  cat_disch

variable {K} in
@[reassoc (attr := simp)]
lemma N.Hom.hom_id [K.Nonsingular] (x : K.N) :
    N.Hom.hom (𝟙 x) = 𝟙 _ := by
  cat_disch

-- Δ_{K}
@[simps]
noncomputable
def ninclusion [K.Nonsingular] : K.Nᵒᵖ ⥤ K.Elements where
  obj Y := .mk (.op <| .mk Y.unop.dim) Y.unop.simplex
  map {Y Z} f := .mk (.op <| N.Hom.hom f.unop) (N.Hom.hom_spec _)

example : K.Elements ⥤ SimplexCategoryᵒᵖ := CategoryOfElements.π _

-- attribute [grind] Nonsingular.mono_of_mem_nonDegenerate

set_option backward.isDefEq.respectTransparency false in
instance mono_hom_nonDegenerateElements [K.Nonsingular]
    {x y : K.nonDegenerateElements.FullSubcategory} (f : x ⟶ y) :
    Mono f.hom.val.unop := by
  have : Mono (yonedaEquiv.{w}.symm y.obj.snd) := Nonsingular.mono' _ y.property
  have : Mono (yonedaEquiv.{w}.symm x.obj.snd) := Nonsingular.mono' _ x.property
  have heq : yonedaEquiv.{w}.symm y.1.2 =
      uliftYoneda.map f.hom.1.unop ≫ yonedaEquiv.symm x.1.2 := by
    -- TODO: make `SSet.yonedaEquiv` an `abbrev`?
    erw [uliftYonedaEquiv_symm_naturality_left]
    congr
    exact f.hom.2.symm
  have : Mono (uliftYoneda.{w}.map f.hom.val.unop) :=
    mono_of_mono_fac heq.symm
  exact Functor.mono_of_mono_map uliftYoneda.{w} this

set_option backward.isDefEq.respectTransparency false in
lemma map_mem_nonDegenerate_of_nonsingular [K.Nonsingular] (n m : SimplexCategory) (f : n ⟶ m)
    [Mono f] (x : K.obj (.op m)) (hx : x ∈ K.nonDegenerate m.len) :
    K.map f.op x ∈ K.nonDegenerate _ := by
  have : Mono (yonedaEquiv.symm <| K.map f.op x) := by
    have : yonedaEquiv.symm (K.map f.op x) = uliftYoneda.map f ≫ yonedaEquiv.symm x :=
      (uliftYonedaEquiv_symm_naturality_left _ _ _).symm
    rw [this]
    have : Mono (yonedaEquiv.symm x) := Nonsingular.mono' _ hx
    infer_instance
  have := (nonDegenerate_iff_of_mono (yonedaEquiv.symm <| K.map f.op x)
    (stdSimplex.objEquiv.symm (𝟙 _))).mpr (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate _)
  simpa using this

@[to_dual self]
theorem _root_.Quiver.Hom.unop_surjective {X Y : Cᵒᵖ} :
    Function.Surjective (Quiver.Hom.unop : (X ⟶ Y) → (Opposite.unop Y ⟶ Opposite.unop X)) :=
  fun f ↦ ⟨f.op, rfl⟩

@[to_dual self]
theorem _root_.Quiver.Hom.op_surjective {X Y : C} :
    Function.Surjective (Quiver.Hom.op : (X ⟶ Y) → (Opposite.op Y ⟶ Opposite.op X)) :=
  fun f ↦ ⟨f.unop, rfl⟩

set_option backward.isDefEq.respectTransparency false in
instance [K.Nonsingular] : K.nonDegenerateElements.ι.Initial := by
  refine ⟨fun ⟨⟨⟨n⟩⟩, x⟩ ↦ ?_⟩
  obtain ⟨m, f, hf, ⟨y, hy⟩, heq⟩ := exists_nonDegenerate K x
  let U : CostructuredArrow K.nonDegenerateElements.ι ⟨⟨⟨n⟩⟩, x⟩ :=
    CostructuredArrow.mk (Y := ⟨⟨_, y⟩, hy⟩) ⟨.op <| by exact f, heq.symm⟩
  have : Nonempty (CostructuredArrow K.nonDegenerateElements.ι ⟨⟨⟨n⟩⟩, x⟩) := ⟨U⟩
  suffices h : ∀ a : CostructuredArrow K.nonDegenerateElements.ι ⟨Opposite.op ⦋n⦌, x⟩,
      Nonempty (a ⟶ U) from
    zigzag_isConnected fun j₁ j₂ ↦ .trans (.of_hom (h _).some) (.of_inv (h _).some)
  rintro ⟨⟨⟨⟨⟨na⟩⟩, pa⟩, ha⟩, _, homa, ha'⟩
  dsimp at homa ha
  obtain ⟨homa, rfl⟩ := Quiver.Hom.op_surjective homa
  simp_rw [heq] at this
  obtain ⟨⟨⟨⟨ma⟩, τa, πa, rfl⟩, h⟩⟩ := HasStrongEpiMonoFactorisations.has_fac homa
  simp only [ObjectProperty.ι_obj, op_comp, Functor.map_comp,
    comp_apply] at ha'
  obtain rfl := unique_nonDegenerate_dim _ x πa
    ⟨_, K.map_mem_nonDegenerate_of_nonsingular _ _ τa pa ha⟩ ha'.symm f ⟨_, hy⟩ heq
  obtain rfl := congr($(unique_nonDegenerate_simplex _ _ πa
    ⟨_, K.map_mem_nonDegenerate_of_nonsingular _ _ τa pa ha⟩ ha'.symm f ⟨_, hy⟩ heq).1)
  obtain rfl := unique_nonDegenerate_map _ _ πa
    ⟨_, K.map_mem_nonDegenerate_of_nonsingular _ _ τa pa ha⟩ ha'.symm f ⟨_, hy⟩ heq
  exact ⟨CostructuredArrow.homMk ⟨.op τa, by simp [U]⟩ (by ext; simp [U])⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable
def nonDegenerateElementsEquiv [K.Nonsingular] :
    K.nonDegenerateElements.FullSubcategory ≌ K.Nᵒᵈ where
  functor.obj x := OrderDual.toDual ⟨⟨x.obj.snd⟩, x.property⟩
  functor.map {x y} f := homOfLE <| by
    rw [OrderDual.toDual_le_toDual, N.le_iff_exists_mono]
    exact ⟨f.hom.1.unop, inferInstance, f.hom.2⟩
  inverse.obj x := ⟨⟨_, (OrderDual.ofDual x).simplex⟩, (OrderDual.ofDual x).2⟩
  inverse.map {x y} f := ⟨.op <| N.Hom.hom _, by simp⟩
  unitIso :=
    NatIso.ofComponents
      (fun x ↦ ObjectProperty.isoMk _
        (CategoryOfElements.isoMk _ _ (.op <| Iso.refl _) (by simp)))
        (by dsimp; cat_disch)
  counitIso := Iso.refl _

@[simp]
lemma yonedaEquiv_symm_objEquiv_symm {n m : ℕ} (x : ⦋m⦌ ⟶ ⦋n⦌) :
    yonedaEquiv.symm (stdSimplex.objEquiv.symm x) = uliftYoneda.map x :=
  rfl

-- def asdfasdfasdf (n m : ℕ) :

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma map_objEquiv_objEquiv_symm_id (n m : ℕ) (x : Δ[n] _⦋m⦌) (i) :
    dsimp% Δ[n].map (stdSimplex.objEquiv x).op (stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) i = x i := by
  rfl

lemma mono_stdSimplex_objEquiv_of_mem_nonDegenerate {n m : ℕ} {x : Δ[n] _⦋m⦌}
    (hx : x ∈ Δ[n].nonDegenerate _) :
    Mono (stdSimplex.objEquiv x) := by
  obtain ⟨x, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  simpa using (SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono x).mp hx

set_option backward.isDefEq.respectTransparency false in
instance (n : ℕ) : (Δ[n] : SSet.{u}).Nonsingular where
  mono {m} := by
    intro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
    have : SSet.yonedaEquiv.symm (stdSimplex.objEquiv.symm x) = uliftYoneda.map x := by
      rfl
    rw [this]
    rw [uliftYoneda.{u}.mono_map_iff_mono]
    exact (SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono x).mp hx

set_option backward.isDefEq.respectTransparency false in
instance (n : ℕ) : OrderTop (Δ[n] : SSet.{u}).N where
  top := ⟨.mk (stdSimplex.objEquiv.symm (𝟙 _)), stdSimplex.objEquiv_symm_id_mem_nonDegenerate n⟩
  le_top a := by
    rw [N.le_iff_exists_mono]
    exact ⟨stdSimplex.objEquiv a.simplex, mono_stdSimplex_objEquiv_of_mem_nonDegenerate a.2,
      stdSimplex.ext _ a.simplex (by simp)⟩

abbrev stdSimplex.topFaceNonDegenerate (n : ℕ) :
    (Δ[n] : SSet.{u}).nonDegenerateElements.FullSubcategory :=
  ⟨⟨_, stdSimplex.objEquiv.symm (𝟙 _)⟩, stdSimplex.objEquiv_symm_id_mem_nonDegenerate n⟩

noncomputable
def isInitialObjEquivSymmIdNonDegenerateElements (n : ℕ) : IsInitial
    (stdSimplex.topFaceNonDegenerate n) :=
  IsInitial.isInitialObj (Δ[n].nonDegenerateElementsEquiv.inverse) ⊥ isInitialBot

@[simp]
lemma dimp_N_stdSimplex_top (n : ℕ) : (⊤ : (Δ[n] : SSet.{u}).N).dim = n :=
  rfl

@[simp]
lemma simplex_N_stdSimplex_top (n : ℕ) :
    (⊤ : (Δ[n] : SSet.{u}).N).simplex = stdSimplex.objEquiv.symm (𝟙 _) :=
  rfl

instance [K.Nonsingular] (y : K.Subcomplex) : (y : SSet.{w}).Nonsingular :=
  Nonsingular.of_mono y.ι

set_option backward.defeqAttrib.useBackward true in
noncomputable def nonDegenerateElementsπOfNonsingular (K : SSet.{u}) [K.Nonsingular] :
    K.nonDegenerateElements.FullSubcategory ⥤ SemiSimplexCategoryᵒᵖ :=
  (SemiSimplexCategory.lift (K.nonDegenerateElements.ι ⋙ CategoryOfElements.π K).leftOp ?_).rightOp
where finally
  intro ⟨X⟩ ⟨Y⟩ f
  dsimp
  simp only [unop_mono_iff]
  obtain ⟨f, rfl⟩ := _root_.Quiver.Hom.op_surjective f
  rw [Quiver.Hom.unop_op, ← unop_mono_iff]
  infer_instance

@[simp]
lemma nonDegenerateElementsπOfNonsingular_obj [K.Nonsingular]
    (x : K.nonDegenerateElements.FullSubcategory) :
    K.nonDegenerateElementsπOfNonsingular.obj x = .op (.mk x.obj.fst.unop.len) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma nonDegenerateElementsπOfNonsingular_map [K.Nonsingular]
    {x y : K.nonDegenerateElements.FullSubcategory} (f : x ⟶ y) :
    K.nonDegenerateElementsπOfNonsingular.map f =
      .op (SemiSimplexCategory.homOfMono <| f.hom.val.unop) :=
  rfl

@[simps!]
noncomputable def nonDegenerateElementsMapCompπOfNonsingular {K L : SSet.{u}} (f : K ⟶ L) [Mono f]
    [K.Nonsingular] [L.Nonsingular] :
    nonDegenerateElementsMap f ⋙ L.nonDegenerateElementsπOfNonsingular ≅
      K.nonDegenerateElementsπOfNonsingular :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
def N.orderHomOfMono {K L : SSet.{u}} (f : K ⟶ L) [Mono f] : K.N →o L.N where
  toFun x := N.mk (f.app _ x.simplex)
    ((nonDegenerate_iff_of_mono f x.simplex).mpr x.nonDegenerate)
  monotone' x y hxy := by
    rw [le_iff_exists_mono] at hxy ⊢
    obtain ⟨g, hg, heq⟩ := hxy
    simp only [mk_dim, mk_simplex, exists_prop]
    exact ⟨g, hg, by simp [← heq]⟩

end SSet

namespace CategoryTheory

variable {C : Type*} [Category* C]

structure Functor.Coelements (F : Cᵒᵖ ⥤ Type*) where
  obj : C
  val : F.obj (.op obj)

variable (F : Cᵒᵖ ⥤ Type*)

--namespace Functor.Coelements
--
--structure Hom (X Y : F.Coelements) where
--  hom : X.obj ⟶ Y.obj
--  map_hom_val : F.map hom.op Y.val = X.val := by cat_disch
--
--instance : Category F.Coelements where
--  Hom := Hom F
--  id X := { hom := 𝟙 _ }
--  comp {X Y Z} f g := { hom := f.hom ≫ g.hom }
--
--end Functor.Coelements

variable {D : Type*} [Category* D] {E : Type*} [Category* E]
variable {A : Type*} [Category* A]

-- `E = K.nonDegenerateElements.FullSubcategory`
-- `C = SemiSimplexCategory`
-- `D = SimplexCategory`
-- `F = toSimplexCategory`
-- `P = map mono`
structure FunctorLift (F : C ⥤ D) (P : ObjectProperty (E ⥤ D)) where
  lift (G : E ⥤ D) (h : P G) : E ⥤ C
  liftIso (G : E ⥤ D) (h : P G) : lift G h ⋙ F ≅ G

structure FunctorLift' (F : C ⥤ D) (P : ObjectProperty (E ⥤ D)) where
  lift : P.FullSubcategory ⥤ (E ⥤ C)
  liftIso : lift ⋙ (Functor.whiskeringRight _ _ _).obj F ≅ P.ι

namespace FunctorLift

@[simps]
def id : FunctorLift (𝟭 C) (⊤ : ObjectProperty (E ⥤ C)) where
  lift G _ := G
  liftIso _ _ := .refl _

variable {F : C ⥤ D} {P : ObjectProperty (Eᵒᵖ ⥤ D)} (H : FunctorLift F P)

abbrev bracketDiag (X : Cᵒᵖ ⥤ A) (K : Dᵒᵖ ⥤ Type u) (incl : E ⥤ K.Elements)
    (h : P (incl.op ⋙ (CategoryOfElements.π K).leftOp)) :
    E ⥤ A :=
  Functor.rightOp (H.lift (incl.op ⋙ (CategoryOfElements.π _).leftOp) h) ⋙ X

end FunctorLift

namespace FunctorLift'

variable {F : C ⥤ D} {P : ObjectProperty (Eᵒᵖ ⥤ D)} (H : FunctorLift' F P)

abbrev bracketDiag' (X : Cᵒᵖ ⥤ A) (K : Dᵒᵖ ⥤ Type u) (incl : E ⥤ K.Elements)
    (h : P (incl.op ⋙ (CategoryOfElements.π K).leftOp)) :
    E ⥤ A :=
  Functor.rightOp (H.lift.obj ⟨incl.op ⋙ (CategoryOfElements.π _).leftOp, h⟩) ⋙ X

end FunctorLift'

end CategoryTheory

namespace SemiSimplexCategory

@[simps]
def functorLift (E : Type*) [Category* E] :
    FunctorLift (toSimplexCategory) (fun G ↦ ∀ ⦃X Y : E⦄ (f : X ⟶ Y), Mono (G.map f)) where
  lift G h := lift G h
  liftIso G h := liftComp _

end SemiSimplexCategory

namespace CategoryTheory.SemisimplicialObject

/-!
## Bracket for semi-simplicial objects
-/

variable (X : SemisimplicialObject C) (K : SSet.{u})

set_option backward.isDefEq.respectTransparency false in
noncomputable abbrev bracketDiag (X : SemisimplicialObject C) (K : SSet.{u}) [K.Nonsingular] :
    K.nonDegenerateElements.FullSubcategory ⥤ C :=
  K.nonDegenerateElementsπOfNonsingular ⋙ X

set_option backward.defeqAttrib.useBackward true in
noncomputable abbrev bracketDiag' (X : SemisimplicialObject C) (K : SSet.{u}) [K.Nonsingular] :
    K.nonDegenerateElements.FullSubcategory ⥤ C :=
  FunctorLift.bracketDiag (SemiSimplexCategory.functorLift _) X K K.nonDegenerateElements.ι <| by
    intro ⟨X⟩ ⟨Y⟩ f
    dsimp
    simp only [unop_mono_iff]
    obtain ⟨f, rfl⟩ := _root_.Quiver.Hom.op_surjective f
    rw [Quiver.Hom.unop_op, ← unop_mono_iff]
    infer_instance

abbrev HasBracket [K.Nonsingular] : Prop := HasLimit (X.bracketDiag K)

variable [K.Nonsingular]

/--
The bracket `X[K]` of a semi-simplicial object `X` with a non-singular
simplicial set `K`.
Note: In the case where `X` is simplicial, we have a more natural construction
`SimplicialObject.bracket` below.
-/
noncomputable abbrev bracket [X.HasBracket K] : C :=
  limit (X.bracketDiag K)

instance [HasLimitsOfShape K.Nᵒᵈ C] : X.HasBracket K :=
  Functor.Initial.hasLimit_of_comp K.nonDegenerateElementsEquiv.inverse

instance [HasFiniteLimits C] [K.Finite] : X.HasBracket K :=
  have : Fintype K.N := Fintype.ofFinite _
  inferInstance

noncomputable
def bracketIsoOfNonsingular [X.HasBracket K] :
    X.bracket K ≅
      limit (K.nonDegenerateElementsEquiv.inverse ⋙ X.bracketDiag K) :=
  (Functor.Initial.limitIso _ _).symm

-- TODO: add `π` lemma for `limitIso`
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketIsoOfNonsingular_hom_π [X.HasBracket K] (x : K.Nᵒᵈ) :
    (X.bracketIsoOfNonsingular K).hom ≫ limit.π _ x =
      limit.π _ _ := by
  simp [bracketIsoOfNonsingular, CategoryTheory.Functor.Initial.limitIso_inv]

-- TODO: add `π` lemma for `limitIso`
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketIsoOfNonsingular_inv_π [X.HasBracket K] (x : K.Nᵒᵈ) :
    dsimp% (X.bracketIsoOfNonsingular K).inv ≫ limit.π _ _ =
      limit.π _ x := by
  simp [← cancel_epi (X.bracketIsoOfNonsingular K).hom]

open SSet

noncomputable def bracketStdSimplexIso (n : ℕ) : X.bracket Δ[n] ≅ X _⦋n⦌ₛ :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (limitOfDiagramInitial (isInitialObjEquivSymmIdNonDegenerateElements n) _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketStdSimplexIso_inv_π (n : ℕ) :
    (X.bracketStdSimplexIso n).inv ≫
      limit.π _ (stdSimplex.topFaceNonDegenerate n) = 𝟙 _ := by
  -- TODO: fix homOfMono (!)
  have := X.map_id (.op <| ⦋n⦌ₛ)
  simp only [Functor.comp_obj, nonDegenerateElementsπOfNonsingular_obj, bracketStdSimplexIso,
    limit.conePointUniqueUpToIso_inv_comp, coneOfDiagramInitial_pt, coneOfDiagramInitial_π_app,
    IsInitial.to_self, Functor.comp_map, nonDegenerateElementsπOfNonsingular_map,
    ObjectProperty.FullSubcategory.id_hom, CategoryOfElements.id_val, unop_id]
  erw [SemiSimplexCategory.homOfMono_id]
  assumption

variable {K L M : SSet.{u}} [K.Nonsingular] [L.Nonsingular] [M.Nonsingular]

set_option backward.isDefEq.respectTransparency false in
noncomputable
def bracketMap [X.HasBracket K] [X.HasBracket L] (f : K ⟶ L) [Mono f] :
    X.bracket L ⟶ X.bracket K :=
  letI e : nonDegenerateElementsMap f ⋙ L.nonDegenerateElementsπOfNonsingular ⋙ X ≅ _ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (nonDegenerateElementsMapCompπOfNonsingular f) _
  haveI : HasLimit (nonDegenerateElementsMap f ⋙ L.nonDegenerateElementsπOfNonsingular ⋙ X) :=
    hasLimit_of_iso e.symm
  limit.pre _ _ ≫ (HasLimit.isoOfNatIso e).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketMap_π [X.HasBracket K] [X.HasBracket L] (f : K ⟶ L) [Mono f]
    (x : K.nonDegenerateElements.FullSubcategory) :
    X.bracketMap f ≫ limit.π _ x =
      limit.π _ ((nonDegenerateElementsMap f).obj x) := by
  simp [bracketMap]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketMap_comp [X.HasBracket K] [X.HasBracket L] [X.HasBracket M]
      (f : K ⟶ L) (g : L ⟶ M) [Mono f] [Mono g] :
    X.bracketMap (f ≫ g) = X.bracketMap g ≫ X.bracketMap f := by
  ext
  simp only [bracketMap_π, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma bracketMap_id [X.HasBracket K] : X.bracketMap (𝟙 K) = 𝟙 _ := by
  ext ⟨j⟩
  simp only [bracketMap_π, Category.id_comp]
  rfl

lemma _root_.CategoryTheory.Functor.isEmpty_elements {C : Type*} [Category* C] {F : C ⥤ Type*}
    (h : IsInitial F) :
    IsEmpty F.Elements := by
  constructor
  intro x
  have : IsEmpty (F.obj x.1) := by
    rw [← Types.initial_iff_empty]
    constructor
    exact .isInitialObj ((evaluation _ _).obj x.1) _ h
  apply this.elim' x.2

noncomputable def isTerminalBracketOfIsInitial [X.HasBracket K] (h : IsInitial K) :
    IsTerminal (X.bracket K) :=
  haveI : IsEmpty K.Elements := K.isEmpty_elements h
  haveI : IsEmpty K.nonDegenerateElements.FullSubcategory := K.nonDegenerateElements.ι.obj.isEmpty
  (Limits.isLimitEquivIsTerminalOfIsEmpty _ _) (limit.isLimit _)

noncomputable def isInitialBoundaryZero : IsInitial (∂Δ[0] : SSet.{u}) := by
  apply Nonempty.some
  rw [boundary_zero]
  exact ⟨SSet.Subcomplex.isInitialBot⟩

lemma _root_.SSet.yonedaEquiv_mem_nonDegenerate_of_mono (n : ℕ) {K : SSet.{u}} (f : Δ[n] ⟶ K)
    [Mono f] :
    SSet.yonedaEquiv f ∈ nonDegenerate _ n :=
  (nonDegenerate_iff_of_mono f (stdSimplex.objEquiv.symm (𝟙 _))).mpr
    (stdSimplex.objEquiv_symm_id_mem_nonDegenerate n)

@[simps]
noncomputable
def bracketFunctor {J : Type*} [Category* J] (F : J ⥤ SSet.{u}) [∀ j, Nonsingular (F.obj j)]
    [∀ j, X.HasBracket (F.obj j)] [∀ ⦃i j : J⦄ (f : i ⟶ j), Mono (F.map f)] :
    Jᵒᵖ ⥤ C where
  obj j := X.bracket (F.obj j.unop)
  map f := X.bracketMap (F.map f.unop)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable
def bracketCone {J : Type*} [Category* J] (F : J ⥤ SSet.{u}) [∀ j, Nonsingular (F.obj j)]
    [∀ j, X.HasBracket (F.obj j)] [∀ ⦃i j : J⦄ (f : i ⟶ j), Mono (F.map f)]
    (c : Cocone F) [c.pt.Nonsingular] [X.HasBracket c.pt]
    [∀ j, Mono (c.ι.app (Opposite.unop j))] :
    Cone (X.bracketFunctor F) where
  pt := X.bracket c.pt
  π.app j := X.bracketMap (c.ι.app j.unop)
  π.naturality j k f := by simp [← bracketMap_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- Note: The folĺowing proof is painful, because `X[-]` is not fully functorial, when
-- `X` is only semi-simplicial.
/-- `X[-]` sends colimits to limits. -/
noncomputable
def isLimitBracketCone {J : Type*} [Category* J] (F : J ⥤ SSet.{u}) [∀ j, Nonsingular (F.obj j)]
    [∀ j, X.HasBracket (F.obj j)] [∀ ⦃i j : J⦄ (f : i ⟶ j), Mono (F.map f)]
    (c : Cocone F) [c.pt.Nonsingular] [X.HasBracket c.pt]
    [∀ j, Mono (c.ι.app (Opposite.unop j))] (hc : IsColimit c) :
    IsLimit (X.bracketCone F c) where
  lift s := by
    dsimp [bracket]
    let t : Cone (X.bracketDiag c.pt) :=
      { pt := s.pt
        π.app := fun ⟨⟨⟨⟨n⟩⟩, xp⟩, hx⟩ ↦ by
          dsimp
          let cn := Functor.mapCocone ((evaluation (SimplexCategoryᵒᵖ) (Type u)).obj (.op ⦋n⦌)) c
          let x := (Functor.coconeTypesEquiv _).symm cn
          have : x.IsColimit := sorry
          let aa : (F ⋙ evaluation SimplexCategoryᵒᵖ (Type u) _⦋n⦌).CoconeTypes :=
            {
              pt := s.pt ⟶ X _⦋n⦌ₛ
              ι j := by
                dsimp
                sorry
                --dsimp at x
                --exact s.π.app (.op j) ≫ limit.π _ ⟨⟨_, x⟩, by dsimp⟩ ≫ _
              ι_naturality := sorry
            }
          let : c.pt _⦋n⦌ → (s.pt ⟶ X _⦋n⦌ₛ) :=
            this.desc aa
          -- let sapp (j) := s.π.app j ≫ limit.π _ ⟨⟨.op ⦋n⦌, _⟩, sorry⟩
          -- dsimp at sapp
          apply this
          exact xp
        π.naturality := sorry
      }
    exact limit.lift _ t
  fac := sorry
  uniq := sorry

def inclNonDegenerateBoundaryOne :
    Discrete WalkingPair ⥤ (∂Δ[1] : SSet.{u}).nonDegenerateElements.FullSubcategory :=
  Discrete.functor fun x ↦ match x with
  | .left =>
    ⟨⟨_, uliftYonedaEquiv (boundary.ι (n := 0) 0)⟩,
      SSet.yonedaEquiv_mem_nonDegenerate_of_mono _ _⟩
  | .right =>
    ⟨⟨_, uliftYonedaEquiv (boundary.ι (n := 0) 1)⟩,
      SSet.yonedaEquiv_mem_nonDegenerate_of_mono _ _⟩

def inclNonDegenerateBoundaryOne' :
    Discrete WalkingPair ⥤ (∂Δ[1] : SSet.{u}).nonDegenerateElements.FullSubcategory :=
  Discrete.functor fun x ↦ match x with
  | .left =>
    ⟨⟨_, uliftYonedaEquiv (boundary.ι (n := 0) 0)⟩,
      SSet.yonedaEquiv_mem_nonDegenerate_of_mono _ _⟩
  | .right =>
    ⟨⟨_, uliftYonedaEquiv (boundary.ι (n := 0) 1)⟩,
      SSet.yonedaEquiv_mem_nonDegenerate_of_mono _ _⟩

instance : inclNonDegenerateBoundaryOne.Initial := by
  sorry

end CategoryTheory.SemisimplicialObject

namespace CategoryTheory

variable (X : SemisimplicialObject C)

/--
A semi-simplicial object in a category `C` with finite limits is a `P`-hypercover
if the natural map `X[Δⁿ] ⟶ X[∂Δⁿ]` satisfies `P`.

To obtain the usual notion of a hypercover on a site `C` with topology `J`, we
take a semi-simplicial object `H` in `FormalCoproduct C` and ask
for the induced semi-simplical object in `Cᵒᵖ ⥤ Type _` to be a `P`-hypercover, where
`P` is the class of "covering morphisms" (which SGA calls "morphisme couvrant"):
A morphism of presheafs `K ⟶ L` is covering if it becomes an epimorphism after
sheafification.
(see `GrothendieckTopology.couvrant` below)

The `1`-truncation of a hypercover in the above sense induces a `1`-hypercover
(see `CategoryTheory.GrothendieckTopology.OneHypercover.ofIsHypercover`).
-/
structure MorphismProperty.IsHypercover [HasFiniteLimits C] (P : MorphismProperty C) : Prop where
  prop_bracketMap (n : ℕ) : P (X.bracketMap <| (∂Δ[n] : (Δ[n] : SSet.{0}).Subcomplex).ι)

variable (J : GrothendieckTopology C)

variable {A : Type*} [Category* A]

def ObjectProperty.isPrelocal (P : ObjectProperty C) : MorphismProperty C := fun _ _ f =>
  ∀ Z, P Z → Function.Injective (fun (g : _ ⟶ Z) ↦ f ≫ g)

/-- Covering morphisms in the sense of SGA. -/
def GrothendieckTopology.couvrant : MorphismProperty (Cᵒᵖ ⥤ A) :=
  ObjectProperty.isPrelocal (Presheaf.IsSheaf J)

namespace Limits.FormalCoproduct

def objIsoOfEq (X : FormalCoproduct.{w} C) {i j : X.I} (hij : i = j) :
    X.obj i ≅ X.obj j :=
  eqToIso (by rw [hij])

@[simp]
lemma objIsoOfEq_rfl (X : FormalCoproduct.{w} C) (i : X.I) :
    X.objIsoOfEq (rfl : i = i) = Iso.refl _ :=
  rfl

@[simp]
lemma objIsoOfEq_trans (X : FormalCoproduct.{w} C) {i j k : X.I}
    (hij : i = j) (hjk : j = k) :
    X.objIsoOfEq hij ≪≫ X.objIsoOfEq hjk = X.objIsoOfEq (hij.trans hjk) := by
  subst hij hjk
  simp

@[simp]
lemma objIsoOfEq_symm (X : FormalCoproduct.{w} C) {i j : X.I}
    (hij : i = j) :
    (X.objIsoOfEq hij).symm = X.objIsoOfEq hij.symm := by
  subst hij
  simp

variable {C : Type*} [Category.{v} C]

noncomputable def uliftYoneda : FormalCoproduct.{w} C ⥤ Cᵒᵖ ⥤ Type (max w v) :=
  (eval _ _).obj CategoryTheory.uliftYoneda

end Limits.FormalCoproduct

/-- The `1`-truncation of a semi-simplical object in `FormalCoproduct.{w} (Over S)`
induces a pre-`1`-hypercover of `S`. -/
@[simps]
def SemisimplicialObject.preOneHypercover {S : C}
    (H : SemisimplicialObject (FormalCoproduct.{w} (Over S))) : PreOneHypercover.{w} S where
  I₀ := (H _⦋0⦌ₛ).I
  X i := ((H _⦋0⦌ₛ).obj i).left
  f i := ((H _⦋0⦌ₛ).obj i).hom
  I₁ i j := { x : (H _⦋1⦌ₛ).I // (H.δ 0).f x = i ∧ (H.δ 1).f x = j }
  Y _ _ k := ((H _⦋1⦌ₛ).obj k).left
  p₁ i j k := ((H.δ 0).φ k.1).left ≫ ((H _⦋0⦌ₛ).objIsoOfEq k.2.1).hom.left
  p₂ i j k := ((H.δ 1).φ k.1).left ≫ ((H _⦋0⦌ₛ).objIsoOfEq k.2.2).hom.left
  w := by simp

/-- The `1`-truncation of a hypercover induces a `1`-hypercover. -/
def GrothendieckTopology.OneHypercover.ofIsHypercover {S : C}
    (H : SemisimplicialObject (FormalCoproduct.{w} (Over S)))
    (h : (J.over S).couvrant.IsHypercover <| H ⋙ FormalCoproduct.uliftYoneda) :
    J.OneHypercover S where
  __ := H.preOneHypercover
  mem₀ := by
    have := h.prop_bracketMap 0
    sorry
  mem₁ := sorry

end CategoryTheory

namespace CategoryTheory.SimplicialObject

/-!
## Bracket for simplicial objects
-/

abbrev bracketDiag' : K.Elements ⥤ C :=
  FunctorLift.bracketDiag .id X K (𝟭 _) <| by tauto

noncomputable abbrev bracketDiag : K.Elements ⥤ C :=
  CategoryOfElements.π K ⋙ X

example : bracketDiag' X K = bracketDiag X K := rfl

abbrev HasBracket : Prop := HasLimit (X.bracketDiag K)

/-- The bracket `X[K]` of a simplical object `X` with a simplicial set `K`. -/
noncomputable abbrev bracket [X.HasBracket K] : C :=
  limit (X.bracketDiag K)

instance [K.Nonsingular] [HasLimitsOfShape K.Nᵒᵈ C] : X.HasBracket K :=
  Functor.Initial.hasLimit_of_comp
    (K.nonDegenerateElementsEquiv.inverse ⋙ K.nonDegenerateElements.ι)

instance [K.Nonsingular] [HasFiniteLimits C] [K.Finite] : X.HasBracket K :=
  have := Fintype.ofFinite K.N
  inferInstance

noncomputable
def bracketIsoOfNonsingular [K.Nonsingular] [X.HasBracket K] :
    X.bracket K ≅
      limit (K.nonDegenerateElementsEquiv.inverse ⋙ K.nonDegenerateElements.ι ⋙ X.bracketDiag K) :=
  (Functor.Initial.limitIso _ _).symm ≪≫ HasLimit.isoOfNatIso (Functor.associator _ _ _)

-- TODO: add `π` lemma for `limitIso`
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketIsoOfNonsingular_hom_π [K.Nonsingular] [X.HasBracket K] (x : K.Nᵒᵈ) :
    (X.bracketIsoOfNonsingular K).hom ≫ limit.π _ x =
      limit.π _ _ := by
  simp [bracketIsoOfNonsingular, CategoryTheory.Functor.Initial.limitIso_inv]

-- TODO: add `π` lemma for `limitIso`
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketIsoOfNonsingular_inv_π [K.Nonsingular] [X.HasBracket K] (x : K.Nᵒᵈ) :
    dsimp% (X.bracketIsoOfNonsingular K).inv ≫ limit.π _ _ =
      limit.π _ x := by
  simp [← cancel_epi (X.bracketIsoOfNonsingular K).hom]

open SSet

noncomputable def bracketStdSimplexIso (n : ℕ) : X.bracket Δ[n] ≅ X _⦋n⦌ :=
  X.bracketIsoOfNonsingular _ ≪≫
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial isInitialBot _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketStdSimplexIso_inv_π (n : ℕ) :
    (X.bracketStdSimplexIso n).inv ≫ limit.π _ ⟨_, stdSimplex.objEquiv.symm (𝟙 _)⟩ = 𝟙 _ := by
  have : (X.bracketIsoOfNonsingular Δ[n]).inv ≫
      limit.π (X.bracketDiag (Δ[n] : SSet.{_}))
        ⟨Opposite.op ⦋n⦌, stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)⟩ = limit.π _ ⊥ :=
    X.bracketIsoOfNonsingular_inv_π Δ[n] ⊥
  dsimp
  simp only [bracketStdSimplexIso, Iso.trans_inv, Category.assoc]
  rw [this]
  simp

example (n : ℕ) : (∂Δ[n] : SSet.{u}).Nonsingular :=
  inferInstance

variable {K L M : SSet.{u}}

noncomputable
def bracketMap [X.HasBracket K] [X.HasBracket L] (f : K ⟶ L) :
    X.bracket L ⟶ X.bracket K :=
  haveI : HasLimit (CategoryOfElements.map f ⋙ CategoryOfElements.π L ⋙ X) :=
    hasLimit_of_iso (Functor.isoWhiskerRight (CategoryOfElements.mapπiso f) _).symm
  limit.pre (CategoryOfElements.π L ⋙ X) (CategoryOfElements.map f) ≫
    (HasLimit.isoOfNatIso <| (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CategoryOfElements.mapπiso _) _).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketMap_π [X.HasBracket K] [X.HasBracket L] (f : K ⟶ L) (x : K.Elements) :
    X.bracketMap f ≫ limit.π _ x = limit.π _ ((CategoryOfElements.map f).obj x) := by
  simp [bracketMap]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketMap_comp [X.HasBracket K] [X.HasBracket L] [X.HasBracket M]
      (f : K ⟶ L) (g : L ⟶ M) :
    X.bracketMap (f ≫ g) = X.bracketMap g ≫ X.bracketMap f := by
  ext
  simp [CategoryOfElements.map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma bracketMap_id [X.HasBracket K] : X.bracketMap (𝟙 K) = 𝟙 _ := by
  ext ⟨j⟩
  simp [CategoryOfElements.map]

end SimplicialObject

end CategoryTheory
