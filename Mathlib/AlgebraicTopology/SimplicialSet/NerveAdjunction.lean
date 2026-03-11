/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# The adjunction between the nerve and the homotopy category functor

We define an adjunction `nerveAdjunction : hoFunctor ⊣ nerveFunctor` between the functor that
takes a simplicial set to its homotopy category and the functor that takes a category to its nerve.

Up to natural isomorphism, this is constructed as the composite of two other adjunctions,
namely `nerve₂Adj : hoFunctor₂ ⊣ nerveFunctor₂` between analogously-defined functors involving
the category of 2-truncated simplicial sets and `coskAdj 2 : truncation 2 ⊣ Truncated.cosk 2`. The
aforementioned natural isomorphism

`cosk₂Iso : nerveFunctor ≅ nerveFunctor₂ ⋙ Truncated.cosk 2`

exists because nerves of categories are 2-coskeletal.

We also prove that `nerveFunctor` is fully faithful, demonstrating that `nerveAdjunction` is
reflective. Since the category of simplicial sets is cocomplete, we conclude in
`Mathlib/CategoryTheory/Category/Cat/Colimit.lean` that the category of categories has colimits.

Finally we show that `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` preserves finite cartesian products; note
that it fails to preserve infinite products.

-/

@[expose] public section

universe u

open CategoryTheory Nerve Simplicial SimplicialObject.Truncated
  SimplexCategory.Truncated Opposite Limits

namespace SSet

namespace Truncated

section liftOfStrictSegal
/-! The goal of this section is to define `SSet.Truncated.liftOfStrictSegal`
which allows to construct of morphism `X ⟶ Y` of `2`-truncated simplicial sets
from the data of maps on `0`- and `1`-simplices when `Y` is strict Segal.
-/

variable {n : ℕ} {X Y : Truncated.{u} 2} (f₀ : X _⦋0⦌₂ → Y _⦋0⦌₂) (f₁ : X _⦋1⦌₂ → Y _⦋1⦌₂)
  (hδ₁ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₁ x))
  (hδ₀ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₁ x))
  (H : ∀ (x : X _⦋2⦌₂) (y : Y _⦋2⦌₂), f₁ (X.map (δ₂ 2).op x) = Y.map (δ₂ 2).op y →
    f₁ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op y →
      f₁ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op y)
  (hσ : ∀ (x : X _⦋0⦌₂), f₁ (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₀ x))
  (hY : Y.StrictSegal)

namespace liftOfStrictSegal

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `SSet.Truncated.liftOfStrictSegal`. -/
def f₂ (x : X _⦋2⦌₂) : Y _⦋2⦌₂ :=
  (hY.spineEquiv 2).symm
    (.mk₂ (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 2).op x)))
      (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 0).op x))) (by
        simp only [spine_vertex]
        rw [← δ₂_one_eq_const, ← δ₂_zero_eq_const, ← hδ₁, ← hδ₀]
        simp only [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_δ₂_two]))

@[simp]
lemma spineEquiv_f₂_arrow_zero (x : X _⦋2⦌₂) :
    ((hY.spineEquiv 2) (f₂ f₀ f₁ hδ₁ hδ₀ hY x)).arrow 0 = f₁ (X.map (δ₂ 2).op x) := by
  simp [f₂]

@[simp]
lemma spineEquiv_f₂_arrow_one (x : X _⦋2⦌₂) :
    ((hY.spineEquiv 2) (f₂ f₀ f₁ hδ₁ hδ₀ hY x)).arrow 1 = f₁ (X.map (δ₂ 0).op x) := by
  simp [f₂]

lemma hδ'₀ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) := by
  simp [← spineEquiv_f₂_arrow_one f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_one_eq_δ]

lemma hδ'₂ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 2).op x) = Y.map (δ₂ 2).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) := by
  simp [← spineEquiv_f₂_arrow_zero f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_zero_eq_δ]

include H in
lemma hδ'₁ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) :=
  H x (f₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₀ f₀ f₁ hδ₁ hδ₀ hY x)

include hσ in
lemma hσ'₀ (x : X _⦋1⦌₂) :
    f₂ f₀ f₁ hδ₁ hδ₀ hY (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₁ x) := by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    dsimp [StrictSegal.spineEquiv]
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero, op_comp,
      Functor.map_comp_apply, hσ, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← Functor.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero,
      op_comp, Functor.map_comp_apply, hδ₁]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_one_eq_δ,
      ← Functor.map_comp_apply, ← op_comp]

include hσ in
lemma hσ'₁ (x : X _⦋1⦌₂) :
    f₂ f₀ f₁ hδ₁ hδ₀ hY (X.map (σ₂ 1).op x) = Y.map (σ₂ 1).op (f₁ x) := by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← Functor.map_comp_apply, ← op_comp]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    dsimp [StrictSegal.spineEquiv]
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one, op_comp,
      Functor.map_comp_apply, hσ, SimplexCategory.mkOfSucc_one_eq_δ,
      ← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one,
      op_comp, Functor.map_comp_apply, hδ₀]

/-- Auxiliary definition for `SSet.Truncated.liftOfStrictSegal`. -/
def app (n : (SimplexCategory.Truncated 2)ᵒᵖ) : X.obj n ⟶ Y.obj n := by
  obtain ⟨n, hn⟩ := n
  induction n using SimplexCategory.rec with | _ n
  match n with
  | 0 => exact TypeCat.ofHom ⟨f₀⟩
  | 1 => exact TypeCat.ofHom ⟨f₁⟩
  | 2 => exact TypeCat.ofHom ⟨f₂ f₀ f₁ hδ₁ hδ₀ hY⟩

/-- The property of morphisms in `SimplexCategory.Truncated 2` for
which `liftOfStrictSegal.app` is natural. -/
abbrev naturalityProperty : MorphismProperty (SimplexCategory.Truncated 2) :=
  (MorphismProperty.naturalityProperty (app f₀ f₁ hδ₁ hδ₀ hY)).unop

include H hσ in
lemma naturalityProperty_eq_top :
    naturalityProperty f₀ f₁ hδ₁ hδ₀ hY = ⊤ := by
  refine SimplexCategory.Truncated.morphismProperty_eq_top _
    (fun n hn i ↦ ?_) (fun n hn i ↦ ?_)
  · obtain _ | _ | n := n
    · fin_cases i
      · ext; apply hδ₀
      · ext; apply hδ₁
    · fin_cases i
      · ext; apply hδ'₀ f₀ f₁ hδ₁ hδ₀ hY
      · ext; apply hδ'₁ f₀ f₁ hδ₁ hδ₀ H hY
      · ext; apply hδ'₂ f₀ f₁ hδ₁ hδ₀ hY
    · lia
  · obtain _ | _ | n := n
    · fin_cases i
      ext; apply hσ
    · fin_cases i
      · ext; apply hσ'₀ f₀ f₁ hδ₁ hδ₀ hσ hY
      · ext; apply hσ'₁ f₀ f₁ hδ₁ hδ₀ hσ hY
    · lia

end liftOfStrictSegal

open liftOfStrictSegal in
/-- Constructor for morphisms `X ⟶ Y` between `2`-truncated simplicial sets from
the data of maps on `0`- and `1`-simplices when `Y` is strict Segal. -/
def liftOfStrictSegal : X ⟶ Y where
  app := liftOfStrictSegal.app f₀ f₁ hδ₁ hδ₀ hY
  naturality _ _ φ :=
    (liftOfStrictSegal.naturalityProperty_eq_top f₀ f₁ hδ₁ hδ₀ H hσ hY).symm.le
      φ.unop (by simp)

lemma liftOfStrictSegal_app_0 :
    (liftOfStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (op ⦋0⦌₂) = TypeCat.ofHom ⟨f₀⟩ := rfl

lemma liftOfStrictSegal_app_1 :
    (liftOfStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (op ⦋1⦌₂) = TypeCat.ofHom ⟨f₁⟩ := rfl

end liftOfStrictSegal

namespace HomotopyCategory

variable {X : Truncated.{u} 2} {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- Given a `2`-truncated simplicial set `X` and a category `C`,
this is the functor `X.HomotopyCategory ⥤ C` corresponding to
a morphism `X ⟶ (truncation 2).obj (nerve C)`. -/
def descOfTruncation (φ : X ⟶ (truncation 2).obj (nerve C)) :
    X.HomotopyCategory ⥤ C :=
  lift (fun x ↦ nerveEquiv (φ.app _ x)) (fun e ↦ nerve.homEquiv (e.map φ))
    (fun x ↦ by simpa using nerve.homEquiv_id (φ.app _ x))
      (fun h ↦ nerve.homEquiv_comp (h.map φ))

@[simp]
lemma descOfTruncation_obj_mk (φ : X ⟶ (truncation 2).obj (nerve C)) (x : X _⦋0⦌₂) :
    (descOfTruncation φ).obj (mk x) = nerveEquiv (φ.app _ x) := rfl

@[simp]
lemma descOfTruncation_map_homMk (φ : X ⟶ (truncation 2).obj (nerve C))
    {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) :
    (descOfTruncation φ).map (homMk e) = nerve.homEquiv (e.map φ) :=
  Category.id_comp _

lemma descOfTruncation_comp {X' : Truncated.{u} 2} (ψ : X ⟶ X')
    (φ : X' ⟶ (truncation 2).obj (nerve C)) :
    descOfTruncation (ψ ≫ φ) = mapHomotopyCategory ψ ⋙ descOfTruncation φ :=
  functor_ext (fun _ ↦ by simp) (by cat_disch)

/-- Given a `2`-truncated simplicial set `X` and a category `C`,
this is the morphism `X ⟶ (truncation 2).obj (nerve C)` corresponding
to a functor `X.HomotopyCategory ⥤ C`. -/
def homToNerveMk (F : X.HomotopyCategory ⥤ C) : X ⟶ (truncation 2).obj (nerve C) :=
  liftOfStrictSegal (fun x ↦ nerveEquiv.symm (F.obj (mk x)))
    (fun f ↦ ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f))))
    (fun f ↦ ComposableArrows.ext₀ rfl)
    (fun f ↦ ComposableArrows.ext₀ rfl)
    (fun x y h₂ h₀ ↦ by
      have h' {a b : X _⦋0⦌₂} (e : Edge a b) :
          ComposableArrows.mk₁ (F.map (homMk (Edge.mk' e.edge))) =
            ComposableArrows.mk₁ (F.map (homMk e)) :=
        ComposableArrows.arrowEquiv.injective
          (congr_arg F.mapArrow.obj (congr_arrowMk_homMk (Edge.mk' e.edge) e rfl))
      obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, h, rfl⟩ := Edge.CompStruct.exists_of_simplex x
      dsimp at h₀ h₂ ⊢
      have : ComposableArrows.mk₂ (F.map (homMk e₀₁)) (F.map (homMk e₁₂)) = y := by
        rw [h.d₂, h'] at h₂
        rw [h.d₀, h'] at h₀
        refine (spine_bijective (X := (truncation 2).obj (nerve C)) _ _).injective ?_
        ext i
        fin_cases i
        · dsimp
          simp only [SimplexCategory.mkOfSucc_zero_eq_δ, ← h₂]
          apply nerve.δ₂_mk₂_eq
        · dsimp
          simp only [SimplexCategory.mkOfSucc_one_eq_δ, ← h₀]
          apply nerve.δ₀_mk₂_eq
      rw [h.d₁, ← this]
      have := (nerve.δ₁_mk₂_eq (F.map (homMk e₀₁)) (F.map (homMk e₁₂))).symm
      rwa [← Functor.map_comp, homMk_comp_homMk h, ← h'] at this)
    (fun x ↦ ComposableArrows.arrowEquiv.injective
      ((congr_arg F.mapArrow.obj
        (congr_arrowMk_homMk (Edge.mk' (X.map (σ₂ 0).op x)) (Edge.id x) rfl)).trans (by aesop)))
    ((Nerve.strictSegal C).truncation 1)

@[simp]
lemma homToNerveMk_app_zero (F : X.HomotopyCategory ⥤ C) (x : X _⦋0⦌₂) :
    (homToNerveMk F).app _ x = nerveEquiv.symm (F.obj (mk x)) := rfl

lemma homToNerveMk_app_one (F : X.HomotopyCategory ⥤ C) (f : X _⦋1⦌₂) :
    (homToNerveMk F).app _ f =
      ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f))) :=
  rfl

@[simp]
lemma homToNerveMk_app_edge (F : X.HomotopyCategory ⥤ C) {x y : X _⦋0⦌₂} (e : Edge x y) :
    (homToNerveMk F).app _ e.edge =
      ComposableArrows.mk₁ (F.map (homMk e)) := by
  rw [homToNerveMk_app_one]
  exact ComposableArrows.arrowEquiv.injective
    (congr_arg F.mapArrow.obj (congr_arrowMk_homMk (Edge.mk' e.edge) e rfl))

set_option backward.isDefEq.respectTransparency false in
/-- Given a `2`-truncated simplicial set `X` and a category `C`,
this is the bijection between morphism `X.HomotopyCategory ⥤ C`
and `X ⟶ (truncation 2).obj (nerve C)` which is part of the adjunction
`SSet.Truncated.nerve₂Adj`. -/
def functorEquiv :
    (X.HomotopyCategory ⥤ C) ≃ (X ⟶ (truncation 2).obj (nerve C)) where
  toFun := homToNerveMk
  invFun := descOfTruncation
  left_inv F :=
    functor_ext (fun x ↦ by simp) (fun x y f ↦ by
      dsimp
      simp only [Category.comp_id, Category.id_comp, descOfTruncation_map_homMk,
        homToNerveMk_app_zero]
      exact nerve.homEquiv.symm.injective (Edge.ext (by cat_disch)))
  right_inv φ :=
    IsStrictSegal.hom_ext (fun s ↦ by
      obtain ⟨x₀, x₁, f, rfl⟩ := Edge.exists_of_simplex s
      dsimp [nerve.homEquiv]
      simp only [homToNerveMk_app_edge, descOfTruncation_obj_mk,
        descOfTruncation_map_homMk]
      refine ComposableArrows.ext₁ ?_ ?_ rfl
      · dsimp [nerveEquiv, ComposableArrows.right]
        simp only [← f.src_eq, NatTrans.naturality_apply]
        rfl
      · dsimp [nerveEquiv, ComposableArrows.right]
        simp only [← f.tgt_eq, NatTrans.naturality_apply]
        rfl)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma homToNerveMk_comp {D : Type u} [SmallCategory D]
    (F : X.HomotopyCategory ⥤ C) (G : C ⥤ D) :
    homToNerveMk (F ⋙ G) = homToNerveMk F ≫ (truncation 2).map (nerveMap G) :=
  IsStrictSegal.hom_ext (fun s ↦ by
    obtain ⟨x₀, x₁, f, rfl⟩ := Edge.exists_of_simplex s
    dsimp
    simp only [homToNerveMk_app_edge, Functor.comp_obj, Functor.comp_map]
    exact ComposableArrows.ext₁ rfl rfl (by aesop))

end HomotopyCategory

/-- The adjunction between the 2-truncated homotopy category functor
and the 2-truncated nerve functor. -/
def nerve₂Adj : hoFunctor₂.{u} ⊣ nerveFunctor₂ :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (Cat.Hom.equivFunctor _ _).trans HomotopyCategory.functorEquiv
      homEquiv_naturality_left_symm _ _ := by ext1; exact HomotopyCategory.descOfTruncation_comp _ _
      homEquiv_naturality_right _ _ := HomotopyCategory.homToNerveMk_comp _ _ }

end Truncated

end SSet

namespace CategoryTheory

namespace nerve

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- The functor `C ⥤ D` that is reconstructed for a morphism
between the `2`-truncated nerves. -/
@[simps]
def functorOfNerveMap (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D)) :
    C ⥤ D where
  obj x := nerveEquiv (φ.app (op ⟨⦋0⦌, by simp⟩) (nerveEquiv.symm x))
  map f := nerve.homEquiv ((nerve.edgeMk f).toTruncated.map φ)
  map_id x := by
    rw [edgeMk_id, SSet.Edge.toTruncated_id, SSet.Truncated.Edge.map_id]
    exact nerve.homEquiv_id _
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact (nerve.homEquiv_comp (h.toTruncated.map φ)).symm

lemma nerveFunctor₂_map_functorOfNerveMap
    (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D)) :
    nerveFunctor₂.map (functorOfNerveMap φ).toCatHom = φ :=
  SSet.Truncated.IsStrictSegal.hom_ext (fun f ↦ by
    obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective f
    exact (nerveMap_app_mk₁ _ _).trans ((nerve.mk₁_homEquiv_apply _).trans
      (ComposableArrows.mk₁_hom _)))

lemma functorOfNerveMap_nerveFunctor₂_map (F : C ⥤ D) :
    functorOfNerveMap ((SSet.truncation 2).map (nerveMap F)) = F :=
  Functor.ext (fun x ↦ by cat_disch) (fun x y f ↦ by cat_disch)

/-- The `2`-truncated nerve functor is fully faithful. -/
def fullyFaithfulNerveFunctor₂ : nerveFunctor₂.{u, u}.FullyFaithful where
  preimage φ := (functorOfNerveMap φ).toCatHom
  map_preimage _ := nerveFunctor₂_map_functorOfNerveMap _
  preimage_map _ := by ext1; exact functorOfNerveMap_nerveFunctor₂_map _

instance : nerveFunctor₂.{u, u}.Faithful :=
  (fullyFaithfulNerveFunctor₂).faithful

instance : nerveFunctor₂.{u, u}.Full :=
  (fullyFaithfulNerveFunctor₂).full

instance : Reflective nerveFunctor₂.{u, u} := Reflective.mk _ SSet.Truncated.nerve₂Adj

end nerve

open SSet

/-- The adjunction between the nerve functor and the homotopy category functor is, up to
isomorphism, the composite of the adjunctions `SSet.coskAdj 2` and `nerve₂Adj`. -/
noncomputable def nerveAdjunction : hoFunctor ⊣ nerveFunctor :=
  Adjunction.ofNatIsoRight ((SSet.coskAdj 2).comp Truncated.nerve₂Adj) Nerve.cosk₂Iso.symm


/-- Repleteness exists for full and faithful functors but not fully faithful functors, which is
why we do this inefficiently. -/
instance nerveFunctor.faithful : nerveFunctor.{u, u}.Faithful :=
  Functor.Faithful.of_iso Nerve.cosk₂Iso.symm

instance nerveFunctor.full : nerveFunctor.{u, u}.Full :=
  Functor.Full.of_iso Nerve.cosk₂Iso.symm

/-- The nerve functor is both full and faithful and thus is fully faithful. -/
noncomputable def nerveFunctor.fullyfaithful : nerveFunctor.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

instance nerveAdjunction.isIso_counit : IsIso nerveAdjunction.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- The counit map of `nerveAdjunction` is an isomorphism since the nerve functor is fully
faithful. -/
noncomputable def nerveFunctorCompHoFunctorIso : nerveFunctor.{u, u} ⋙ hoFunctor ≅ 𝟭 Cat :=
  asIso (nerveAdjunction.counit)

noncomputable instance : Reflective nerveFunctor where
  L := hoFunctor
  adj := nerveAdjunction

section

instance (C D : Type u) [Category.{u} C] [Category.{u} D] :
    IsIso (prodComparison (nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor)
      (Cat.of C) (Cat.of D)) := by
  let iso : nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor ≅ nerveFunctor :=
    (nerveFunctor.associator hoFunctor nerveFunctor).symm ≪≫
      Functor.isoWhiskerRight nerveFunctorCompHoFunctorIso nerveFunctor ≪≫
        nerveFunctor.leftUnitor
  exact IsIso.of_isIso_fac_right (prodComparison_natural_of_natTrans iso.hom).symm

namespace hoFunctor

instance : hoFunctor.IsLeftAdjoint := nerveAdjunction.isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
instance (C D : Type u) [Category.{u} C] [Category.{u} D] :
    IsIso (prodComparison hoFunctor (nerve C) (nerve D)) := by
  have : IsIso (nerveFunctor.map (prodComparison hoFunctor (nerve C) (nerve D))) := by
    have : IsIso (prodComparison (hoFunctor ⋙ nerveFunctor) (nerve C) (nerve D)) :=
      IsIso.of_isIso_fac_left
        (prodComparison_comp nerveFunctor (hoFunctor ⋙ nerveFunctor)
          (A := Cat.of C) (B := Cat.of D)).symm
    exact IsIso.of_isIso_fac_right (prodComparison_comp hoFunctor nerveFunctor).symm
  exact isIso_of_fully_faithful nerveFunctor _

instance isIso_prodComparison_stdSimplex.{w} (n m : ℕ) :
    IsIso (prodComparison hoFunctor (Δ[n] : SSet.{w}) Δ[m]) :=
  IsIso.of_isIso_fac_right (prodComparison_natural
    hoFunctor (stdSimplex.isoNerve n).hom (stdSimplex.isoNerve m).hom).symm

set_option backward.isDefEq.respectTransparency false in
lemma isIso_prodComparison_of_stdSimplex {D : SSet.{u}} (X : SSet.{u})
    (H : ∀ m, IsIso (prodComparison hoFunctor D Δ[m])) :
    IsIso (prodComparison hoFunctor D X) := by
  have : IsIso (Functor.whiskerLeft (CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda)
      (prodComparisonNatTrans hoFunctor.{u} D)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun x ↦ H (x.left).len
  exact isIso_app_coconePt_of_preservesColimit _ (prodComparisonNatTrans hoFunctor _) _
    (Presheaf.isColimitTautologicalCocone' X)

set_option backward.isDefEq.respectTransparency false in
instance isIso_prodComparison (X Y : SSet) :
    IsIso (prodComparison hoFunctor X Y) := isIso_prodComparison_of_stdSimplex _ fun m ↦ by
  convert_to IsIso (hoFunctor.map (prod.braiding _ _).hom ≫
    prodComparison hoFunctor Δ[m] X ≫ (prod.braiding _ _).hom)
  · ext <;> simp [← Functor.map_comp]
  suffices IsIso (prodComparison hoFunctor Δ[m] X) by infer_instance
  exact isIso_prodComparison_of_stdSimplex _ (isIso_prodComparison_stdSimplex _)

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of simplicial sets `X` and
`Y`. -/
instance preservesBinaryProduct (X Y : SSet) :
    PreservesLimit (pair X Y) hoFunctor :=
  PreservesLimitPair.of_iso_prod_comparison hoFunctor X Y

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves limits of functors out of
`Discrete WalkingPair`. -/
instance preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) hoFunctor where
  preservesLimit {F} := preservesLimit_of_iso_diagram hoFunctor (diagramIsoPair F).symm

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves finite products of simplicial sets. -/
instance preservesFiniteProducts : PreservesFiniteProducts hoFunctor :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

end hoFunctor

end

end CategoryTheory
