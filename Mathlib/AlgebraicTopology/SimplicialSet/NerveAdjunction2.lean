/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Presheaf

/-!

-/

universe u

open CategoryTheory Nerve Simplicial SimplicialObject.Truncated
  SimplexCategory.Truncated Opposite

namespace SSet

namespace Truncated

namespace Path
variable {n : ℕ} {X : Truncated.{u} (n + 1)} (p q : X.Path 1)
  (h : p.vertex 1 = q.vertex 0)

@[simps!]
def mk₂ : X.Path 2 where
  vertex := ![p.vertex 0, p.vertex 1, q.vertex 1]
  arrow := ![p.arrow 0, q.arrow 0]
  arrow_src i := by
    fin_cases i
    · exact p.arrow_src 0
    · exact (q.arrow_src 0).trans h.symm
  arrow_tgt i := by
    fin_cases i
    · exact p.arrow_tgt 0
    · exact q.arrow_tgt 0

end Path

section

variable {n : ℕ} {X Y : Truncated.{u} 2} (f₀ : X _⦋0⦌₂ → Y _⦋0⦌₂) (f₁ : X _⦋1⦌₂ → Y _⦋1⦌₂)
  (hδ₁ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₁ x))
  (hδ₀ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₁ x))
  (H : ∀ (x : X _⦋2⦌₂) (y : Y _⦋2⦌₂), f₁ (X.map (δ₂ 2).op x) = Y.map (δ₂ 2).op y →
    f₁ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op y →
      f₁ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op y)
  (hσ : ∀ (x : X _⦋0⦌₂), f₁ (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₀ x))
  (hY : Y.StrictSegal)


namespace liftOfIsStrictSegal

def f₂ (x : X _⦋2⦌₂) : Y _⦋2⦌₂ :=
  (hY.spineEquiv 2).symm
    (.mk₂ (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 2).op x)))
      (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 0).op x))) (by
        simp only [spine_vertex]
        rw [← δ₂_one_eq_const, ← δ₂_zero_eq_const, ← hδ₁, ← hδ₀]
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_δ₂_two]))

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
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero, op_comp,
      FunctorToTypes.map_comp_apply, hσ, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero,
      op_comp, FunctorToTypes.map_comp_apply, hδ₁]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_one_eq_δ,
      ← FunctorToTypes.map_comp_apply, ← op_comp]

include hσ in
lemma hσ'₁ (x : X _⦋1⦌₂) :
    f₂ f₀ f₁ hδ₁ hδ₀ hY (X.map (σ₂ 1).op x) = Y.map (σ₂ 1).op (f₁ x) := by
  have := hσ
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← FunctorToTypes.map_comp_apply, ← op_comp]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    dsimp [StrictSegal.spineEquiv]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one, op_comp,
      FunctorToTypes.map_comp_apply, hσ, SimplexCategory.mkOfSucc_one_eq_δ,
      ← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one,
      op_comp, FunctorToTypes.map_comp_apply, hδ₀]

def app (n : (SimplexCategory.Truncated 2)ᵒᵖ) : X.obj n ⟶ Y.obj n := by
  obtain ⟨n, hn⟩ := n
  induction n using SimplexCategory.rec with | _ n
  match n with
  | 0 => exact f₀
  | 1 => exact f₁
  | 2 => exact f₂ f₀ f₁ hδ₁ hδ₀ hY

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
    · omega
  · obtain _ | _ | n := n
    · fin_cases i
      ext; apply hσ
    · fin_cases i
      · ext; apply hσ'₀ f₀ f₁ hδ₁ hδ₀ hσ hY
      · ext; apply hσ'₁ f₀ f₁ hδ₁ hδ₀ hσ hY
    · omega

end liftOfIsStrictSegal

open liftOfIsStrictSegal in
def liftOfIsStrictSegal : X ⟶ Y where
  app := liftOfIsStrictSegal.app f₀ f₁ hδ₁ hδ₀ hY
  naturality _ _ φ :=
    (liftOfIsStrictSegal.naturalityProperty_eq_top f₀ f₁ hδ₁ hδ₀ H hσ hY).symm.le
      φ.unop (by simp)

@[simp]
lemma liftOfIsStrictSegal_app_0 :
    (liftOfIsStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (op ⦋0⦌₂) = f₀ := rfl

@[simp]
lemma liftOfIsStrictSegal_app_1 :
    (liftOfIsStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (op ⦋1⦌₂) = f₁ := rfl

end

namespace HomotopyCategory

variable {X : Truncated.{u} 2} {C D : Type u} [SmallCategory C] [SmallCategory D]

def descOfTruncation (φ : X ⟶ (truncation 2).obj (nerve C)) :
    X.HomotopyCategory ⥤ C :=
  lift (fun x ↦ nerveEquiv (φ.app _ x)) (fun e ↦ nerveHomEquiv (e.map φ))
    (fun x ↦ by simpa using nerveHomEquiv_id (φ.app _ x))
      (fun h ↦ nerveHomEquiv_comp (h.map φ))

@[simp]
lemma descOfTruncation_obj_mk (φ : X ⟶ (truncation 2).obj (nerve C)) (x : X _⦋0⦌₂) :
    (descOfTruncation φ).obj (mk x) = nerveEquiv (φ.app _ x) := rfl

@[simp]
lemma descOfTruncation_map_homMk (φ : X ⟶ (truncation 2).obj (nerve C))
    {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) :
    (descOfTruncation φ).map (homMk e) = nerveHomEquiv (e.map φ) :=
  Category.id_comp _

lemma descOfTruncation_comp {X' : Truncated.{u} 2} (ψ : X ⟶ X')
    (φ : X' ⟶ (truncation 2).obj (nerve C)) :
    descOfTruncation (ψ ≫ φ) = mapHomotopyCategory ψ ⋙ descOfTruncation φ :=
  functor_ext (fun _ ↦ by simp) (by cat_disch)

def homToNerveMk (F : X.HomotopyCategory ⥤ C) : X ⟶ (truncation 2).obj (nerve C) :=
  liftOfIsStrictSegal (fun x ↦ nerveEquiv.symm (F.obj (mk x)))
    (fun f ↦ ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f))))
    (fun f ↦ ComposableArrows.ext₀ rfl)
    (fun f ↦ ComposableArrows.ext₀ rfl)
    (fun x y h₂ h₁ ↦ by
      dsimp at h₁ h₂ ⊢
      have := Edge.CompStruct.exists_of_simplex x
      sorry)
    (fun x ↦ by
      refine (ComposableArrows.ext₁ ?_ ?_ ?_).trans
        (σ_zero_nerveEquiv_symm (F.obj (mk x))).symm
      · simp [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_zero]
      · simp [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_zero]
      · dsimp
        simp
        sorry)
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

def functorEquiv :
    (X.HomotopyCategory ⥤ C) ≃ (X ⟶ (truncation 2).obj (nerve C)) where
  toFun := homToNerveMk
  invFun := descOfTruncation
  left_inv F := by
    refine functor_ext (fun x ↦ by simp) (fun x y f ↦ ?_)
    · dsimp
      simp only [Category.comp_id, Category.id_comp, descOfTruncation_map_homMk,
        homToNerveMk_app_zero]
      exact nerveHomEquiv.symm.injective (Edge.ext (by cat_disch))
  right_inv φ := IsStrictSegal.hom_ext (fun s ↦ by
    obtain ⟨x₀, x₁, f, rfl⟩ := Edge.exists_of_simplex s
    dsimp [nerveHomEquiv]
    simp only [homToNerveMk_app_edge, descOfTruncation_obj_mk, nerve_obj,
      SimplexCategory.len_mk, descOfTruncation_map_homMk]
    refine ComposableArrows.ext₁ ?_ ?_ rfl
    · dsimp [nerveEquiv, ComposableArrows.right]
      simp only [← f.src_eq, FunctorToTypes.naturality]
      rfl
    · dsimp [nerveEquiv, ComposableArrows.right]
      simp only [← f.tgt_eq, FunctorToTypes.naturality]
      rfl)

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
and the 2-truncated nerve functor and the . -/
def nerve₂Adj : hoFunctor₂.{u} ⊣ nerveFunctor₂ :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := HomotopyCategory.functorEquiv
      homEquiv_naturality_left_symm _ _ := HomotopyCategory.descOfTruncation_comp _ _
      homEquiv_naturality_right _ _ := HomotopyCategory.homToNerveMk_comp _ _ }

end Truncated

end SSet

namespace CategoryTheory

namespace nerve

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

@[simps]
def functorOfNerveMap (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D)) :
    C ⥤ D where
  obj x := nerveEquiv (φ.app (op ⟨⦋0⦌, by simp⟩) (nerveEquiv.symm x))
  map f := nerveHomEquiv (SSet.Truncated.Edge.map (Edge.ofHom f) φ)
  map_id x := by
    simp
    have := nerveHomEquiv_id (φ.app (op ⟨⦋0⦌, by simp⟩) (nerveEquiv.symm x))
    sorry
  map_comp f g := by
    refine (nerveHomEquiv_comp ?_).symm
    sorry

lemma nerveFunctor₂_map_functorOfNerveMap
    (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D)) :
    nerveFunctor₂.map (functorOfNerveMap φ) = φ :=
  SSet.Truncated.IsStrictSegal.hom_ext (fun f ↦ by
    obtain ⟨x, y, f, rfl⟩ := SSet.Truncated.Edge.exists_of_simplex f
    dsimp
    refine ComposableArrows.ext₁ ?_ ?_ ?_
    · sorry
    · sorry
    · sorry)

lemma functorOfNerveMap_nerveFunctor₂_map (F : C ⥤ D) :
    functorOfNerveMap ((SSet.truncation 2).map (nerveMap F)) = F :=
  Functor.ext (fun x ↦ by cat_disch)
    (fun x y f ↦ by simpa using nerveHomEquiv_ofHom_map_nerveMap f F)

def fullyFaithfulNerveFunctor₂ : nerveFunctor₂.{u, u}.FullyFaithful where
  preimage φ := functorOfNerveMap φ
  map_preimage _ := nerveFunctor₂_map_functorOfNerveMap _
  preimage_map _ := functorOfNerveMap_nerveFunctor₂_map _

end nerve

end CategoryTheory
