/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# ...

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial
  HomotopicalAlgebra

namespace CategoryTheory

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]

namespace Functor.PushoutObjObj

section

variable {F G : C₁ ⥤ C₂ ⥤ C₃} {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
  (sq : F.PushoutObjObj f₁ f₂) (e : F ≅ G)

@[simps]
def ofNatIso : G.PushoutObjObj f₁ f₂ where
  pt := sq.pt
  inl := (e.inv.app Y₁).app X₂ ≫ sq.inl
  inr := (e.inv.app X₁).app Y₂ ≫ sq.inr
  isPushout :=
    sq.isPushout.of_iso ((e.app _).app _) ((e.app _).app _) ((e.app _).app _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma ofNatIso_ι :
    (sq.ofNatIso e).ι = sq.ι ≫ (e.hom.app _).app _ := by
  apply sq.hom_ext
  · simp [← (sq.ofNatIso e).inl_ι]
  · simp [← (sq.ofNatIso e).inr_ι]

end

section

variable [MonoidalCategory C₁] [BraidedCategory C₁]
  {X₁ Y₁ X₂ Y₂ : C₁} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
  (sq : (curriedTensor C₁).PushoutObjObj f₁ f₂)

@[simps!]
def flipTensor : (curriedTensor C₁).PushoutObjObj f₂ f₁ :=
  sq.flip.ofNatIso (BraidedCategory.curriedBraidingNatIso _).symm

@[simp]
lemma flipTensor_ι : dsimp% sq.flipTensor.ι = sq.ι ≫ (β_ _ _).inv := by
  simp [flipTensor]

end

end Functor.PushoutObjObj

end CategoryTheory

namespace SSet

namespace Subcomplex

section

variable {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)

@[simps]
def pushoutObjObj : (curriedTensor _).PushoutObjObj A.ι B.ι where
  pt := A.unionProd B
  inl := (A.unionProd B).lift (_ ◁ B.ι) (sorry)
  inr := (A.unionProd B).lift (A.ι ▷ _) (sorry)
  isPushout := by
    sorry

lemma pushoutObjObj_ι : (pushoutObjObj A B).ι = (A.unionProd B).ι := by
  apply (pushoutObjObj A B).hom_ext
  · rw [(A.pushoutObjObj B).inl_ι]
    simp
  · rw [(A.pushoutObjObj B).inr_ι]
    simp

end

end Subcomplex

open modelCategoryQuillen

lemma rlp_monomorphisms :
    (MorphismProperty.monomorphisms SSet.{u}).rlp = I.rlp := by
  sorry

namespace prodStdSimplex

noncomputable def pairing {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).Pairing :=
  sorry

instance {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    (pairing.{u} k n).IsRegular :=
  sorry

lemma strongAnodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    strongAnodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι :=
  (pairing k n).strongAnodyneExtensions

lemma anodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    anodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι :=
  (pairing k n).anodyneExtensions

end prodStdSimplex

variable {X₁ X₂ Y₁ Y₂ E B : SSet.{u}}
  {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂} {p : E ⟶ B}

lemma fibration_pullbackObjObjπ [Mono i] [Fibration p]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    Fibration sq₁₃.π := by
  rw [fibration_iff]
  intro _ _ _ h
  simp only [J, MorphismProperty.iSup_iff] at h
  obtain ⟨m, ⟨k⟩⟩ := h
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[m + 1, k].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  suffices anodyneExtensions sq₁₂.ι from
    this _ (by rwa [← HomotopicalAlgebra.fibration_iff])
  intro E B p hp
  rw [HasLiftingProperty.iff_of_arrow_iso_left
    (show Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι from
      Arrow.isoMk (Iso.refl _) (β_ _ _))]
  let sq₁₃' := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom Λ[m + 1, k].ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃']
  suffices (MorphismProperty.monomorphisms _).rlp sq₁₃'.π from this _ inferInstance
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff (Subcomplex.pushoutObjObj _ _),
    Subcomplex.pushoutObjObj_ι]
  exact prodStdSimplex.anodyneExtensions_unionProd_ι _ _ _ hp

lemma anodyneExtensions_pushoutObjObjι
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : anodyneExtensions j) :
    anodyneExtensions sq₁₂.ι := by
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  apply hj
  rw [← HomotopicalAlgebra.fibration_iff] at hp ⊢
  exact fibration_pullbackObjObjπ sq₁₃

lemma anodyneExtensions_pushoutObjObjι'
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j)
    [Mono j] (hi : anodyneExtensions i) :
    anodyneExtensions sq₁₂.ι := by
  refine (anodyneExtensions.arrow_mk_iso_iff ?_).1
    (anodyneExtensions_pushoutObjObjι sq₁₂.flipTensor hi)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

end SSet
