/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Anodyne extensions and pushout-products, fibrations and pullbacks

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial
  HomotopicalAlgebra Limits Opposite

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

variable (F : C₁ ⥤ C₂ ⥤ C₃) {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  [PreservesColimitsOfShape (Discrete PEmpty.{1}) (F.obj X₁)]
  [PreservesColimitsOfShape (Discrete PEmpty.{1}) (F.obj Y₁)]
  (h : IsInitial X₂)

@[simps]
noncomputable def ofIsInitialRight : F.PushoutObjObj f₁ f₂ where
  pt := (F.obj X₁).obj Y₂
  inl := (IsInitial.isInitialObj (F.obj _) _ h).to _
  inr := 𝟙 _
  isPushout := by
    let hX₁ := IsInitial.isInitialObj (F.obj X₁) _ h
    let hY₁ := IsInitial.isInitialObj (F.obj Y₁) _ h
    apply +allowSynthFailures IsPushout.of_horiz_isIso
    · exact isIso_of_isInitial hX₁ hY₁ _
    · exact ⟨hX₁.hom_ext _ _⟩


@[simp]
lemma ofIsInitialRight_ι : (ofIsInitialRight F f₁ f₂ h).ι = (F.map f₁).app Y₂ := by
  simpa using (ofIsInitialRight F f₁ f₂ h).inr_ι

end

section

variable (F : C₁ ⥤ C₂ ⥤ C₃) {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  [PreservesColimitsOfShape (Discrete PEmpty.{1}) (F.flip.obj X₂)]
  [PreservesColimitsOfShape (Discrete PEmpty.{1}) (F.flip.obj Y₂)]
  (h : IsInitial X₁)

@[simps]
noncomputable def ofIsInitialLeft : F.PushoutObjObj f₁ f₂ where
  pt := (F.obj Y₁).obj X₂
  inl := 𝟙 _
  inr := (IsInitial.isInitialObj (F.flip.obj _) _ h).to _
  isPushout := by
    let hX₂ := IsInitial.isInitialObj (F.flip.obj X₂) _ h
    let hY₂ := IsInitial.isInitialObj (F.flip.obj Y₂) _ h
    apply +allowSynthFailures IsPushout.of_vert_isIso
    · exact isIso_of_isInitial hX₂ hY₂ _
    · exact ⟨hX₂.hom_ext _ _⟩

@[simp]
lemma ofIsInitialLeft_ι : (ofIsInitialLeft F f₁ f₂ h).ι = (F.obj Y₁).map f₂ := by
  simpa using (ofIsInitialLeft F f₁ f₂ h).inl_ι

end

section

variable [MonoidalCategory C₁]
  {X₁ Y₁ X₂ Y₂ : C₁} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

section

variable {f₁ f₂} [BraidedCategory C₁] {X₁ Y₁ X₂ Y₂ : C₁} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
  (sq : (curriedTensor C₁).PushoutObjObj f₁ f₂)

@[simps!]
def flipTensor : (curriedTensor C₁).PushoutObjObj f₂ f₁ :=
  sq.flip.ofNatIso (BraidedCategory.curriedBraidingNatIso _).symm

@[simp]
lemma flipTensor_ι : dsimp% sq.flipTensor.ι = sq.ι ≫ (β_ _ _).inv := by
  simp [flipTensor]

end

end

end Functor.PushoutObjObj

namespace Functor.PullbackObjObj

variable (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂) {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₃ Y₃ : C₃} (f₃ : X₃ ⟶ Y₃)

section

variable (h : IsInitial X₁)
  [PreservesLimitsOfShape (Discrete PEmpty.{1}) (G.flip.obj X₃)]
  [PreservesLimitsOfShape (Discrete PEmpty.{1}) (G.flip.obj Y₃)]

@[simps]
noncomputable def ofIsInitial : G.PullbackObjObj f₁ f₃ where
  pt := (G.obj (op Y₁)).obj Y₃
  fst := (IsTerminal.isTerminalObj (G.flip.obj X₃) _ h.op).from _
  snd := 𝟙 _
  isPullback := by
    let hX₃ := IsTerminal.isTerminalObj (G.flip.obj X₃) _ h.op
    let hY₃ := IsTerminal.isTerminalObj (G.flip.obj Y₃) _ h.op
    apply +allowSynthFailures IsPullback.of_vert_isIso
    · exact isIso_of_isTerminal hX₃ hY₃ _
    · exact ⟨hY₃.hom_ext _ _⟩

@[simp]
lemma ofIsInitial_π : (ofIsInitial G f₁ f₃ h).π = (G.obj (op Y₁)).map f₃ := by
  simpa using (ofIsInitial G f₁ f₃ h).π_snd

end

section

variable (h : IsTerminal Y₃)
  [PreservesLimitsOfShape (Discrete PEmpty.{1}) (G.obj (op X₁))]
  [PreservesLimitsOfShape (Discrete PEmpty.{1}) (G.obj (op Y₁))]

@[simps]
noncomputable def ofIsTerminal : G.PullbackObjObj f₁ f₃ where
  pt := (G.obj (op X₁)).obj X₃
  fst := 𝟙 _
  snd := (IsTerminal.isTerminalObj (G.obj _) _ h).from _
  isPullback := by
    let hX₁ := IsTerminal.isTerminalObj (G.obj (op X₁)) _ h
    let hY₁ := IsTerminal.isTerminalObj (G.obj (op Y₁)) _ h
    apply +allowSynthFailures IsPullback.of_horiz_isIso
    · exact isIso_of_isTerminal hY₁ hX₁ _
    · exact ⟨hX₁.hom_ext _ _⟩

@[simp]
lemma ofIsTerminal_π : (ofIsTerminal G f₁ f₃ h).π = (G.map f₁.op).app X₃ := by
  simpa using (ofIsTerminal G f₁ f₃ h).π_fst

end

end Functor.PullbackObjObj

end CategoryTheory

namespace SSet

open modelCategoryQuillen

namespace prodStdSimplex

-- this will be done in #39298
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

section

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
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff (Subcomplex.unionProd.pushoutObjObj _ _),
    Subcomplex.unionProd.pushoutObjObj_ι]
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

end

lemma anodyneExtensions_unionProd_ι
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hB : anodyneExtensions B.ι) :
    anodyneExtensions (A.unionProd B).ι := by
  simpa using anodyneExtensions_pushoutObjObjι (Subcomplex.unionProd.pushoutObjObj A B) hB

lemma anodyneExtensions_unionProd_ι'
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hA : anodyneExtensions A.ι) :
    anodyneExtensions (A.unionProd B).ι := by
  simpa using anodyneExtensions_pushoutObjObjι' (Subcomplex.unionProd.pushoutObjObj A B) hA

lemma anodyneExtensions.whiskerRight
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : anodyneExtensions f) (Z : SSet.{u}) :
    anodyneExtensions (f ▷ Z) := by
  simpa using anodyneExtensions_pushoutObjObjι'
    (.ofIsInitialRight (curriedTensor _) f (initial.to Z) initialIsInitial) hf

lemma anodyneExtensions.whiskerLeft
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : anodyneExtensions f) (Z : SSet.{u}) :
    anodyneExtensions (Z ◁ f) := by
  simpa using anodyneExtensions_pushoutObjObjι
    (.ofIsInitialLeft (curriedTensor _) (initial.to Z) f initialIsInitial) hf

instance {E B X : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration ((ihom X).map p) := by
  simpa using fibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
    MonoidalClosed.internalHom (initial.to X) p initialIsInitial)

instance {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (X : SSet.{u}) [IsFibrant X] :
    Fibration ((MonoidalClosed.pre i).app X) := by
  simpa using fibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsTerminal
    MonoidalClosed.internalHom i (terminal.from X) terminalIsTerminal)

instance (A : SSet.{u}) : IsFibrant ((ihom A).obj (⊤_ _)) := by
  have : IsIso (terminal.from ((ihom A).obj (⊤_ _))) :=
    isIso_of_isTerminal (IsTerminal.isTerminalObj _ _ terminalIsTerminal)
      terminalIsTerminal _
  rw [isFibrant_iff]
  infer_instance

instance {A X : SSet.{u}} [IsFibrant X] : IsFibrant ((ihom A).obj X) :=
  isFibrant_of_fibration ((ihom A).map (terminal.from X))

end SSet
