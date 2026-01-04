/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.ArrowSeven
public import Mathlib.CategoryTheory.ComposableArrows.One
public import Mathlib.CategoryTheory.ComposableArrows.Two
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Spectral objects...

-/

@[expose] public section

open CategoryTheory Category Limits Preadditive

namespace CategoryTheory

namespace Limits

open Functor

variable {C ι ι' J : Type _} [Category C] [Category ι] [Category ι'] [Category J]
  (F : ι' ⥤ ι)

-- this should be moved to `Limits.FunctorCategory`
noncomputable instance [HasFiniteLimits C] (i : ι) :
  PreservesFiniteLimits ((evaluation ι C).obj i) := ⟨fun _ => inferInstance⟩

noncomputable instance [HasFiniteColimits C] (i : ι) :
  PreservesFiniteColimits ((evaluation ι C).obj i) := ⟨fun _ => inferInstance⟩

instance [HasZeroMorphisms C] :
    ((whiskeringLeft ι' ι C).obj F).PreservesZeroMorphisms where

noncomputable instance [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J ((whiskeringLeft ι' ι C).obj F) :=
    ⟨fun {_} => ⟨fun hc => ⟨evaluationJointlyReflectsLimits _
      (fun i => isLimitOfPreserves ((evaluation ι C).obj (F.obj i)) hc)⟩⟩⟩

noncomputable instance [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J ((whiskeringLeft ι' ι C).obj F) :=
    ⟨fun {_} => ⟨fun hc => ⟨evaluationJointlyReflectsColimits _
      (fun i => isColimitOfPreserves ((evaluation ι C).obj (F.obj i)) hc)⟩⟩⟩

noncomputable instance [HasFiniteLimits C] :
    PreservesFiniteLimits ((whiskeringLeft ι' ι C).obj F) :=
  ⟨fun _ => by infer_instance⟩

noncomputable instance [HasFiniteColimits C] :
    PreservesFiniteColimits ((whiskeringLeft ι' ι C).obj F) :=
  ⟨fun _ => by infer_instance⟩

instance [HasFiniteColimits C] {X Y : ι ⥤ C} (τ : X ⟶ Y) [Epi τ] :
    Epi (whiskerLeft F τ) := ((whiskeringLeft ι' ι C).obj F).map_epi τ

instance [HasFiniteLimits C] {X Y : ι ⥤ C} (τ : X ⟶ Y) [Mono τ] :
  Mono (whiskerLeft F τ) := ((whiskeringLeft ι' ι C).obj F).map_mono τ

instance [HasFiniteColimits C] {X Y : ι ⥤ C} (τ : X ⟶ Y) [Epi τ] (i : ι) :
    Epi (τ.app i) :=
  ((evaluation ι C).obj i).map_epi τ

instance [HasFiniteLimits C] {X Y : ι ⥤ C} (τ : X ⟶ Y) [Mono τ] (i : ι) :
    Mono (τ.app i) :=
  ((evaluation ι C).obj i).map_mono τ

end Limits

namespace ShortComplex

variable {C ι : Type _} [Category C] [Category ι] [Abelian C]
variable (S : ShortComplex (ι ⥤ C))

noncomputable def evaluationHomologyIso (a : ι) :
    (S.map ((evaluation _ _).obj a)).homology ≅ S.homology.obj a :=
  S.mapHomologyIso ((evaluation _ _).obj a)

lemma homology_map {a b : ι} (φ : a ⟶ b) :
    S.homology.map φ =
  (S.evaluationHomologyIso a).inv ≫ homologyMap (S.mapNatTrans ((evaluation _ _).map φ)) ≫
    (S.evaluationHomologyIso b).hom :=
  NatTrans.app_homology ((evaluation _ _).map φ) S

noncomputable def homologyMapMapNatTransEvaluationMapArrowIso {a b : ι} (φ : a ⟶ b) :
  Arrow.mk (homologyMap (S.mapNatTrans ((evaluation _ _).map φ))) ≅
    Arrow.mk (S.homology.map φ) := by
  refine Arrow.isoMk (S.evaluationHomologyIso a) (S.evaluationHomologyIso b) ?_
  dsimp
  rw [homology_map, Iso.hom_inv_id_assoc]

lemma mono_homology_map_iff {a b : ι} (φ : a ⟶ b) :
    Mono (S.homology.map φ) ↔ Mono (homologyMap (S.mapNatTrans ((evaluation _ _).map φ))) :=
  (MorphismProperty.monomorphisms C).arrow_mk_iso_iff
    (S.homologyMapMapNatTransEvaluationMapArrowIso φ).symm

lemma epi_homology_map_iff {a b : ι} (φ : a ⟶ b) :
    Epi (S.homology.map φ) ↔ Epi (homologyMap (S.mapNatTrans ((evaluation _ _).map φ))) :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (S.homologyMapMapNatTransEvaluationMapArrowIso φ).symm

lemma isIso_homology_map_iff {a b : ι} (φ : a ⟶ b) :
    IsIso (S.homology.map φ) ↔ IsIso (homologyMap (S.mapNatTrans ((evaluation _ _).map φ))) :=
  (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (S.homologyMapMapNatTransEvaluationMapArrowIso φ).symm

end ShortComplex

end CategoryTheory

namespace Monotone

@[simps]
def natTrans {X Y : Type*} [Preorder X] [Preorder Y] {f g : X → Y} (hf : Monotone f)
    (hg : Monotone g) (h : ∀ x, f x ≤ g x) :
    Monotone.functor hf ⟶ Monotone.functor hg where
  app x := homOfLE (h x)

end Monotone

namespace SimplexCategory

@[simps!]
def natTransToCatMapOfLE {Δ Δ' : SimplexCategory} (f g : Δ ⟶ Δ')
    (h : ∀ x, f.toOrderHom x ≤ g.toOrderHom x) :
    SimplexCategory.toCat.map f ⟶ SimplexCategory.toCat.map g :=
  .ofNatTrans (Monotone.natTrans f.toOrderHom.monotone g.toOrderHom.monotone h)

end SimplexCategory

namespace CategoryTheory

open Functor

namespace ComposableArrows

variable (C : Type*) [Category C]

@[simps!]
def whiskerLeftNatTrans {n m : ℕ} {Φ Ψ : Fin (n + 1) ⥤ Fin (m + 1)} (α : Φ ⟶ Ψ) :
    (whiskerLeftFunctor Φ : ComposableArrows C _ ⥤ _) ⟶ whiskerLeftFunctor Ψ where
  app S := ((whiskeringLeft (Fin (n + 1)) (Fin (m + 1)) C).map α).app S

def functorδ {n : ℕ} (i : Fin (n + 2)) :
    ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  whiskerLeftFunctor (SimplexCategory.toCat.map (SimplexCategory.δ i)).toFunctor

variable {C}

abbrev δ {n : ℕ} (S : ComposableArrows C (n + 1)) (i : Fin (n + 2)) :
    ComposableArrows C n :=
  (functorδ C i).obj S

variable (C)

def natTransδ {n : ℕ} (i j : Fin (n + 2)) (hij : i.1 ≤ j.1) :
    functorδ C j ⟶ functorδ C i :=
  whiskerLeftNatTrans C (SimplexCategory.natTransToCatMapOfLE _ _ (by
    intro x
    dsimp [SimplexCategory.δ, Fin.succAbove, Fin.succ,
      Fin.castSucc, Fin.castAdd, Fin.castLE]
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    obtain ⟨x, hx⟩ := x
    simp only at hij
    simp only [Fin.mk_lt_mk]
    split_ifs with h₁ h₂ <;> simp only [Fin.mk_le_mk] <;> lia)).toNatTrans

variable {C}

abbrev mapδ {n : ℕ} (S : ComposableArrows C (n + 1)) (i j : Fin (n + 2)) (hij : i.1 ≤ j.1) :
    S.δ j ⟶ S.δ i :=
  (natTransδ C i j hij).app S

variable {D : Type*} [Category D] {n : ℕ} (S : ComposableArrows C n) (F : C ⥤ D)

@[simps!]
def apply : ComposableArrows D n := S ⋙ F

end ComposableArrows

variable {C ι : Type _} [Category C] [Abelian C] [Category ι]

lemma ShortComplex.exact_iff_exact_evaluation (S : ShortComplex (ι ⥤ C)) :
    S.Exact ↔ ∀ (i : ι), (S.map ((evaluation ι C).obj i)).Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology,
    fun i => Iso.isZero_iff (S.mapHomologyIso ((evaluation ι C).obj i)),
    evaluation_obj_obj, Functor.isZero_iff]

lemma ComposableArrows.isComplex_iff_isComplex_evaluation
    {n : ℕ} (S : ComposableArrows (ι ⥤ C) n) :
    S.IsComplex ↔ ∀ (i : ι), (S.apply ((evaluation ι C).obj i)).IsComplex := by
  constructor
  · intro hS i
    constructor
    intro k hk
    exact ((evaluation ι C).obj i).congr_map (hS.zero k)
  · intro hS
    constructor
    intro k hk
    ext i
    exact (hS i).zero k

lemma ComposableArrows.exact_iff_exact_evaluation
    {n : ℕ} (S : ComposableArrows (ι ⥤ C) n) :
    S.Exact ↔ ∀ (i : ι), (S.apply ((evaluation ι C).obj i)).Exact := by
  constructor
  · intro hS i
    exact
      { toIsComplex := S.isComplex_iff_isComplex_evaluation.1 hS.toIsComplex i
        exact := fun k hk =>
          (hS.sc k).exact_iff_exact_evaluation.1 (hS.exact k) i }
  · intro hS
    exact
      { toIsComplex := S.isComplex_iff_isComplex_evaluation.2
          (fun i => (hS i).toIsComplex)
        exact := fun k hk => by
          rw [ShortComplex.exact_iff_exact_evaluation]
          intro i
          exact (hS i).exact k }

namespace ComposableArrows

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)

def threeδ₃Toδ₂ :
    mk₂ f₁ f₂ ⟶ mk₂ f₁ f₂₃ :=
  homMk₂ (𝟙 _) (𝟙 _) f₃ (by simp) (by simpa using h₂₃)

@[simp]
lemma threeδ₃Toδ₂_app_zero :
    (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 0 = 𝟙 _ := rfl

@[simp]
lemma threeδ₃Toδ₂_app_one :
    (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 1 = 𝟙 _ := rfl

@[simp]
lemma threeδ₃Toδ₂_app_two :
    (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 2 = f₃ := rfl

def threeδ₂Toδ₁ :
    mk₂ f₁ f₂₃ ⟶ mk₂ f₁₂ f₃ :=
  homMk₂ (𝟙 _) f₂ (𝟙 _) (by simpa using h₁₂) (by simpa using h₂₃.symm)

@[simp]
lemma threeδ₂Toδ₁_app_zero :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃).app 0 = 𝟙 _ := rfl

@[simp]
lemma threeδ₂Toδ₁_app_one :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃).app 1 = f₂ := rfl

@[simp]
lemma threeδ₂Toδ₁_app_two :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃).app 2 = 𝟙 _ := rfl

/-- Variant of `threeδ₂Toδ₁_app_two`. -/
@[simp]
lemma threeδ₂Toδ₁_app_two' :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃).app ⟨2, by lia⟩ = 𝟙 _ := rfl

def threeδ₁Toδ₀ :
    mk₂ f₁₂ f₃ ⟶ mk₂ f₂ f₃ :=
  homMk₂ f₁ (𝟙 _) (𝟙 _) (by simpa using h₁₂.symm) (by simp; rfl)

@[simp]
lemma threeδ₁Toδ₀_app_zero :
    (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 0 = f₁ := rfl

@[simp]
lemma threeδ₁Toδ₀_app_one :
    (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 1 = (𝟙 _) := rfl

@[simp]
lemma threeδ₁Toδ₀_app_two :
    (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 2 = (𝟙 _) := rfl

end

section

variable {i₀ i₁ i₂ i₃ i₄ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)

def fourδ₄Toδ₃ :
    mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃₄ :=
  homMk₃ (𝟙 _) (𝟙 _) (𝟙 _) f₄ (by simp) (by simp; rfl) (by simpa using h₃₄)

@[simp]
lemma fourδ₄Toδ₃_app_zero :
    (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 0 = 𝟙 _ := rfl

@[simp]
lemma fourδ₄Toδ₃_app_one :
    (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 1 = 𝟙 _ := rfl

@[simp]
lemma fourδ₄Toδ₃_app_two :
    (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 2 = 𝟙 _ := rfl

@[simp]
lemma fourδ₄Toδ₃_app_three :
    (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 3 = f₄ := rfl

def fourδ₂Toδ₁ :
    mk₃ f₁ f₂₃ f₄ ⟶ mk₃ f₁₂ f₃ f₄ :=
  homMk₃ (𝟙 _) f₂ (𝟙 _) (𝟙 _) (by simpa using h₁₂) (by simpa using h₂₃.symm) (by simp; rfl)

@[simp]
lemma fourδ₂Toδ₁_app_zero :
    (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ h₁₂ f₂₃ h₂₃).app 0 = 𝟙 _ := rfl

@[simp]
lemma fourδ₂Toδ₁_app_one :
    (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ h₁₂ f₂₃ h₂₃).app 1 = f₂ := rfl

@[simp]
lemma fourδ₂Toδ₁_app_two :
    (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ h₁₂ f₂₃ h₂₃).app 2 = 𝟙 _ := rfl

/-- Variant of `fourδ₂Toδ₁_app_two`. -/
@[simp]
lemma fourδ₂Toδ₁_app_two' :
    (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ h₁₂ f₂₃ h₂₃).app ⟨2, by lia⟩ = 𝟙 _ := rfl

@[simp]
lemma fourδ₂Toδ₁_app_three :
    (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ h₁₂ f₂₃ h₂₃).app 3 = 𝟙 _ := rfl

def fourδ₁Toδ₀ :
    mk₃ f₁₂ f₃ f₄ ⟶ mk₃ f₂ f₃ f₄ :=
  homMk₃ f₁ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using h₁₂.symm) (by simp; rfl) (by simp; rfl)

@[simp]
lemma fourδ₁Toδ₀_app_zero :
    (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 0 = f₁ := rfl

@[simp]
lemma fourδ₁Toδ₀_app_one :
    (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 1 = 𝟙 _ := rfl

@[simp]
lemma fourδ₁Toδ₀_app_two :
    (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 2 = 𝟙 _ := rfl

@[simp]
lemma fourδ₁Toδ₀_app_three :
    (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 3 = 𝟙 _ := rfl

end

section

omit [Abelian C]

lemma isIso_iff₀ {S₁ S₂ : ComposableArrows C 0} (f : S₁ ⟶ S₂) :
    IsIso f ↔ IsIso (f.app 0) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h ↦ h 0, fun _ i ↦ by fin_cases i; assumption⟩

lemma isIso_iff₁ {S₁ S₂ : ComposableArrows C 1} (f : S₁ ⟶ S₂) :
    IsIso f ↔ IsIso (f.app 0) ∧ IsIso (f.app 1) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h ↦ ⟨h 0, h 1⟩, fun _ i ↦ by fin_cases i <;> tauto⟩

lemma isIso_iff₂ {S₁ S₂ : ComposableArrows C 2} (f : S₁ ⟶ S₂) :
    IsIso f ↔ IsIso (f.app 0) ∧ IsIso (f.app 1) ∧ IsIso (f.app 2) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun _ i ↦ by fin_cases i <;> tauto⟩

end

end ComposableArrows

end CategoryTheory
