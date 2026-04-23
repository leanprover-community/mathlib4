/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Homology.ShortComplex.Retract
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

-/

@[expose] public section


open CategoryTheory Limits

universe v u

open HomologicalComplex

section

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

/-- A morphism of homological complexes `f : K ⟶ L` is a quasi-isomorphism in degree `i`
when it induces a quasi-isomorphism of short complexes `K.sc i ⟶ L.sc i`. -/
class QuasiIsoAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : Prop where
  quasiIso : ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f)

lemma quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔
      ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f) := by
  constructor
  · intro h
    exact h.quasiIso
  · intro h
    exact ⟨h⟩

instance quasiIsoAt_of_isIso (f : K ⟶ L) [IsIso f] (i : ι) [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff]
  infer_instance

lemma quasiIsoAt_iff' (f : K ⟶ L) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j] [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    QuasiIsoAt f j ↔
      ShortComplex.QuasiIso ((shortComplexFunctor' C c i j k).map f) := by
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (natIsoSc' C c i j k hi hk) (Arrow.mk f))

lemma quasiIsoAt_of_retract {f : K ⟶ L} {f' : K' ⟶ L'}
    (h : RetractArrow f f') (i : ι) [K.HasHomology i] [L.HasHomology i]
    [K'.HasHomology i] [L'.HasHomology i] [hf' : QuasiIsoAt f' i] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff] at hf' ⊢
  exact ShortComplex.quasiIso_of_retract (h.map (shortComplexFunctor C c i))

lemma quasiIsoAt_iff_isIso_homologyMap (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔ IsIso (homologyMap f i) := by
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  rfl

lemma quasiIsoAt_iff_exactAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hK : K.ExactAt i) :
    QuasiIsoAt f i ↔ L.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hK ⊢
  constructor
  · intro h
    exact IsZero.of_iso hK (@asIso _ _ _ _ _ h).symm
  · intro hL
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

lemma quasiIsoAt_iff_exactAt' (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hL : L.ExactAt i) :
    QuasiIsoAt f i ↔ K.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hL ⊢
  constructor
  · intro h
    exact IsZero.of_iso hL (@asIso _ _ _ _ _ h)
  · intro hK
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

lemma exactAt_iff_of_quasiIsoAt (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt f i] :
    K.ExactAt i ↔ L.ExactAt i :=
  ⟨fun hK => (quasiIsoAt_iff_exactAt f i hK).1 inferInstance,
    fun hL => (quasiIsoAt_iff_exactAt' f i hL).1 inferInstance⟩

instance (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] [hf : QuasiIsoAt f i] :
    IsIso (homologyMap f i) := by
  simpa only [quasiIsoAt_iff, ShortComplex.quasiIso_iff] using hf

/-- The isomorphism `K.homology i ≅ L.homology i` induced by a morphism `f : K ⟶ L` such
that `[QuasiIsoAt f i]` holds. -/
@[simps! hom]
noncomputable def isoOfQuasiIsoAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] : K.homology i ≅ L.homology i :=
  asIso (homologyMap f i)

@[reassoc (attr := simp)]
lemma isoOfQuasiIsoAt_hom_inv_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] :
    homologyMap f i ≫ (isoOfQuasiIsoAt f i).inv = 𝟙 _ :=
  (isoOfQuasiIsoAt f i).hom_inv_id

@[reassoc (attr := simp)]
lemma isoOfQuasiIsoAt_inv_hom_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] :
    (isoOfQuasiIsoAt f i).inv ≫ homologyMap f i = 𝟙 _ :=
  (isoOfQuasiIsoAt f i).inv_hom_id

lemma CochainComplex.quasiIsoAt₀_iff {K L : CochainComplex C ℕ} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 0 0 1).HasHomology] [(L.sc' 0 0 1).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' C _ 0 0 1).map f) :=
  quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

lemma ChainComplex.quasiIsoAt₀_iff {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 1 0 0).HasHomology] [(L.sc' 1 0 0).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' C _ 1 0 0).map f) :=
  quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

/-- A morphism of homological complexes `f : K ⟶ L` is a quasi-isomorphism when it
is so in every degree, i.e. when the induced maps `homologyMap f i : K.homology i ⟶ L.homology i`
are all isomorphisms (see `quasiIso_iff` and `quasiIsoAt_iff_isIso_homologyMap`). -/
class QuasiIso (f : K ⟶ L) [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] : Prop where
  quasiIsoAt : ∀ i, QuasiIsoAt f i := by infer_instance

lemma quasiIso_iff (f : K ⟶ L) [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso f ↔ ∀ i, QuasiIsoAt f i :=
  ⟨fun h => h.quasiIsoAt, fun h => ⟨h⟩⟩

attribute [instance] QuasiIso.quasiIsoAt

instance quasiIso_of_isIso (f : K ⟶ L) [IsIso f] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso f where

instance quasiIsoAt_comp (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] [hφ' : QuasiIsoAt φ' i] :
    QuasiIsoAt (φ ≫ φ') i := by
  rw [quasiIsoAt_iff] at hφ hφ' ⊢
  rw [Functor.map_comp]
  exact ShortComplex.quasiIso_comp _ _

instance quasiIso_comp (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ : QuasiIso φ] [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') where

lemma quasiIsoAt_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] [hφφ' : QuasiIsoAt (φ ≫ φ') i] :
    QuasiIsoAt φ' i := by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ i) (homologyMap φ' i)

lemma quasiIsoAt_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] :
    QuasiIsoAt (φ ≫ φ') i ↔ QuasiIsoAt φ' i := by
  constructor
  · intro
    exact quasiIsoAt_of_comp_left φ φ' i
  · intro
    infer_instance

lemma quasiIso_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ : QuasiIso φ] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ' := by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_left φ φ']

lemma quasiIso_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ : QuasiIso φ] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ' := by
  rw [← quasiIso_iff_comp_left φ φ']
  infer_instance

lemma quasiIsoAt_of_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ' : QuasiIsoAt φ' i] [hφφ' : QuasiIsoAt (φ ≫ φ') i] :
    QuasiIsoAt φ i := by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ i) (homologyMap φ' i)

lemma quasiIsoAt_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ' : QuasiIsoAt φ' i] :
    QuasiIsoAt (φ ≫ φ') i ↔ QuasiIsoAt φ i := by
  constructor
  · intro
    exact quasiIsoAt_of_comp_right φ φ' i
  · intro
    infer_instance

lemma quasiIso_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_right φ φ']

lemma quasiIso_of_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ : QuasiIso φ'] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ := by
  rw [← quasiIso_iff_comp_right φ φ']
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma quasiIso_iff_of_arrow_mk_iso (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ')
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [∀ i, K'.HasHomology i] [∀ i, L'.HasHomology i] :
    QuasiIso φ ↔ QuasiIso φ' := by
  simp [← quasiIso_iff_comp_left (show K' ⟶ K from e.inv.left) φ,
    ← quasiIso_iff_comp_right φ' (show L' ⟶ L from e.inv.right)]

lemma quasiIso_of_arrow_mk_iso (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ')
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [∀ i, K'.HasHomology i] [∀ i, L'.HasHomology i]
    [hφ : QuasiIso φ] : QuasiIso φ' := by
  simpa only [← quasiIso_iff_of_arrow_mk_iso φ φ' e]

lemma quasiIso_of_retractArrow {f : K ⟶ L} {f' : K' ⟶ L'}
    (h : RetractArrow f f') [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [∀ i, K'.HasHomology i] [∀ i, L'.HasHomology i] [QuasiIso f'] :
    QuasiIso f where
  quasiIsoAt i := quasiIsoAt_of_retract h i

namespace HomologicalComplex

section PreservesHomology

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Preadditive C₁] [Preadditive C₂]
  {K L : HomologicalComplex C₁ c} (φ : K ⟶ L) (F : C₁ ⥤ C₂) [F.Additive]
  [F.PreservesHomology]

section

variable (i : ι) [K.HasHomology i] [L.HasHomology i]
  [((F.mapHomologicalComplex c).obj K).HasHomology i]
  [((F.mapHomologicalComplex c).obj L).HasHomology i]

instance quasiIsoAt_map_of_preservesHomology [hφ : QuasiIsoAt φ i] :
    QuasiIsoAt ((F.mapHomologicalComplex c).map φ) i := by
  rw [quasiIsoAt_iff] at hφ ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

lemma quasiIsoAt_map_iff_of_preservesHomology [F.ReflectsIsomorphisms] :
    QuasiIsoAt ((F.mapHomologicalComplex c).map φ) i ↔ QuasiIsoAt φ i := by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_iff_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

end

section

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
  [∀ i, ((F.mapHomologicalComplex c).obj K).HasHomology i]
  [∀ i, ((F.mapHomologicalComplex c).obj L).HasHomology i]

instance quasiIso_map_of_preservesHomology [hφ : QuasiIso φ] :
    QuasiIso ((F.mapHomologicalComplex c).map φ) where

lemma quasiIso_map_iff_of_preservesHomology [F.ReflectsIsomorphisms] :
    QuasiIso ((F.mapHomologicalComplex c).map φ) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_map_iff_of_preservesHomology φ F]

end

end PreservesHomology

variable (C c)

/-- The morphism property on `HomologicalComplex C c` given by quasi-isomorphisms. -/
def quasiIso [CategoryWithHomology C] :
    MorphismProperty (HomologicalComplex C c) := fun _ _ f => QuasiIso f

variable {C c} [CategoryWithHomology C]

@[simp]
lemma mem_quasiIso_iff (f : K ⟶ L) : quasiIso C c f ↔ QuasiIso f := by rfl

instance : (quasiIso C c).IsMultiplicative where
  id_mem _ := by
    rw [mem_quasiIso_iff]
    infer_instance
  comp_mem _ _ hf hg := by
    rw [mem_quasiIso_iff] at hf hg ⊢
    infer_instance

instance : (quasiIso C c).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    rw [mem_quasiIso_iff] at hg hfg ⊢
    rwa [← quasiIso_iff_comp_right f g]
  of_precomp f g hf hfg := by
    rw [mem_quasiIso_iff] at hf hfg ⊢
    rwa [← quasiIso_iff_comp_left f g]

instance : (quasiIso C c).IsStableUnderRetracts where
  of_retract h hg := by
    rw [mem_quasiIso_iff] at hg ⊢
    exact quasiIso_of_retractArrow h

instance : (quasiIso C c).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ (_ : IsIso _) ↦ by rw [mem_quasiIso_iff]; infer_instance)

end HomologicalComplex

end

namespace HomotopyEquiv

variable {ι : Type*} {C : Type u} [Category.{v} C] [Preadditive C]
  {c : ComplexShape ι} {K L : HomologicalComplex C c}
  (e : HomotopyEquiv K L)

instance quasiIsoAt_hom (n : ι) [K.HasHomology n] [L.HasHomology n] :
    QuasiIsoAt e.hom n := by
  classical
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  exact (e.toHomologyIso n).isIso_hom

instance quasiIsoAt_inv (n : ι) [K.HasHomology n] [L.HasHomology n] :
    QuasiIsoAt e.inv n :=
  e.symm.quasiIsoAt_hom n

instance quasiIso_hom [∀ n, K.HasHomology n] [∀ n, L.HasHomology n] :
    QuasiIso e.hom :=
  ⟨fun _ => inferInstance⟩

instance quasiIso_inv [∀ n, K.HasHomology n] [∀ n, L.HasHomology n] :
    QuasiIso e.inv :=
  ⟨fun _ => inferInstance⟩

end HomotopyEquiv

lemma homotopyEquivalences_le_quasiIso
    {ι : Type*} (C : Type u) [Category.{v} C] [Preadditive C]
    (c : ComplexShape ι) [CategoryWithHomology C] :
    homotopyEquivalences C c ≤ quasiIso C c := by
  rintro K L _ ⟨e, rfl⟩
  simp only [HomologicalComplex.mem_quasiIso_iff]
  infer_instance
