/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Cycles
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.ComposableArrows.Three
public import Batteries.Tactic.Lint

/-!
# Spectral objects in abelian categories

Let `X` be a spectral object index by the category `ι`
in the abelian category `C`. The purpose of this file
is to introduce the homology `X.E` of the short complex `X.shortComplexE`
`(X.H n₀).obj (mk₁ f₃) ⟶ (X.H n₁).obj (mk₁ f₂) ⟶ (X.H n₂).obj (mk₁ f₁)`
when `f₁`, `f₂` and `f₃` are composable morphisms in `ι` and the
equalities `n₀ + 1 = n₁` and `n₁ + 1 = n₂` hold (both maps in the
short complex are given by `X.δ`). All the relevant objects in the
spectral sequence attached to spectral objects can be defined
in terms of this homology `X.E`: the objects in all pages, including
the page at infinity.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)

/-- The short complex consisting of the composition of
two morphisms `X.δ`, given three composable morphisms `f₁`, `f₂`
and `f₃` in `ι`, and three consecutive integers. -/
@[simps]
def shortComplexE : ShortComplex C where
  X₁ := (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₂)
  X₃ := (X.H n₂).obj (mk₁ f₁)
  f := X.δ n₀ n₁ hn₁ f₂ f₃
  g := X.δ n₁ n₂ hn₂ f₁ f₂

/-- The homology of the short complex `shortComplexE` consisting of
two morphisms `X.δ`. In the documentation, we shorten it as `E^n₁(f₁, f₂, f₃)` -/
noncomputable def E : C := (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homology

lemma isZero_E_of_isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂))) :
    IsZero (X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) :=
  (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_iff_isZero_homology.1
    (ShortComplex.exact_of_isZero_X₂ _ h)

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι}
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  {i'' j'' k'' l'' : ι} (f₁'' : i'' ⟶ j'') (f₂'' : j'' ⟶ k'') (f₃'' : k'' ⟶ l'')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (β : mk₃ f₁' f₂' f₃' ⟶ mk₃ f₁'' f₂'' f₃'')
  (γ : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁'' f₂'' f₃'')

/-- The functoriality of `shortComplexE` with respect to morphisms
in `ComposableArrows ι 3`. -/
@[simps]
def shortComplexEMap :
    X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶
      X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' where
  τ₁ := (X.H n₀).map (homMk₁ (α.app 2) (α.app 3) (naturality' α 2 3))
  τ₂ := (X.H n₁).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))
  τ₃ := (X.H n₂).map (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
  comm₁₂ := δ_naturality ..
  comm₂₃ := δ_naturality ..

@[simp]
lemma shortComplexEMap_id :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) = 𝟙 _ := by
  ext
  all_goals dsimp; convert (X.H _).map_id _; cat_disch

@[reassoc, simp]
lemma shortComplexEMap_comp :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) =
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β := by
  ext
  all_goals dsimp; rw [← Functor.map_comp]; congr 1; cat_disch

/-- The functoriality of `E` with respect to morphisms
in `ComposableArrows ι 3`. -/
noncomputable def EMap :
    X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' :=
  ShortComplex.homologyMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α)

@[simp]
lemma EMap_id :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) = 𝟙 _ := by
  dsimp only [EMap]
  rw [shortComplexEMap_id, ShortComplex.homologyMap_id]
  rfl

/-- Variant of `EMap_id`. -/
lemma EMap_id' (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃) (hα : α = 𝟙 _) :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ α = 𝟙 _ := by
  subst hα
  simp only [EMap_id]

@[reassoc, simp]
lemma EMap_comp :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) =
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β := by
  dsimp only [EMap]
  rw [shortComplexEMap_comp, ShortComplex.homologyMap_comp]

lemma isIso_EMap
    (h₀ : IsIso ((X.H n₀).map ((functorArrows ι 2 3 3).map α)))
    (h₁ : IsIso ((X.H n₁).map ((functorArrows ι 1 2 3).map α)))
    (h₂ : IsIso ((X.H n₂).map ((functorArrows ι 0 1 3).map α))) :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) := by
  have : IsIso (shortComplexEMap X n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) := by
    apply (config := { allowSynthFailures := true})
      ShortComplex.isIso_of_isIso <;> assumption
  dsimp [EMap]
  infer_instance

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

lemma δ_eq_zero_of_isIso₁ (hf : IsIso f) :
    X.δ n₀ n₁ hn₁ f g = 0 := by
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ n₀ n₁ hn₁ f g _ rfl

lemma δ_eq_zero_of_isIso₂ (hg : IsIso g) :
    X.δ n₀ n₁ hn₁ f g = 0 := by
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using X.zero₁ n₀ n₁ hn₁ f g _ rfl

end

lemma isZero_H_obj_of_isIso (n : ℤ) {i j : ι} (f : i ⟶ j) (hf : IsIso f) :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine IsZero.of_iso ?_ ((X.H n).mapIso e.symm)
  have h := X.zero₂ n (𝟙 i) (𝟙 i) (𝟙 i) (by simp)
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← h]
  congr 1
  cat_disch

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)

/-- `E^n₁(f₁, f₂, f₃)` identifies to the cokernel
of `δToCycles : H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)`. -/
@[simps]
noncomputable def leftHomologyDataShortComplexE :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).LeftHomologyData := by
  let hi := (X.kernelSequenceCycles_exact _ _ hn₂ f₁ f₂).fIsKernel
  have : hi.lift (KernelFork.ofι _ (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).zero) =
      X.δToCycles n₀ n₁ hn₁ f₁ f₂ f₃ :=
    Fork.IsLimit.hom_ext hi (by simpa using hi.fac _ .zero)
  refine {
  K := X.cycles n₁ f₁ f₂
  H := cokernel (X.δToCycles n₀ n₁ hn₁ f₁ f₂ f₃)
  i := X.iCycles n₁ f₁ f₂
  π := cokernel.π _
  wi := by simp
  hi := hi
  wπ := by rw [this]; simp
  hπ := by
    refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).2
      (cokernelIsCokernel (X.δToCycles n₀ n₁ hn₁ f₁ f₂ f₃))
    · exact parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa) (by simp)
    · exact Cofork.ext (Iso.refl _)}

@[simp]
lemma leftHomologyDataShortComplexE_f' :
    (X.leftHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).f' =
      X.δToCycles n₀ n₁ hn₁ f₁ f₂ f₃ := by
  let hi := (X.kernelSequenceCycles_exact _ _ hn₂ f₁ f₂).fIsKernel
  exact Fork.IsLimit.hom_ext hi (by simpa using hi.fac _ .zero)

noncomputable def cyclesIso :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).cycles ≅ X.cycles n₁ f₁ f₂ :=
  (X.leftHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).cyclesIso

@[reassoc (attr := simp)]
lemma cyclesIso_inv_i :
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv ≫
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).iCycles = X.iCycles n₁ f₁ f₂ :=
  ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles _

@[reassoc (attr := simp)]
lemma cyclesIso_hom_i :
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom ≫ X.iCycles n₁ f₁ f₂ =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).iCycles :=
  ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

noncomputable def πE : X.cycles n₁ f₁ f₂ ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ :=
  (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv ≫
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homologyπ
  deriving Epi

@[reassoc (attr := simp)]
lemma δToCycles_cyclesIso_inv :
    X.δToCycles n₀ n₁ hn₁ f₁ f₂ f₃ ≫ (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).toCycles := by
  rw [← cancel_mono (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).iCycles, Category.assoc,
    cyclesIso_inv_i, δToCycles_iCycles, ShortComplex.toCycles_i, shortComplexE_f]

@[reassoc (attr := simp)]
lemma δToCycles_πE :
    X.δToCycles n₀ n₁ hn₁ f₁ f₂ f₃ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ = 0 := by
  simp only [πE, δToCycles_cyclesIso_inv_assoc, ShortComplex.toCycles_comp_homologyπ]

/-- cokernelSequenceE' -/
@[simps]
noncomputable def cokernelSequenceE' : ShortComplex C :=
    ShortComplex.mk _ _ (X.δToCycles_πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)

@[simps!]
noncomputable def cokernelSequenceE'Iso :
    X.cokernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≅ ShortComplex.mk _ _
        (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).toCycles_comp_homologyπ :=
  ShortComplex.isoMk (Iso.refl _) (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).symm
    (Iso.refl _) (by simp) (by simp [πE])

lemma cokernelSequenceE'_exact :
    (X.cokernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).Exact :=
  ShortComplex.exact_of_iso (X.cokernelSequenceE'Iso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).symm
    (ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.homologyIsCokernel _))

instance : Epi (X.cokernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).g := by
  dsimp; infer_instance

/-- `E^n₁(f₁, f₂, f₃)` identifies to the kernel
of `δFromOpcycles : opZ^{n₁}(f₂, f₃) ⟶ H^{n₂}(f₁)`. -/
@[simps]
noncomputable def rightHomologyDataShortComplexE :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).RightHomologyData := by
  let hp := (X.cokernelSequenceOpcycles_exact _ _ hn₁ f₂ f₃).gIsCokernel
  have : hp.desc (CokernelCofork.ofπ _ (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).zero) =
      X.δFromOpcycles n₁ n₂ hn₂ f₁ f₂ f₃ :=
    Cofork.IsColimit.hom_ext hp (by simpa using hp.fac _ .one)
  refine {
  Q := X.opcycles n₁ f₂ f₃
  H := kernel (X.δFromOpcycles n₁ n₂ hn₂ f₁ f₂ f₃)
  p := X.pOpcycles n₁ f₂ f₃
  ι := kernel.ι _
  wp := by simp
  hp := hp
  wι := by rw [this]; simp
  hι := by
    refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).2
      (kernelIsKernel (X.δFromOpcycles n₁ n₂ hn₂ f₁ f₂ f₃))
    · exact parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa) (by simp)
    · exact Fork.ext (Iso.refl _) }

/-- rightHomologyDataShortComplexE_g' -/
@[simp]
lemma rightHomologyDataShortComplexE_g' :
    (X.rightHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).g' =
      X.δFromOpcycles n₁ n₂ hn₂ f₁ f₂ f₃ := by
  let hp := (X.cokernelSequenceOpcycles_exact _ _ hn₁ f₂ f₃).gIsCokernel
  exact Cofork.IsColimit.hom_ext hp (by simpa using hp.fac _ .one)

noncomputable def opcyclesIso :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).opcycles ≅ X.opcycles n₁ f₂ f₃ :=
  (X.rightHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).opcyclesIso

@[reassoc (attr := simp)]
lemma p_opcyclesIso_hom :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).pOpcycles ≫
      (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom =
      X.pOpcycles n₁ f₂ f₃ :=
  ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom _

@[reassoc (attr := simp)]
lemma p_opcyclesIso_inv :
    X.pOpcycles n₁ f₂ f₃ ≫ (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).pOpcycles :=
  (X.rightHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).p_comp_opcyclesIso_inv

noncomputable def ιE : X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ X.opcycles n₁ f₂ f₃ :=
  (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homologyι ≫
    (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom
  deriving Mono

@[reassoc (attr := simp)]
lemma opcyclesIso_hom_δFromOpcycles :
    (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom ≫ X.δFromOpcycles n₁ n₂ hn₂ f₁ f₂ f₃ =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).fromOpcycles := by
  rw [← cancel_epi (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).pOpcycles,
    p_opcyclesIso_hom_assoc, ShortComplex.p_fromOpcycles, shortComplexE_g,
    pOpcycles_δFromOpcycles]

@[reassoc (attr := simp)]
lemma ιE_δFromOpcycles :
    X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.δFromOpcycles n₁ n₂ hn₂ f₁ f₂ f₃ = 0 := by
  simp only [ιE, Category.assoc, opcyclesIso_hom_δFromOpcycles,
    ShortComplex.homologyι_comp_fromOpcycles]

@[reassoc (attr := simp)]
lemma πE_ιE :
    X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
      X.iCycles n₁ f₁ f₂ ≫ X.pOpcycles n₁ f₂ f₃ := by
  simp [πE, ιE]

/-- kernelSequenceE' -/
@[simps]
noncomputable def kernelSequenceE' : ShortComplex C :=
    ShortComplex.mk _ _ (X.ιE_δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)

@[simps!]
noncomputable def kernelSequenceE'Iso :
    X.kernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≅ ShortComplex.mk _ _
        (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homologyι_comp_fromOpcycles :=
  Iso.symm (ShortComplex.isoMk (Iso.refl _) (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)
    (Iso.refl _) (by simp [ιE]) (by simp))

lemma kernelSequenceE'_exact :
    (X.kernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).Exact :=
  ShortComplex.exact_of_iso (X.kernelSequenceE'Iso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).symm
    (ShortComplex.exact_of_f_is_kernel _ (ShortComplex.homologyIsKernel _))

instance : Mono (X.kernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).f := by
  dsimp
  infer_instance

@[simps]
noncomputable def cokernelSequenceE : ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁) ⊞ (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₁₂)
  X₃ := X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  f := biprod.desc ((X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)) (X.δ n₀ n₁ hn₁ f₁₂ f₃)
  g := X.toCycles n₁ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  zero := by ext <;> simp

instance : Epi (X.cokernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).g := by
  dsimp
  apply epi_comp

lemma cokernelSequenceE_exact :
    (X.cokernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE'_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_up_to_refinements
      (x₂ ≫ X.toCycles n₁ f₁ f₂ f₁₂ h₁₂) (by simpa using hx₂)
  dsimp at y₁ hy₁
  let z := π₁ ≫ x₂ - y₁ ≫ X.δ n₀ n₁ hn₁ f₁₂ f₃
  obtain ⟨A₂, π₂, _, x₁, hx₁⟩ := (X.exact₂ n₁ f₁ f₂ f₁₂ h₁₂).exact_up_to_refinements z (by
      have : z ≫ X.toCycles n₁ f₁ f₂ f₁₂ h₁₂ = 0 := by simp [z, hy₁]
      simpa only [zero_comp, Category.assoc, toCycles_i] using this =≫ X.iCycles n₁ f₁ f₂)
  dsimp at x₁ hx₁
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, biprod.lift x₁ (π₂ ≫ y₁), by simp [z, ← hx₁]⟩

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f₁₂) ⟶ A)
  (h : (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ x = 0)
  (h' : X.δ n₀ n₁ hn₁ f₁₂ f₃ ≫ x = 0)

noncomputable def descE :
    X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ A :=
  (X.cokernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).desc x (by cat_disch)

@[reassoc (attr := simp)]
lemma toCycles_πE_descE :
    X.toCycles n₁ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫
      X.descE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ x h h' = x := by
  dsimp only [descE]
  rw [← Category.assoc]
  apply (X.cokernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).g_desc

end

@[simps]
noncomputable def kernelSequenceE : ShortComplex C where
  X₁ := X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  X₂ := (X.H n₁).obj (mk₁ f₂₃)
  X₃ := (X.H n₁).obj (mk₁ f₃) ⊞ (X.H n₂).obj (mk₁ f₁)
  f := X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.fromOpcycles n₁ f₂ f₃ f₂₃ h₂₃
  g := biprod.lift ((X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)) (X.δ n₁ n₂ hn₂ f₁ f₂₃)
  zero := by ext <;> simp

instance : Mono (X.kernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).f := by
  dsimp
  infer_instance

lemma kernelSequenceE_exact :
    (X.kernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceE'_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_up_to_refinements
      (X.liftOpcycles n₁ f₂ f₃ f₂₃ h₂₃ x₂ (by simpa using hx₂ =≫ biprod.fst)) (by
        dsimp
        rw [← X.fromOpcyles_δ n₁ n₂ hn₂ f₁ f₂ f₃ f₂₃ h₂₃,
          X.liftOpcycles_fromOpcycles_assoc ]
        simpa using hx₂ =≫ biprod.snd)
  dsimp at x₁ hx₁
  refine ⟨A₁, π₁, inferInstance, x₁, ?_⟩
  dsimp
  rw [← reassoc_of% hx₁, liftOpcycles_fromOpcycles]

section

variable {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ f₂₃))
  (h : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃) = 0)
  (h' : x ≫ X.δ n₁ n₂ hn₂ f₁ f₂₃ = 0)

noncomputable def liftE :
    A ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ :=
  (X.kernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).lift x (by cat_disch)

@[reassoc (attr := simp)]
lemma liftE_ιE_fromOpcycles :
    X.liftE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃ x h h' ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫
      X.fromOpcycles n₁ f₂ f₃ f₂₃ h₂₃ = x := by
  apply (X.kernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).lift_f

end

end

section

variable (n₀ n₁ n₂ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  {i₀' i₁' i₂' i₃' : ι}
  (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')

@[reassoc]
lemma cyclesIso_inv_cyclesMap
    (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia))) :
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv ≫
      ShortComplex.cyclesMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) =
      X.cyclesMap n₁ f₁ f₂ f₁' f₂' β ≫
        (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃').inv := by
  subst hβ
  rw [← cancel_mono (ShortComplex.iCycles _), Category.assoc, Category.assoc,
    ShortComplex.cyclesMap_i, cyclesIso_inv_i_assoc, cyclesIso_inv_i,
    shortComplexEMap_τ₂, cyclesMap_i]
  dsimp

@[reassoc]
lemma opcyclesMap_opcyclesIso_hom
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃')
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2) (naturality' α 2 3)) :
    ShortComplex.opcyclesMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) ≫
      (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃').hom =
    (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom ≫ X.opcyclesMap n₁ f₂ f₃ f₂' f₃' γ := by
  subst hγ
  rw [← cancel_epi (ShortComplex.pOpcycles _), ShortComplex.p_opcyclesMap_assoc,
    p_opcyclesIso_hom, p_opcyclesIso_hom_assoc, shortComplexEMap_τ₂, p_opcyclesMap]
  dsimp

@[reassoc]
lemma πE_EMap (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
    (naturality' α 1 2 (by lia) (by lia))) :
    X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α =
      X.cyclesMap n₁ f₁ f₂ f₁' f₂' β ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' := by
  dsimp [πE, EMap]
  simp only [Category.assoc, ShortComplex.homologyπ_naturality,
    X.cyclesIso_inv_cyclesMap_assoc n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α β hβ]

@[reassoc]
lemma EMap_ιE
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃')
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2) (naturality' α 2 3)) :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' =
      X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.opcyclesMap n₁ f₂ f₃ f₂' f₃' γ := by
  dsimp [ιE, EMap]
  simp only [ShortComplex.homologyι_naturality_assoc, Category.assoc,
    X.opcyclesMap_opcyclesIso_hom n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α γ hγ]

end

section

variable (n₀ n₁ n₂ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)

noncomputable def opcyclesToE : X.opcycles n₁ f₁₂ f₃ ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ :=
  X.descOpcycles n₀ _ hn₁ _ _
    (X.toCycles n₁ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) (by simp)

@[reassoc (attr := simp)]
lemma p_opcyclesToE :
    X.pOpcycles n₁ f₁₂ f₃ ≫ X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ =
      X.toCycles n₁ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := by
  simp [opcyclesToE]

@[reassoc (attr := simp)]
lemma opcyclesToE_ιE :
    X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
      X.opcyclesMap n₁ f₁₂ f₃ f₂ f₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) := by
  rw [← cancel_epi (X.pOpcycles n₁ f₁₂ f₃), p_opcyclesToE_assoc,
    πE_ιE, toCycles_i_assoc]
  symm
  apply X.p_opcyclesMap
  rfl

instance : Epi (X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂) :=
  epi_of_epi_fac (X.p_opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂)

/-- cokernelSequenceE'' -/
@[simps!]
noncomputable def cokernelSequenceE'' : ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁)
  X₂ := X.opcycles n₁ f₁₂ f₃
  X₃ := X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  f := (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ X.pOpcycles n₁ f₁₂ f₃
  g := X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂

instance : Epi (X.cokernelSequenceE'' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).g := by
  dsimp
  infer_instance

lemma cokernelSequenceE''_exact :
    (X.cokernelSequenceE'' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.pOpcycles n₁ f₁₂ f₃) x₂
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).exact_up_to_refinements y₂
      (by simpa only [Category.assoc, p_opcyclesToE, hx₂, comp_zero]
        using hy₂.symm =≫ X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂)
  dsimp at y₁ hy₁
  obtain ⟨a, b, rfl⟩ : ∃ a b, y₁ = a ≫ biprod.inl + b ≫ biprod.inr :=
    ⟨y₁ ≫ biprod.fst, y₁ ≫ biprod.snd, by ext <;> simp⟩
  simp only [Preadditive.add_comp, Category.assoc, biprod.inl_desc, biprod.inr_desc] at hy₁
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, a, ?_⟩
  dsimp
  simp only [Category.assoc, hy₂, reassoc_of% hy₁, Preadditive.add_comp, δ_pOpcycles,
    comp_zero, add_zero]

-- TODO: dual statement?

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j : ι} (f : i ⟶ j) {i' j' : ι} (f' : i' ⟶ j')

/-- An homology data for `X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)`,
expressing `H^n₁(f)` as the homology of this short complex,
see `EIsoH`. -/
@[simps!]
noncomputable def homologyDataEIdId :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)).HomologyData :=
  (ShortComplex.HomologyData.ofZeros (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j))
    (X.δ_eq_zero_of_isIso₂ n₀ n₁ hn₁ f (𝟙 j) inferInstance)
    (X.δ_eq_zero_of_isIso₁ n₁ n₂ hn₂ (𝟙 i) f inferInstance))

/-- For any morphism `f : i ⟶ j`, this is the isomorphism from
`E^n₁(𝟙 i, f, 𝟙 j)` to `H^n₁(f)`. -/
noncomputable def EIsoH :
    X.E n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j) ≅ (X.H n₁).obj (mk₁ f) :=
  (X.homologyDataEIdId ..).left.homologyIso

lemma EIsoH_hom_naturality
    (α : mk₁ f ⟶ mk₁ f') (β : mk₃ (𝟙 _) f (𝟙 _) ⟶ mk₃ (𝟙 _) f' (𝟙 _))
    (hβ : β = homMk₃ (α.app 0) (α.app 0) (α.app 1) (α.app 1)
      (by simp) (naturality' α 0 1) (by simp [Precomp.obj, Precomp.map])) :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ (𝟙 _) f (𝟙 _) (𝟙 _) f' (𝟙 _) β ≫
      (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f').hom =
    (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom ≫ (X.H n₁).map α := by
  obtain rfl : α = homMk₁ (β.app 1) (β.app 2) (naturality' β 1 2) := by
    subst hβ
    exact hom_ext₁ rfl rfl
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ β) _ _ _ _).homologyMap_comm

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i₀ i₁ : ι} (f : i₀ ⟶ i₁)

noncomputable def cyclesIsoH :
    X.cycles n₀ (𝟙 i₀) f ≅ (X.H n₀).obj (mk₁ f) :=
  (X.cyclesIso (n₀ - 1) n₀ n₁ (by lia) hn₁ (𝟙 i₀) f (𝟙 i₁)).symm ≪≫
    (X.homologyDataEIdId ..).left.cyclesIso

@[simp]
lemma cyclesIsoH_inv :
    (X.cyclesIsoH n₀ n₁ hn₁ f).inv = X.toCycles n₀ (𝟙 _) f f (by simp) := by
  rw [← cancel_mono (X.iCycles n₀ (𝟙 _) f ), toCycles_i]
  dsimp [cyclesIsoH]
  rw [Category.assoc, cyclesIso_hom_i,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles,
    homologyDataEIdId_left_i, ← Functor.map_id]
  congr 1
  cat_disch

@[reassoc (attr := simp)]
lemma cyclesIsoH_hom_inv_id :
    (X.cyclesIsoH n₀ n₁ hn₁ f).hom ≫
      X.toCycles n₀ (𝟙 _) f f (by simp) = 𝟙 _ := by
  simpa using (X.cyclesIsoH n₀ n₁ hn₁ f).hom_inv_id

@[reassoc (attr := simp)]
lemma cyclesIsoH_inv_hom_id :
    X.toCycles n₀ (𝟙 _) f f (by simp) ≫
      (X.cyclesIsoH n₀ n₁ hn₁ f).hom = 𝟙 _ := by
  simpa using (X.cyclesIsoH n₀ n₁ hn₁ f).inv_hom_id

noncomputable def opcyclesIsoH :
    X.opcycles n₁ f (𝟙 i₁) ≅ (X.H n₁).obj (mk₁ f) :=
  (X.opcyclesIso n₀ n₁ (n₁ + 1) hn₁ (by lia) (𝟙 i₀) f (𝟙 i₁)).symm ≪≫
    (X.homologyDataEIdId ..).right.opcyclesIso

@[simp]
lemma opcyclesIsoH_hom :
    (X.opcyclesIsoH n₀ n₁ hn₁ f).hom = X.fromOpcycles n₁ f (𝟙 _) f (by simp) := by
  rw [← cancel_epi (X.pOpcycles n₁ f (𝟙 _)), p_fromOpcycles]
  dsimp [opcyclesIsoH]
  rw [p_opcyclesIso_inv_assoc, ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom,
    homologyDataEIdId_right_p, ← Functor.map_id]
  congr 1
  cat_disch

@[reassoc (attr := simp)]
lemma opcyclesIsoH_hom_inv_id :
      X.fromOpcycles n₁ f (𝟙 _) f (by simp) ≫
        (X.opcyclesIsoH n₀ n₁ hn₁ f).inv = 𝟙 _ := by
  simpa using (X.opcyclesIsoH n₀ n₁ hn₁ f).hom_inv_id

@[reassoc (attr := simp)]
lemma opcyclesIsoH_inv_hom_id :
    (X.opcyclesIsoH n₀ n₁ hn₁ f).inv ≫
      X.fromOpcycles n₁ f (𝟙 _) f (by simp) = 𝟙 _ := by
  simpa using (X.opcyclesIsoH n₀ n₁ hn₁ f).inv_hom_id

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) {i j : ι} (f : i ⟶ j)

@[reassoc (attr := simp)]
lemma cyclesIsoH_hom_EIsoH_inv :
    (X.cyclesIsoH n₁ n₂ hn₂ f).hom ≫ (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f).inv =
      X.πE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j) := by
  let h := (X.homologyDataEIdId n₀ n₁ n₂ hn₁ hn₂ f).left
  have : h.cyclesIso.inv =
      X.toCycles n₁ (𝟙 i) f f (by simp) ≫
        (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)).inv := by
    rw [← cancel_mono (X.cyclesIso ..).hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← cancel_mono (X.iCycles ..), Category.assoc, cyclesIso_hom_i,
      h.cyclesIso_inv_comp_iCycles, toCycles_i]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₀ = n₁ - 1 := by lia
  rw [← cancel_epi (X.cyclesIsoH n₁ n₂ hn₂ f).inv,
    cyclesIsoH_inv, cyclesIsoH_inv_hom_id_assoc]
  dsimp [EIsoH]
  rw [← cancel_epi h.π, h.π_comp_homologyIso_inv]
  simp [πE, h, this]

@[reassoc (attr := simp)]
lemma EIsoH_hom_opcyclesIsoH_inv :
    (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom ≫ (X.opcyclesIsoH n₀ n₁ hn₁ f).inv =
      X.ιE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j) := by
  let h := (X.homologyDataEIdId n₀ n₁ n₂ hn₁ hn₂ f)
  have : h.right.opcyclesIso.hom =
      (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)).hom ≫
        X.fromOpcycles n₁ f (𝟙 j) f (by simp) := by
    rw [← cancel_epi (X.opcyclesIso ..).inv, Iso.inv_hom_id_assoc,
      ← cancel_epi (X.pOpcycles ..), p_opcyclesIso_inv_assoc,
      h.right.pOpcycles_comp_opcyclesIso_hom, p_fromOpcycles]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₂ = n₁ + 1 := by lia
  rw [← cancel_mono (X.opcyclesIsoH n₀ n₁ hn₁ f).hom, Category.assoc,
    opcyclesIsoH_hom, opcyclesIsoH_inv_hom_id]
  dsimp [EIsoH, ιE]
  rw [Category.assoc, ← this,
    h.left_homologyIso_eq_right_homologyIso_trans_iso_symm,
    ← ShortComplex.RightHomologyData.homologyIso_hom_comp_ι]
  simp [h]

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
    (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)

@[reassoc (attr := simp)]
lemma opcyclesMap_threeδ₂Toδ₁_opcyclesToE :
    X.opcyclesMap n₁ _ _ _ _ (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃) ≫
      X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ = 0 := by
  rw [← cancel_epi (X.pOpcycles ..), comp_zero,
    p_opcyclesMap_assoc _ _ _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) rfl _,
    p_opcyclesToE, H_map_twoδ₂Toδ₁_toCycles_assoc, zero_comp]

@[simps]
noncomputable def shortComplexOpcyclesThreeδ₂Toδ₁ : ShortComplex C :=
  ShortComplex.mk _ _
    (X.opcyclesMap_threeδ₂Toδ₁_opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃)

instance :
    Mono (X.shortComplexOpcyclesThreeδ₂Toδ₁ n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).f := by
  dsimp
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  replace hx := hx =≫ X.fromOpcycles n₁ f₁₂ f₃ _ rfl
  rw [zero_comp, Category.assoc,
    X.opcyclesMap_fromOpcycles n₁ f₁ f₂₃ f₁₂ f₃ (f₁₂ ≫ f₃) (by cat_disch) _ rfl _ (𝟙 _)
      (by simp) (by cat_disch), Functor.map_id, Category.comp_id] at hx
  rw [← cancel_mono (X.fromOpcycles n₁ f₁ f₂₃ (f₁₂ ≫ f₃) (by cat_disch)), hx, zero_comp]

instance :
    Epi (X.shortComplexOpcyclesThreeδ₂Toδ₁ n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).g := by
  dsimp; infer_instance

lemma shortComplexOpcyclesThreeδ₂Toδ₁_exact :
    (X.shortComplexOpcyclesThreeδ₂Toδ₁ n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).Exact := by
  let φ : X.cokernelSequenceE'' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ ⟶
      (X.shortComplexOpcyclesThreeδ₂Toδ₁ n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃) :=
    { τ₁ := X.pOpcycles n₁ f₁ f₂₃
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id, X.p_opcyclesMap _ _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂) rfl] }
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact X.cokernelSequenceE''_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂

lemma shortComplexOpcyclesThreeδ₂Toδ₁_shortExact :
    (X.shortComplexOpcyclesThreeδ₂Toδ₁ n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).ShortExact where
  exact := X.shortComplexOpcyclesThreeδ₂Toδ₁_exact ..

end

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    {i₀' i₁' i₂' i₃' : ι} (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
    (f₁₂' : i₀' ⟶ i₂') (h₁₂' : f₁' ≫ f₂' = f₁₂')

@[reassoc]
lemma opcyclesToE_EMap (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') (β : mk₂ f₁₂ f₃ ⟶ mk₂ f₁₂' f₃')
    (h₀ : β.app 0 = α.app 0) (h₁ : β.app 1 = α.app 2) :
    X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ ≫ X.EMap _ _ _ _ _ _ _ _ _ _ _ α =
      X.opcyclesMap _ _ _ _ _ β ≫ X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁₂' h₁₂' := by
  rw [← cancel_mono (X.ιE ..), Category.assoc, Category.assoc, opcyclesToE_ιE,
    ← cancel_epi (X.pOpcycles ..), p_opcyclesToE_assoc,
    X.πE_EMap_assoc _ _ _ _ _ _ _ _ _ _ _ _
      (homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1) (naturality' α 1 2)) rfl,
    πE_ιE, X.cyclesMap_i_assoc _ _ _ _ _ _ _ rfl, toCycles_i_assoc,
    X.p_opcyclesMap_assoc _ _ _ _ _ _ _ rfl, X.p_opcyclesMap _ _ _ _ _ _ _ rfl,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  ext
  · simpa [h₀] using naturality' α 0 1
  · simp [h₁]

end SpectralObject

end Abelian

end CategoryTheory
