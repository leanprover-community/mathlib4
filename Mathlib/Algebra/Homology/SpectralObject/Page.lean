/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Cycles
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.ComposableArrows.Three

/-!
# Spectral objects in abelian categories

Let `X` be a spectral object index by the category `ι`
in the abelian category `C`. The purpose of this file
is to introduce the homology `X.E` of the short complex `X.shortComplex`
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

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (n₀ n₁ n₂ : ℤ)

/-- The short complex consisting of the composition of
two morphisms `X.δ`, given three composable morphisms `f₁`, `f₂`
and `f₃` in `ι`, and three consecutive integers. -/
@[simps]
def shortComplex (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₂)
  X₃ := (X.H n₂).obj (mk₁ f₁)
  f := X.δ f₂ f₃ n₀ n₁
  g := X.δ f₁ f₂ n₁ n₂

/-- The homology of the short complex `shortComplex` consisting of
two morphisms `X.δ`. In the documentation, we shorten it as `E^n₁(f₁, f₂, f₃)` -/
noncomputable def E (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) : C :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homology

lemma isZero_E_of_isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsZero (X.E f₁ f₂ f₃ n₀ n₁ n₂) :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).exact_iff_isZero_homology.1
    (ShortComplex.exact_of_isZero_X₂ _ h)

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  {i'' j'' k'' l'' : ι} (f₁'' : i'' ⟶ j'') (f₂'' : j'' ⟶ k'') (f₃'' : k'' ⟶ l'')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (β : mk₃ f₁' f₂' f₃' ⟶ mk₃ f₁'' f₂'' f₃'')
  (γ : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁'' f₂'' f₃'')
  (n₀ n₁ n₂ : ℤ)

/-- The functoriality of `shortComplex` with respect to morphisms
in `ComposableArrows ι 3`. -/
@[simps]
def shortComplexMap (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ ⟶
      X.shortComplex f₁' f₂' f₃' n₀ n₁ n₂ where
  τ₁ := (X.H n₀).map (homMk₁ (α.app 2) (α.app 3) (naturality' α 2 3))
  τ₂ := (X.H n₁).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))
  τ₃ := (X.H n₂).map (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
  comm₁₂ := δ_naturality ..
  comm₂₃ := δ_naturality ..

@[simp]
lemma shortComplexMap_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplexMap f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  ext
  all_goals dsimp; convert (X.H _).map_id _; cat_disch

@[reassoc, simp]
lemma shortComplexMap_comp (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplexMap f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) n₀ n₁ n₂ hn₁ hn₂  =
    X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
      X.shortComplexMap f₁' f₂' f₃' f₁'' f₂'' f₃'' β n₀ n₁ n₂ hn₁ hn₂ := by
  ext
  all_goals dsimp; rw [← Functor.map_comp]; congr 1; cat_disch

/-- The functoriality of `E` with respect to morphisms
in `ComposableArrows ι 3`. -/
noncomputable def map (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.E f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.homologyMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂)

@[simp]
lemma map_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  dsimp only [map]
  simp [shortComplexMap_id, ShortComplex.homologyMap_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, simp]
lemma map_comp (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) n₀ n₁ n₂ hn₁ hn₂ =
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
      X.map f₁' f₂' f₃' f₁'' f₂'' f₃'' β n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [map]
  simp [shortComplexMap_comp, ShortComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
lemma isIso_map
    (h₀ : IsIso ((X.H n₀).map ((functorArrows ι 2 3 3).map α)))
    (h₁ : IsIso ((X.H n₁).map ((functorArrows ι 1 2 3).map α)))
    (h₂ : IsIso ((X.H n₂).map ((functorArrows ι 0 1 3).map α)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) := by
  have : IsIso (shortComplexMap X f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂) := by
    apply +allowSynthFailures ShortComplex.isIso_of_isIso <;> assumption
  dsimp [map]
  infer_instance

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

lemma δ_eq_zero_of_isIso₁ (hf : IsIso f) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ = 0 := by
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ f g _ rfl n₀ n₁

lemma δ_eq_zero_of_isIso₂ (hg : IsIso g) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ = 0 := by
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using X.zero₁ f g _ rfl n₀ n₁

end

set_option backward.isDefEq.respectTransparency false in
lemma isZero_H_obj_of_isIso {i j : ι} (f : i ⟶ j) (hf : IsIso f) (n : ℤ) :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine IsZero.of_iso ?_ ((X.H n).mapIso e.symm)
  have h := X.zero₂ (𝟙 i) (𝟙 i) (𝟙 i) (by simp) n
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← h]
  congr 1
  cat_disch

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- `E^n₁(f₁, f₂, f₃)` identifies to the cokernel
of `δToCycles : H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)`. -/
@[simps]
noncomputable def leftHomologyDataShortComplexE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).LeftHomologyData := by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  have : hi.lift (KernelFork.ofι _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).zero) =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ :=
    Fork.IsLimit.hom_ext hi (by simpa using hi.fac _ .zero)
  exact {
    K := X.cycles f₁ f₂ n₁
    H := cokernel (X.δToCycles f₁ f₂ f₃ n₀ n₁)
    i := X.iCycles f₁ f₂ n₁
    π := cokernel.π _
    wi := by simp
    hi := hi
    wπ := by rw [this]; simp
    hπ := by
      refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).2
        (cokernelIsCokernel (X.δToCycles f₁ f₂ f₃ n₀ n₁))
      · exact parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa) (by simp)
      · exact Cofork.ext (Iso.refl _) }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma leftHomologyDataShortComplexE_f' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.leftHomologyDataShortComplexE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).f' =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  exact Fork.IsLimit.hom_ext hi (by simpa using hi.fac _ .zero)

/-- The cycles of the short complex `shortComplexE` at `E^{n₁}(f₁, f₂, f₃)`
identifies to `Z^{n₁}(f₁, f₂)`. -/
noncomputable def cyclesIso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).cycles ≅ X.cycles f₁ f₂ n₁ :=
  (X.leftHomologyDataShortComplexE f₁ f₂ f₃ n₀ n₁ n₂).cyclesIso

@[reassoc (attr := simp)]
lemma cyclesIso_inv_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ).inv ≫
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles = X.iCycles f₁ f₂ n₁ :=
  ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles _

@[reassoc (attr := simp)]
lemma cyclesIso_hom_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.iCycles f₁ f₂ n₁ =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ).iCycles :=
  ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

set_option backward.isDefEq.respectTransparency false in
/-- The epimorphism `Z^{n₁}(f₁, f₂) ⟶ E^{n₁}(f₁, f₂, f₃)`. -/
noncomputable def πE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.cycles f₁ f₂ n₁ ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).inv ≫
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homologyπ
  deriving Epi

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma δToCycles_cyclesIso_inv (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ).toCycles := by
  simp [← cancel_mono (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).iCycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma δToCycles_πE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ = 0 := by
  simp [πE]

/-- The (exact) sequence `H^{n-1}(f₃) ⟶ Z^n(f₁, f₂) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps]
noncomputable def cokernelSequenceCyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.δToCycles_πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

set_option backward.isDefEq.respectTransparency false in
/-- The short complex `H^{n-1}(f₃) ⟶ Z^n(f₁, f₂) ⟶ E^n(f₁, f₂, f₃)` identifies
to the cokernel sequence of the definition of the homology of the short
complex `shortComplexE` as a cokernel of `ShortComplex.toCycles`. -/
@[simps!]
noncomputable def cokernelSequenceCyclesEIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≅ ShortComplex.mk _ _
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).toCycles_comp_homologyπ :=
  ShortComplex.isoMk (Iso.refl _) (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).symm
    (Iso.refl _) (by simp) (by simp [πE])

lemma cokernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).Exact :=
  ShortComplex.exact_of_iso (X.cokernelSequenceCyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ).symm
    (ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.homologyIsCokernel _))

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- `E^n₁(f₁, f₂, f₃)` identifies to the kernel
of `δFromOpcycles : opZ^{n₁}(f₂, f₃) ⟶ H^{n₂}(f₁)`. -/
@[simps]
noncomputable def rightHomologyDataShortComplexE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).RightHomologyData := by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  have : hp.desc (CokernelCofork.ofπ _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ).zero) =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ :=
    Cofork.IsColimit.hom_ext hp (by simpa using hp.fac _ .one)
  exact {
    Q := X.opcycles f₂ f₃ n₁
    H := kernel (X.δFromOpcycles f₁ f₂ f₃ n₁ n₂)
    p := X.pOpcycles f₂ f₃ n₁
    ι := kernel.ι _
    wp := by simp
    hp := hp
    wι := by rw [this]; simp
    hι := by
      refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).2
        (kernelIsKernel (X.δFromOpcycles f₁ f₂ f₃ n₁ n₂))
      · exact parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa) (by simp)
      · exact Fork.ext (Iso.refl _) }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma rightHomologyDataShortComplexE_g'
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.rightHomologyDataShortComplexE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).g' =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ := by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  exact Cofork.IsColimit.hom_ext hp (by simpa using hp.fac _ .one)

end

end SpectralObject

end Abelian

end CategoryTheory
