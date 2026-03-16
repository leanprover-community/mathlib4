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

@[reassoc, simp]
lemma map_comp (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) n₀ n₁ n₂ hn₁ hn₂ =
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
      X.map f₁' f₂' f₃' f₁'' f₂'' f₃'' β n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [map]
  simp [shortComplexMap_comp, ShortComplex.homologyMap_comp]

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

/-- `E^n₁(f₁, f₂, f₃)` identifies to the cokernel
of `δToCycles : H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)`. -/
@[simps]
noncomputable def leftHomologyDataShortComplex
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

@[simp]
lemma leftHomologyDataShortComplex_f' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.leftHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).f' =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  exact Fork.IsLimit.hom_ext hi (by simpa using hi.fac _ .zero)

/-- The cycles of the short complex `shortComplex` at `E^{n₁}(f₁, f₂, f₃)`
identifies to `Z^{n₁}(f₁, f₂)`. -/
noncomputable def cyclesIso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).cycles ≅ X.cycles f₁ f₂ n₁ :=
  (X.leftHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂).cyclesIso

@[reassoc (attr := simp)]
lemma cyclesIso_inv_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles = X.iCycles f₁ f₂ n₁ :=
  ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles _

@[reassoc (attr := simp)]
lemma cyclesIso_hom_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.iCycles f₁ f₂ n₁ =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles :=
  ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

/-- The epimorphism `Z^{n₁}(f₁, f₂) ⟶ E^{n₁}(f₁, f₂, f₃)`. -/
noncomputable def πE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.cycles f₁ f₂ n₁ ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).inv ≫
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homologyπ
  deriving Epi

@[reassoc (attr := simp)]
lemma δToCycles_cyclesIso_inv (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).toCycles := by
  simp [← cancel_mono (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).iCycles]

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

/-- The short complex `H^{n-1}(f₃) ⟶ Z^n(f₁, f₂) ⟶ E^n(f₁, f₂, f₃)` identifies
to the cokernel sequence of the definition of the homology of the short
complex `shortComplex` as a cokernel of `ShortComplex.toCycles`. -/
@[simps!]
noncomputable def cokernelSequenceCyclesEIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≅ ShortComplex.mk _ _
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).toCycles_comp_homologyπ :=
  ShortComplex.isoMk (Iso.refl _) (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).symm
    (Iso.refl _) (by simp) (by simp [πE])

lemma cokernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).Exact :=
  ShortComplex.exact_of_iso (X.cokernelSequenceCyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.homologyIsCokernel _))

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

/-- `E^n₁(f₁, f₂, f₃)` identifies to the kernel
of `δFromOpcycles : opZ^{n₁}(f₂, f₃) ⟶ H^{n₂}(f₁)`. -/
@[simps]
noncomputable def rightHomologyDataShortComplex
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).RightHomologyData := by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  have : hp.desc (CokernelCofork.ofπ _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).zero) =
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

@[simp]
lemma rightHomologyDataShortComplex_g'
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).g' =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ := by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  exact Cofork.IsColimit.hom_ext hp (by simpa using hp.fac _ .one)

/-- The opcycles of the short complex `shortComplex` at `E^{n₁}(f₁, f₂, f₃)`
identifies to `opZ^{n₁}(f₂, f₃)`. -/
noncomputable def opcyclesIso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).opcycles ≅ X.opcycles f₂ f₃ n₁ :=
  (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).opcyclesIso

@[reassoc (attr := simp)]
lemma p_opcyclesIso_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles ≫
      (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
    X.pOpcycles f₂ f₃ n₁ :=
  ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom _

@[reassoc (attr := simp)]
lemma p_opcyclesIso_inv (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.pOpcycles f₂ f₃ n₁ ≫ (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles :=
  (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).p_comp_opcyclesIso_inv

/-- The monomorphism `E^{n₁}(f₁, f₂, f₃) ⟶ opZ^{n₁}(f₂, f₃) ⟶ `. -/
noncomputable def ιE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.opcycles f₂ f₃ n₁ :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι ≫
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom
  deriving Mono

@[reassoc (attr := simp)]
lemma opcyclesIso_hom_δFromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).fromOpcycles := by
  simp [← cancel_epi (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles]

@[reassoc (attr := simp)]
lemma ιE_δFromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ = 0 := by
  simp [ιE]

@[reassoc (attr := simp)]
lemma πE_ιE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.iCycles f₁ f₂ n₁ ≫ X.pOpcycles f₂ f₃ n₁ := by
  simp [πE, ιE]

/-- The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ opZ^n(f₂, f₃) ⟶ H^{n+1}(f₁)`. -/
@[simps]
noncomputable def kernelSequenceOpcyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.ιE_δFromOpcycles f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

/-- The short complex `E^n(f₁, f₂, f₃) ⟶ opZ^n(f₂, f₃) ⟶ H^{n+1}(f₁)` identifies
to the kernel sequence of the definition of the homology of the short
complex `shortComplex` as a kernel of `ShortComplex.fromOpcycles`. -/
@[simps!]
noncomputable def kernelSequenceOpcyclesEIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≅
      ShortComplex.mk _ _
        (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι_comp_fromOpcycles :=
  Iso.symm (ShortComplex.isoMk (Iso.refl _) (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)
    (Iso.refl _) (by simp [ιE]) (by simp))

lemma kernelSequenceOpcyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).Exact :=
  ShortComplex.exact_of_iso (X.kernelSequenceOpcyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_f_is_kernel _ (ShortComplex.homologyIsKernel _))

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp; infer_instance

/-- The (exact) sequence `H^n(f₁) ⊞ H^{n-1}(f₃) ⟶ H^n(f₁ ≫ f₂) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps]
noncomputable def cokernelSequenceE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁) ⊞ (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₁₂)
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := biprod.desc ((X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)) (X.δ f₁₂ f₃ n₀ n₁)
  g := X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

lemma cokernelSequenceE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceCyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁) (by simpa using hx₂)
  dsimp at y₁ hy₁
  let z := π₁ ≫ x₂ - y₁ ≫ X.δ f₁₂ f₃ n₀ n₁
  obtain ⟨A₂, π₂, _, x₁, hx₁⟩ := (X.exact₂ f₁ f₂ f₁₂ h₁₂ n₁).exact_up_to_refinements z (by
      have : z ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ = 0 := by simp [z, hy₁]
      simpa only [zero_comp, Category.assoc, toCycles_i] using this =≫ X.iCycles f₁ f₂ n₁)
  dsimp at x₁ hx₁
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, biprod.lift x₁ (π₂ ≫ y₁), by simp [z, ← hx₁]⟩

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f₁₂) ⟶ A)
  (h : (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ x = 0)
  (hn₁ : n₀ + 1 = n₁) (h' : X.δ f₁₂ f₃ n₀ n₁ hn₁ ≫ x = 0)

/-- Constructor for morphisms for `E^{n₁}(f₁, f₂, f₃)`. -/
noncomputable def descE (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ A :=
  (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).desc x (by cat_disch)

@[reassoc (attr := simp)]
lemma toCycles_πE_descE (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.descE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ x h hn₁ h' hn₂ = x := by
  dsimp only [descE]
  rw [← Category.assoc]
  apply (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).g_desc

end

/-- The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ H^n(f₂ ≫ f₃) ⟶ H^n(f₃) ⊞ H^{n+1}(f₁)`. -/
@[simps]
noncomputable def kernelSequenceE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := (X.H n₁).obj (mk₁ f₂₃)
  X₃ := (X.H n₁).obj (mk₁ f₃) ⊞ (X.H n₂).obj (mk₁ f₁)
  f := X.ιE f₁ f₂ f₃ n₀ n₁ n₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁
  g := biprod.lift ((X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)) (X.δ f₁ f₂₃ n₁ n₂)
  zero := by ext <;> simp

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.kernelSequenceE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp; infer_instance

lemma kernelSequenceE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceOpcyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements
      (X.liftOpcycles f₂ f₃ f₂₃ h₂₃ x₂ (by simpa using hx₂ =≫ biprod.fst)) (by
        dsimp
        rw [← X.fromOpcyles_δ f₁ f₂ f₃ f₂₃ h₂₃ n₁ n₂,
          X.liftOpcycles_fromOpcycles_assoc]
        simpa using hx₂ =≫ biprod.snd)
  dsimp at x₁ hx₁
  refine ⟨A₁, π₁, inferInstance, x₁, ?_⟩
  dsimp
  rw [← reassoc_of% hx₁, liftOpcycles_fromOpcycles]

section

variable {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ f₂₃))
  (h : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃) = 0)
  (hn₂ : n₁ + 1 = n₂)
  (h' : x ≫ X.δ f₁ f₂₃ n₁ n₂ hn₂ = 0)

/-- Constructor for morphisms to `E^{n₁}(f₁, f₂, f₃)`. -/
noncomputable def liftE (hn₁ : n₀ + 1 = n₁ := by lia) :
    A ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).lift x (by cat_disch)

@[reassoc (attr := simp)]
lemma liftE_ιE_fromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.liftE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ x h hn₂ h' hn₁ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁ = x := by
  apply (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).lift_f

end

end

section

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  {i₀' i₁' i₂' i₃' : ι}
  (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')

@[reassoc]
lemma cyclesIso_inv_cyclesMap
    (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia)))
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      ShortComplex.cyclesMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) =
    X.cyclesMap f₁ f₂ f₁' f₂' β n₁ ≫ (X.cyclesIso f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂).inv := by
  subst hβ
  simp [← cancel_mono (ShortComplex.iCycles _), cyclesMap_i]

@[reassoc]
lemma opcyclesMap_opcyclesIso_hom
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃')
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2)
      (naturality' α 2 3) := by cat_disch)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex.opcyclesMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) ≫
      (X.opcyclesIso f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂).hom =
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.opcyclesMap f₂ f₃ f₂' f₃' γ n₁ := by
  subst hγ
  simp [← cancel_epi (ShortComplex.pOpcycles _), p_opcyclesMap]

@[reassoc]
lemma πE_map (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂') (n₀ n₁ n₂ : ℤ)
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia)) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ =
      X.cyclesMap f₁ f₂ f₁' f₂' β n₁ ≫ X.πE f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ := by
  simp [πE, map, X.cyclesIso_inv_cyclesMap_assoc f₁ f₂ f₃ f₁' f₂' f₃' α β hβ n₀ n₁ n₂]

@[reassoc]
lemma map_ιE
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃') (n₀ n₁ n₂ : ℤ)
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2)
      (naturality' α 2 3) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.opcyclesMap f₂ f₃ f₂' f₃' γ n₁ := by
  simp [ιE, map, X.opcyclesMap_opcyclesIso_hom f₁ f₂ f₃ f₁' f₂' f₃' α γ hγ n₀ n₁ n₂ hn₁ hn₂]

end

section

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
  (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

/-- The map `opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃)`. -/
noncomputable def opcyclesToE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcycles f₁₂ f₃ n₁ ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  X.descOpcycles _ _ _ _ hn₁ (X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂) (by simp)

@[reassoc (attr := simp)]
lemma p_opcyclesToE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.pOpcycles f₁₂ f₃ n₁ ≫ X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ =
      X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  simp [opcyclesToE]

@[reassoc (attr := simp)]
lemma opcyclesToE_ιE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.opcyclesMap f₁₂ f₃ f₂ f₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₁ := by
  simpa [← cancel_epi (X.pOpcycles f₁₂ f₃ n₁)] using (X.p_opcyclesMap ..).symm

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂) :=
  epi_of_epi_fac (X.p_opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂)

/-- The (exact) sequence `H^n(f₁) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps!]
noncomputable def cokernelSequenceOpcyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁)
  X₂ := X.opcycles f₁₂ f₃ n₁
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ X.pOpcycles f₁₂ f₃ n₁
  g := X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

lemma cokernelSequenceOpcyclesE_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.pOpcycles f₁₂ f₃ n₁) x₂
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements y₂
      (by simpa only [Category.assoc, p_opcyclesToE, hx₂, comp_zero]
        using hy₂.symm =≫ X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂)
  dsimp at y₁ hy₁
  obtain ⟨a, b, rfl⟩ : ∃ a b, y₁ = a ≫ biprod.inl + b ≫ biprod.inr :=
    ⟨y₁ ≫ biprod.fst, y₁ ≫ biprod.snd, by ext <;> simp⟩
  simp only [Preadditive.add_comp, Category.assoc, biprod.inl_desc, biprod.inr_desc] at hy₁
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, a, ?_⟩
  simp [Category.assoc, hy₂, reassoc_of% hy₁, Preadditive.add_comp, δ_pOpcycles,
    comp_zero, add_zero]

-- TODO: add dual statement to `cokernelSequenceOpcyclesE_exact`?

/-- The map `E^n(f₁, f₂, f₃) ⟶ Z^n(f₁, f₂ ≫ f₃)`. -/
noncomputable def EToCycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.cycles f₁ f₂₃ n₁ :=
  X.liftCycles  _ _ _ _ hn₂
    (X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁) (by simp)

@[reassoc (attr := simp)]
lemma EToCycles_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.iCycles f₁ f₂₃ n₁ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁ := by
  simp [EToCycles]

@[reassoc (attr := simp)]
lemma πE_EToCycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.cyclesMap f₁ f₂ f₁ f₂₃ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁ := by
  simpa [← cancel_mono (X.iCycles f₁ f₂₃ n₁)] using (X.cyclesMap_i ..).symm

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂) :=
  mono_of_mono_fac (X.EToCycles_i f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

/-- The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ Z^n(f₁, f₂ ≫ f₃) ⟶ H^n(f₃)`. -/
@[simps!]
noncomputable def kernelSequenceCyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := X.cycles f₁ f₂₃ n₁
  X₃ := (X.H n₁).obj (mk₁ f₃)
  f := X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂
  g := X.iCycles f₁ f₂₃ n₁ ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.kernelSequenceCyclesE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp; infer_instance

lemma kernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceCyclesE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.iCycles f₁ f₂₃ n₁) (by cat_disch)
  exact ⟨A₁, π₁, inferInstance, x₁, by simpa [← cancel_mono (X.iCycles ..)]⟩

end

section

variable {i j : ι} (f : i ⟶ j) {i' j' : ι} (f' : i' ⟶ j')

/-- An homology data for `X.shortComplex n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)`,
expressing `H^n₁(f)` as the homology of this short complex,
see `EIsoH`. -/
@[simps!]
noncomputable def homologyDataIdId (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).HomologyData :=
  (ShortComplex.HomologyData.ofZeros (X.shortComplex (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂)
    (X.δ_eq_zero_of_isIso₂ f (𝟙 j) inferInstance n₀ n₁ hn₁)
    (X.δ_eq_zero_of_isIso₁ (𝟙 i) f inferInstance n₁ n₂ hn₂))

/-- For any morphism `f : i ⟶ j`, this is the isomorphism from
`E^n₁(𝟙 i, f, 𝟙 j)` to `H^n₁(f)`. -/
noncomputable def EIsoH (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ ≅ (X.H n₁).obj (mk₁ f) :=
  (X.homologyDataIdId ..).left.homologyIso

lemma EIsoH_hom_naturality
    (α : mk₁ f ⟶ mk₁ f') (β : mk₃ (𝟙 _) f (𝟙 _) ⟶ mk₃ (𝟙 _) f' (𝟙 _))
    (n₀ n₁ n₂ : ℤ)
    (hβ : β = homMk₃ (α.app 0) (α.app 0) (α.app 1) (α.app 1)
      (by simp) (naturality' α 0 1) (by simp [Precomp.obj, Precomp.map]) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map (𝟙 _) f (𝟙 _) (𝟙 _) f' (𝟙 _) β n₀ n₁ n₂ hn₁ hn₂ ≫
      (X.EIsoH f' n₀ n₁ n₂ hn₁ hn₂).hom =
    (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (X.H n₁).map α := by
  obtain rfl : α = homMk₁ (β.app 1) (β.app 2) (naturality' β 1 2) := by
    subst hβ
    exact hom_ext₁ rfl rfl
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (X.shortComplexMap _ _ _ _ _ _ β n₀ n₁ n₂ hn₁ hn₂) ..).homologyMap_comm

end

section

variable {i₀ i₁ : ι} (f : i₀ ⟶ i₁) (n₀ n₁ : ℤ)

/-- The isomorphism `Z^n(𝟙 _, f) ≅ H^n(f)`. -/
noncomputable def cyclesIsoH (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.cycles (𝟙 i₀) f n₀ ≅ (X.H n₀).obj (mk₁ f) :=
  (X.cyclesIso (𝟙 i₀) f (𝟙 i₁) (n₀ - 1) n₀ n₁ (by lia) hn₁).symm ≪≫
    (X.homologyDataIdId ..).left.cyclesIso

@[simp]
lemma cyclesIsoH_inv (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cyclesIsoH f n₀ n₁ hn₁).inv = X.toCycles (𝟙 _) f f (by simp) n₀ := by
  rw [← cancel_mono (X.iCycles (𝟙 _) f n₀), toCycles_i]
  dsimp [cyclesIsoH]
  simp only [Category.assoc, cyclesIso_hom_i, homologyDataIdId_left_i,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, ← Functor.map_id]
  congr 1
  cat_disch

@[reassoc (attr := simp)]
lemma cyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cyclesIsoH f n₀ n₁ hn₁).hom ≫
      X.toCycles (𝟙 _) f f (by simp) n₀ = 𝟙 _ := by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]
lemma cyclesIsoH_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.toCycles (𝟙 _) f f (by simp) n₀ ≫
      (X.cyclesIsoH f n₀ n₁ hn₁).hom = 𝟙 _ := by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).inv_hom_id

/-- The isomorphism `opZ^n(f, 𝟙 _) ≅ H^n(f)`. -/
noncomputable def opcyclesIsoH (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.opcycles f (𝟙 i₁) n₁ ≅ (X.H n₁).obj (mk₁ f) :=
  (X.opcyclesIso (𝟙 i₀) f (𝟙 i₁) n₀ n₁ (n₁ + 1) hn₁ (by lia)).symm ≪≫
    (X.homologyDataIdId ..).right.opcyclesIso

@[simp]
lemma opcyclesIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.opcyclesIsoH f n₀ n₁ hn₁).hom = X.fromOpcycles f (𝟙 _) f (by simp) n₁ := by
  rw [← cancel_epi (X.pOpcycles f (𝟙 _) n₁), p_fromOpcycles]
  dsimp [opcyclesIsoH]
  simp only [p_opcyclesIso_inv_assoc, homologyDataIdId_right_p, ← Functor.map_id,
    ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom]
  congr 1
  cat_disch

@[reassoc (attr := simp)]
lemma opcyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) :
      X.fromOpcycles f (𝟙 _) f (by simp) n₁ ≫
        (X.opcyclesIsoH f n₀ n₁ hn₁).inv = 𝟙 _ := by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]
lemma opcyclesIsoH_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.opcyclesIsoH f n₀ n₁ hn₁).inv ≫
      X.fromOpcycles f (𝟙 _) f (by simp) n₁ = 𝟙 _ := by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).inv_hom_id

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) {i j : ι} (f : i ⟶ j)

@[reassoc (attr := simp)]
lemma cyclesIsoH_hom_EIsoH_inv :
    (X.cyclesIsoH f n₁ n₂ hn₂).hom ≫ (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).inv =
      X.πE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ := by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂).left
  have : h.cyclesIso.inv =
      X.toCycles (𝟙 i) f f (by simp) n₁ ≫
        (X.cyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).inv := by
    rw [← cancel_mono (X.cyclesIso ..).hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← cancel_mono (X.iCycles ..), Category.assoc, cyclesIso_hom_i ..,
      h.cyclesIso_inv_comp_iCycles, toCycles_i]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₀ = n₁ - 1 := by lia
  rw [← cancel_epi (X.cyclesIsoH f n₁ n₂ hn₂).inv,
    cyclesIsoH_inv .., cyclesIsoH_inv_hom_id_assoc ..]
  dsimp [EIsoH]
  rw [← cancel_epi h.π, h.π_comp_homologyIso_inv]
  simp [πE, h, this]

@[reassoc (attr := simp)]
lemma EIsoH_hom_opcyclesIsoH_inv :
    (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (X.opcyclesIsoH f n₀ n₁ hn₁).inv =
      X.ιE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ := by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂)
  have : h.right.opcyclesIso.hom =
      (X.opcyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).hom ≫
        X.fromOpcycles f (𝟙 j) f (by simp) n₁ := by
    rw [← cancel_epi (X.opcyclesIso ..).inv, Iso.inv_hom_id_assoc,
      ← cancel_epi (X.pOpcycles ..), p_opcyclesIso_inv_assoc ..,
      h.right.pOpcycles_comp_opcyclesIso_hom, p_fromOpcycles]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₂ = n₁ + 1 := by lia
  rw [← cancel_mono (X.opcyclesIsoH f n₀ n₁ hn₁).hom, Category.assoc,
    opcyclesIsoH_hom .., opcyclesIsoH_inv_hom_id ..]
  dsimp [EIsoH, ιE]
  rw [Category.assoc, ← this,
    h.left_homologyIso_eq_right_homologyIso_trans_iso_symm,
    ← ShortComplex.RightHomologyData.homologyIso_hom_comp_ι]
  simp [h]

end

section

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
    (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)

@[reassoc (attr := simp)]
lemma opcyclesMap_threeδ₂Toδ₁_opcyclesToE
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesMap _ _ _ _ (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃) n₁ ≫
      X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ = 0 := by
  rw [← cancel_epi (X.pOpcycles ..), comp_zero,
    p_opcyclesMap_assoc _ _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)]
  simp

/-- The short exact sequence
`0 ⟶ opZ^(f₁, f₂ ≫ f₃) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ H^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps]
noncomputable def shortComplexOpcyclesThreeδ₂Toδ₁
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _
    (X.opcyclesMap_threeδ₂Toδ₁_opcyclesToE f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

instance (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  replace hx := hx =≫ X.fromOpcycles f₁₂ f₃ _ rfl n₁
  rw [zero_comp, Category.assoc,
    X.opcyclesMap_fromOpcycles f₁ f₂₃ f₁₂ f₃ (f₁₂ ≫ f₃) (by cat_disch) _ rfl _ (𝟙 _) n₁
      (by simp) (by cat_disch), Functor.map_id, Category.comp_id] at hx
  rw [← cancel_mono (X.fromOpcycles f₁ f₂₃ (f₁₂ ≫ f₃) (by cat_disch) n₁), hx, zero_comp]

instance (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

lemma shortComplexOpcyclesThreeδ₂Toδ₁_exact
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  let φ : X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ ⟶
      (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂) :=
    { τ₁ := X.pOpcycles f₁ f₂₃ n₁
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id, X.p_opcyclesMap _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂)] }
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact X.cokernelSequenceOpcyclesE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂

lemma shortComplexOpcyclesThreeδ₂Toδ₁_shortExact
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).ShortExact where
  exact := X.shortComplexOpcyclesThreeδ₂Toδ₁_exact ..

end

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  {i₀' i₁' i₂' i₃' : ι} (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (f₁₂' : i₀' ⟶ i₂') (h₁₂' : f₁' ≫ f₂' = f₁₂')

@[reassoc]
lemma opcyclesToE_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') (β : mk₂ f₁₂ f₃ ⟶ mk₂ f₁₂' f₃')
    (n₀ n₁ n₂ : ℤ) (h₀ : β.app 0 = α.app 0 := by cat_disch) (h₁ : β.app 1 = α.app 2 := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫ X.map _ _ _ _ _ _ α _ _ _ =
      X.opcyclesMap _ _ _ _ β _ ≫ X.opcyclesToE f₁' f₂' f₃' f₁₂' h₁₂' n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← cancel_mono (X.ιE ..), Category.assoc, Category.assoc, opcyclesToE_ιE ..,
    ← cancel_epi (X.pOpcycles ..), p_opcyclesToE_assoc ..,
    X.πE_map_assoc _ _ _ _ _ _ _
      (homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1) (naturality' α 1 2)) ..,
    πE_ιE .., X.cyclesMap_i_assoc .., toCycles_i_assoc,
    X.p_opcyclesMap_assoc .., X.p_opcyclesMap ..,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  ext
  · simpa [h₀] using naturality' α 0 1
  · simp [h₁]

end SpectralObject

end Abelian

end CategoryTheory
