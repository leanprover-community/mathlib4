/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Left derivability structures on homological complexes

-/

open CategoryTheory

variable {A α C : Type*} [Category A] [Abelian A] {c : ComplexShape α}
  [Category C] {W : MorphismProperty C}
  (Φ : LocalizerMorphism W (HomologicalComplex.quasiIso A c))
  [Φ.functor.Full] [Φ.functor.Faithful]
  (hW : W = (HomologicalComplex.quasiIso A c).inverseImage Φ.functor)
  {ρ : HomologicalComplex A c ⥤ C} (π : ρ ⋙ Φ.functor ⟶ 𝟭 _) [∀ K, QuasiIso (π.app K)]

namespace HomologicalComplex

include hW π

lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_of_functorial_left_resolutions π
    (fun _ ↦ by rw [mem_quasiIso_iff]; infer_instance) hW

lemma isLeftDerivabilityStructure_of_functorial_left_resolutions :
    Φ.IsLeftDerivabilityStructure :=
  Φ.isLeftDerivabilityStructure_of_functorial_resolutions π
    (fun _ ↦ by rw [mem_quasiIso_iff]; infer_instance) hW

end HomologicalComplex
