/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
import Mathlib.Algebra.Homology.Localization

/-!
# Left derivability structures on homological complexes

-/

open CategoryTheory

variable {A α C₀ : Type*} [Category A] [Abelian A] {c : ComplexShape α}
  [Category C₀] {W₀ : MorphismProperty C₀}
  (Φ : LocalizerMorphism W₀ (HomologicalComplex.quasiIso A c))
  [Φ.functor.Full] [Φ.functor.Faithful]
  (hW₀ : W₀ = (HomologicalComplex.quasiIso A c).inverseImage Φ.functor)
  {ρ : HomologicalComplex A c ⥤ C₀} (π : ρ ⋙ Φ.functor ⟶ 𝟭 _) [∀ K, QuasiIso (π.app K)]

namespace HomologicalComplex

include hW₀ π

lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_of_functorial_left_resolutions π
    (fun _ ↦ by rw [mem_quasiIso_iff]; infer_instance) hW₀

lemma isLeftDerivabilityStructure_of_functorial_left_resolutions :
    Φ.IsLeftDerivabilityStructure :=
  Φ.isLeftDerivabilityStructure_of_functorial_resolutions π
    (fun _ ↦ by rw [mem_quasiIso_iff]; infer_instance) hW₀

end HomologicalComplex

namespace HomotopyCategory

variable {Φ} {H₀ : Type} [Category H₀] {W₀ₕ : MorphismProperty H₀}
  {Φₕ : LocalizerMorphism W₀ₕ (quasiIso A c)}
  [Φₕ.functor.Full] [Φₕ.functor.Faithful]
  (hW₀ₕ : W₀ₕ = (quasiIso A c).inverseImage Φₕ.functor)
  {Ψ : LocalizerMorphism W₀ W₀ₕ} [Ψ.IsLocalizedEquivalence]
  (e : Φ.functor ⋙ quotient _ _ ≅ Ψ.functor ⋙ Φₕ.functor)

/-lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φₕ.IsLocalizedEquivalence := by
  sorry

lemma isLeftDerivabilityStructure_of_functorial_left_resolutions :
    Φₕ.IsLeftDerivabilityStructure :=
  sorry -/

end HomotopyCategory
