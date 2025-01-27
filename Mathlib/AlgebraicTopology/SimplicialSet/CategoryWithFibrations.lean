/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Cofibrations and fibrations in the category of simplicial sets

We endow `SSet` with `CategoryWithCofibrations` and `CategoryWithFibrations`
instances. Cofibrations are monomorphisms, and fibrations are morphisms
having the right lifting property with respect to horn inclusions.

-/

open CategoryTheory HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

namespace modelCategory

/-- The generating cofibrations. -/
def I : MorphismProperty SSet.{u} :=
  .ofHoms (fun (n : ℕ) ↦ (subcomplexBoundary.{u} n).ι)

lemma subcomplexBoundary_ι_mem_I (n : ℕ) :
    I (subcomplexBoundary.{u} n).ι := by constructor

/-- The generating trivial cofibrations. -/
def J : MorphismProperty SSet.{u} :=
  ⨆ n, .ofHoms (fun i ↦ (subcomplexHorn.{u} (n + 1) i).ι)

lemma subcomplexHorn_ι_mem_J (n : ℕ) (i : Fin (n + 2)):
    J (subcomplexHorn.{u} (n + 1) i).ι := by
  simp only [J, iSup_iff]
  exact ⟨n, ⟨i⟩⟩

lemma I_le_monomorphisms : I.{u} ≤ monomorphisms _ := by
  rintro _ _ _ ⟨n⟩
  simp only [monomorphisms.iff]
  have : Mono (Subpresheaf.ι (subcomplexBoundary.{u} n)) := inferInstance
  infer_instance

lemma J_le_monomorphisms : J.{u} ≤ monomorphisms _ := by
  rintro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  simp only [monomorphisms.iff]
  infer_instance

instance : CategoryWithCofibrations SSet.{u} where
  cofibrations := .monomorphisms _

instance : CategoryWithFibrations SSet.{u} where
  fibrations := J.rlp

lemma cofibrations_eq : cofibrations SSet.{u} = monomorphisms _ := rfl

lemma fibrations_eq : fibrations SSet.{u} = J.rlp := rfl

section

variable {X Y : SSet.{u}} (f : X ⟶ Y)

lemma cofibration_iff : Cofibration f ↔ Mono f := by
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

lemma fibration_iff : Fibration f ↔ J.rlp f := by
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

instance [Cofibration f] : Mono f := by rwa [← cofibration_iff]

lemma cofibration_of_mono [Mono f] : Cofibration f := by rwa [cofibration_iff]

instance [hf : Fibration f] {n : ℕ} (i : Fin (n + 2)) :
    HasLiftingProperty (subcomplexHorn (n + 1) i).ι f := by
  rw [fibration_iff] at hf
  exact hf _ (subcomplexHorn_ι_mem_J _ _)

end

end modelCategory

end SSet
