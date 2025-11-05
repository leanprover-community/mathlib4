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

We have an instance `mono_of_cofibration` (but only a lemma `cofibration_of_mono`).
Then, when stating lemmas about cofibrations of simplicial sets, it is advisable
to use the assumption `[Mono f]` instead of `[Cofibration f]`.

-/

open CategoryTheory HomotopicalAlgebra MorphismProperty Simplicial

universe u

namespace SSet

namespace modelCategoryQuillen

/-- The generating cofibrations: this is the family of morphisms in `SSet`
which consists of boundary inclusions `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]`. -/
def I : MorphismProperty SSet.{u} :=
  .ofHoms (fun n ↦ ∂Δ[n].ι)

lemma boundary_ι_mem_I (n : ℕ) :
    I (boundary.{u} n).ι := by constructor

/-- The generating trivial cofibrations: this is the family of morphisms in `SSet`
which consists of horn inclusions `Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]` (for positive `n`). -/
def J : MorphismProperty SSet.{u} :=
  ⨆ n, .ofHoms (fun (i : Fin (n + 2)) ↦ Λ[n + 1, i].ι)

lemma horn_ι_mem_J (n : ℕ) (i : Fin (n + 2)) :
    J (horn.{u} (n + 1) i).ι := by
  simp only [J, iSup_iff]
  exact ⟨n, ⟨i⟩⟩

lemma I_le_monomorphisms : I.{u} ≤ monomorphisms _ := by
  rintro _ _ _ ⟨n⟩
  exact monomorphisms.infer_property _

lemma J_le_monomorphisms : J.{u} ≤ monomorphisms _ := by
  rintro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  exact monomorphisms.infer_property _

/-- The cofibrations for the Quillen model category structure (TODO)
on `SSet` are monomorphisms. -/
scoped instance : CategoryWithCofibrations SSet.{u} where
  cofibrations := .monomorphisms _

/-- The fibrations for the Quillen model category structure (TODO)
on `SSet` are the morphisms which have the right lifting property
with respect to horn inclusions. -/
scoped instance : CategoryWithFibrations SSet.{u} where
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

instance mono_of_cofibration [Cofibration f] : Mono f := by rwa [← cofibration_iff]

lemma cofibration_of_mono [Mono f] : Cofibration f := by rwa [cofibration_iff]

instance [hf : Fibration f] {n : ℕ} (i : Fin (n + 2)) :
    HasLiftingProperty (horn (n + 1) i).ι f := by
  rw [fibration_iff] at hf
  exact hf _ (horn_ι_mem_J _ _)

end

end modelCategoryQuillen

end SSet
