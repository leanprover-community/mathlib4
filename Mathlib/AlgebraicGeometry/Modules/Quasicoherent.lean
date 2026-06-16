/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!

# QC

-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{u}} (M : X.Modules)

namespace AlgebraicGeometry.Scheme.Modules

lemma isQuasicoherent_restrict_iff {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    (M.restrict f).IsQuasicoherent ↔ (M.over f.opensRange).IsQuasicoherent := sorry

variable (𝓤 : OpenCover.{u} X)

lemma _root_.AlgebraicGeometry.Scheme.OpenCover.coversTop : (Opens.grothendieckTopology X).CoversTop
    (fun i : 𝓤.I₀ => (𝓤.f i).opensRange) := by
  intro W x hx
  have hx' : x ∈ (⊤ : X.Opens) := trivial
  rw [← 𝓤.iSup_opensRange, TopologicalSpace.Opens.mem_iSup] at hx'
  obtain ⟨i, hi⟩ := hx'
  refine ⟨(𝓤.f i).opensRange ⊓ W, homOfLE inf_le_right, ?_, ⟨hi, hx⟩⟩
  rw [Sieve.mem_ofObjects_iff]
  exact ⟨i, ⟨homOfLE inf_le_left⟩⟩

theorem isQuasiCoherent_of_open_cover
    (h : ∀ i, (M.restrict (𝓤.f i)).IsQuasicoherent) : M.IsQuasicoherent :=
  have _ i : (M.over (𝓤.f i).opensRange).IsQuasicoherent := by
    rw [← isQuasicoherent_restrict_iff]
    exact h i
  SheafOfModules.IsQuasicoherent.of_coversTop M (fun i : 𝓤.I₀ => (𝓤.f i).opensRange) 𝓤.coversTop

end AlgebraicGeometry.Scheme.Modules
