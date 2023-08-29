/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Heather Macbeth
-/
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Data.Matrix.Basic

#align_import topology.uniform_space.matrix from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Uniform space structure on matrices
-/


open Uniformity Topology

variable (m n 𝕜 : Type*) [UniformSpace 𝕜]

namespace Matrix

instance : UniformSpace (Matrix m n 𝕜) :=
  (by infer_instance : UniformSpace (m → n → 𝕜))
      -- 🎉 no goals

theorem uniformity :
    𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap fun a => (a.1 i j, a.2 i j) := by
  erw [Pi.uniformity, Pi.uniformity]
  -- ⊢ ⨅ (i : m), Filter.comap (fun a => (Prod.fst a i, Prod.snd a i)) (⨅ (i : n),  …
  simp_rw [Filter.comap_iInf, Filter.comap_comap]
  -- ⊢ ⨅ (i : m) (i_1 : n), Filter.comap ((fun a => (Prod.fst a i_1, Prod.snd a i_1 …
  rfl
  -- 🎉 no goals
#align matrix.uniformity Matrix.uniformity

theorem uniformContinuous {β : Type*} [UniformSpace β] {f : β → Matrix m n 𝕜} :
    UniformContinuous f ↔ ∀ i j, UniformContinuous fun x => f x i j := by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_iInf, Filter.tendsto_comap_iff]
  -- ⊢ (∀ (i : m) (i_1 : n), Filter.Tendsto ((fun a => (Prod.fst a i i_1, Prod.snd  …
  apply Iff.intro <;> intro a <;> apply a
  -- ⊢ (∀ (i : m) (i_1 : n), Filter.Tendsto ((fun a => (Prod.fst a i i_1, Prod.snd  …
                      -- ⊢ ∀ (i : m) (j : n), Filter.Tendsto (fun x => (f x.fst i j, f x.snd i j)) (𝓤 β …
                      -- ⊢ ∀ (i : m) (i_1 : n), Filter.Tendsto ((fun a => (Prod.fst a i i_1, Prod.snd a …
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align matrix.uniform_continuous Matrix.uniformContinuous

instance [CompleteSpace 𝕜] : CompleteSpace (Matrix m n 𝕜) :=
  (by infer_instance : CompleteSpace (m → n → 𝕜))
      -- 🎉 no goals

instance [SeparatedSpace 𝕜] : SeparatedSpace (Matrix m n 𝕜) :=
  (by infer_instance : SeparatedSpace (m → n → 𝕜))
      -- 🎉 no goals

end Matrix
