/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Heather Macbeth
-/
import Mathlib.Data.Matrix.Defs
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.UniformSpace.Pi

/-!
# Uniform space structure on matrices
-/


open Uniformity Topology

variable (m n 𝕜 : Type*) [UniformSpace 𝕜]

namespace Matrix

instance instUniformSpace : UniformSpace (Matrix m n 𝕜) :=
  (by infer_instance : UniformSpace (m → n → 𝕜))

instance instIsUniformAddGroup [AddGroup 𝕜] [IsUniformAddGroup 𝕜] :
    IsUniformAddGroup (Matrix m n 𝕜) :=
  inferInstanceAs <| IsUniformAddGroup (m → n → 𝕜)

@[deprecated (since := "2025-03-31")] alias
  instUniformAddGroup := Matrix.instIsUniformAddGroup

theorem uniformity :
    𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap fun a => (a.1 i j, a.2 i j) := by
  erw [Pi.uniformity]
  simp_rw [Pi.uniformity, Filter.comap_iInf, Filter.comap_comap]
  rfl

theorem uniformContinuous {β : Type*} [UniformSpace β] {f : β → Matrix m n 𝕜} :
    UniformContinuous f ↔ ∀ i j, UniformContinuous fun x => f x i j := by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_iInf, Filter.tendsto_comap_iff]
  apply Iff.intro <;> intro a <;> apply a

instance [CompleteSpace 𝕜] : CompleteSpace (Matrix m n 𝕜) :=
  (by infer_instance : CompleteSpace (m → n → 𝕜))

instance [T0Space 𝕜] : T0Space (Matrix m n 𝕜) :=
  inferInstanceAs (T0Space (m → n → 𝕜))

end Matrix
