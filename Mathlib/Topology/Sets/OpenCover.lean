/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Topology.Sets.Opens

/-!
# Open covers
-/

open Set Topology

namespace TopologicalSpace

/-- An indexed family of open sets whose union is `X`. -/
structure OpenCover (ι X : Type*) [TopologicalSpace X] where
  toFun : ι → Opens X
  iSup_eq_top' : iSup toFun = ⊤

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An open cover is a special kind of function into  opens. -/
instance : FunLike (OpenCover ι X) ι (Opens X) :=
  ⟨OpenCover.toFun, fun _ _ ↦ (OpenCover.mk.injEq ..).mpr⟩

namespace OpenCover

@[simp] lemma coe_mk {f : ι → Opens X} (h : iSup f = ⊤) : mk f h = f := rfl

variable (u : OpenCover ι X)

lemma iSup_eq_top : ⨆ i, u i = ⊤ := u.iSup_eq_top'

lemma iSup_set_eq_univ : ⋃ i, (u i : Set X) = univ := by
  simpa [← SetLike.coe_set_eq] using u.iSup_eq_top

/-- Pullback of a covering of `Y` by a continuous map `X → Y`, giving a covering of `X` with the
same index type. -/
def comap (u : OpenCover ι Y) (f : C(X, Y)) : OpenCover ι X :=
  ⟨fun i ↦ (u i).comap f, by simp [← preimage_iUnion, iSup_set_eq_univ]⟩

lemma exists_mem (a : X) : ∃ i, a ∈ u i := by
  simpa [← u.iSup_set_eq_univ] using mem_univ a

lemma exists_mem_nhds (a : X) : ∃ i, (u i : Set X) ∈ 𝓝 a :=
  match u.exists_mem a with | ⟨i, hi⟩ => ⟨i, (u i).isOpen.mem_nhds hi⟩

end OpenCover

end TopologicalSpace
