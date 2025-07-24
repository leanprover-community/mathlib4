/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurable space structure on `WithLp`

If `X` is a measurable space, we set the measurable space structure on `WithLp p X` to be the
same as the one on `X`.
-/

open scoped ENNReal

variable (p : ℝ≥0∞) (X : Type*) [MeasurableSpace X]

namespace WithLp

instance measurableSpace : MeasurableSpace (WithLp p X) :=
  MeasurableSpace.comap WithLp.ofLp inferInstance

@[fun_prop, measurability]
lemma measurable_ofLp : Measurable (@WithLp.ofLp p X) := comap_measurable _

@[deprecated measurable_ofLp (since := "2024-04-27")]
lemma measurable_equiv : Measurable (WithLp.equiv p X) := measurable_ofLp p X

@[fun_prop, measurability]
lemma measurable_toLp : Measurable (@WithLp.toLp p X) := fun s hs ↦ by
  obtain ⟨t, ht, rfl⟩ := hs
  simpa [Set.preimage_preimage]

@[deprecated measurable_toLp (since := "2024-04-27")]
lemma measurable_equiv_symm : Measurable (WithLp.equiv p X).symm := measurable_toLp p X

variable (Y : Type*) [MeasurableSpace Y] [TopologicalSpace X] [TopologicalSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopologyEither X Y]

instance borelSpace : BorelSpace (WithLp p (X × Y)) where
  measurable_eq := by
    rw [instProdTopologicalSpace, borel_comap, measurableSpace,
      BorelSpace.measurable_eq (α := X × Y)]

end WithLp

namespace PiLp

variable {ι : Type*} {X : ι → Type*} [Countable ι] [∀ i, MeasurableSpace (X i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

instance borelSpace : BorelSpace (PiLp p X) where
  measurable_eq := by
    rw [topologicalSpace, borel_comap, WithLp.measurableSpace,
      BorelSpace.measurable_eq (α := Π i, X i)]

end PiLp

namespace MeasurableEquiv

/-- The map from `X` to `WithLp p X` as a measurable equivalence. -/
protected def toLp : X ≃ᵐ (WithLp p X) where
  toEquiv := (WithLp.equiv p X).symm
  measurable_toFun := WithLp.measurable_toLp p X
  measurable_invFun := WithLp.measurable_ofLp p X

lemma coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithLp.toLp p := rfl

lemma coe_toLp_symm : ⇑(MeasurableEquiv.toLp p X).symm = WithLp.ofLp := rfl

@[simp]
lemma toLp_apply (x : X) : MeasurableEquiv.toLp p X x = WithLp.toLp p x := rfl

@[simp]
lemma toLp_symm_apply (x : WithLp p X) :
    (MeasurableEquiv.toLp p X).symm x = WithLp.ofLp x := rfl

end MeasurableEquiv
