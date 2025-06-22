import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

open scoped ENNReal

variable (p : ℝ≥0∞)

namespace WithLp

variable (X : Type*) [MeasurableSpace X]

instance measurableSpace : MeasurableSpace (WithLp p X) :=
  MeasurableSpace.map (WithLp.equiv p X).symm inferInstance

@[fun_prop, measurability]
lemma measurable_equiv : Measurable (WithLp.equiv p X) :=
  Measurable.of_comap_le MeasurableSpace.comap_map_le

@[fun_prop, measurability]
lemma measurable_equiv_symm : Measurable (WithLp.equiv p X).symm :=
  Measurable.of_le_map le_rfl

def measurableEquiv : X ≃ᵐ WithLp p X where
  toEquiv := (WithLp.equiv p X).symm
  measurable_toFun := measurable_equiv_symm p X
  measurable_invFun := measurable_equiv p X

lemma coe_measurableEquiv : ⇑(measurableEquiv p X) = ⇑(WithLp.equiv p X).symm := rfl

lemma coe_measurableEquiv_symm : ⇑(measurableEquiv p X).symm = ⇑(WithLp.equiv p X) := rfl

end WithLp
