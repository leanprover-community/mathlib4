/-
Copyright (c) 2026 Juanjo Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juanjo Madrigal
-/
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# The space `ω₁`

The space `ω₁` with the order topology, a source of many counterexamples in general topology.
We follow [Munkres2000], where this space is denoted `S_Ω`.

## References

* [J. Munkres, *Topology*][Munkres2000]
-/

open scoped Cardinal Ordinal

namespace Omega1Space

private abbrev A₁ : Type := (ℵ₁).ord.ToType

/-- The closure $\overline{S_Ω}$, as a type. -/
@[reducible] def SΩC : Type := WithTop A₁

/-- The greatest element `Ω`. -/
def Ω : SΩC := ⊤

/-- The section below an element. -/
def sec : SΩC → Set SΩC := Set.Iio

/-- $S_Ω$, as a set. -/
def SΩ_ : Set SΩC := sec Ω

/-- $S_Ω$, as a type. -/
@[reducible] def SΩ : Type := SΩ_

private noncomputable def A₁_emb : A₁ ↪o SΩC := WithTop.coeOrderHom
private lemma A₁_emb_range : Set.range A₁_emb = SΩ_ := by
  rw [A₁_emb]
  exact WithTop.range_coe

private noncomputable def A₁OrderIsoSΩ : A₁ ≃o SΩ :=
  OrderEmbedding.orderIso.trans (OrderIso.setCongr _ _ A₁_emb_range)

private lemma mk_A₁ : #A₁ = ℵ₁ := Cardinal.mk_ord_toType _

instance : Uncountable A₁ :=
  Cardinal.aleph0_lt_mk_iff.mp <| by rw [mk_A₁]; exact Cardinal.aleph0_lt_aleph_one

instance : Uncountable SΩ := A₁OrderIsoSΩ.injective.uncountable

/-- $S_Ω$ is uncountable. -/
theorem uncountable_section : ¬ SΩ_.Countable := not_countable (α := SΩ)

private lemma A₁_Iio_countable (i : A₁) : (Set.Iio i).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, ← Cardinal.lt_aleph_one_iff]
  have hord : Cardinal.ord #A₁ = typeLT A₁ := by rw [mk_A₁, Ordinal.type_toType]
  have h := Cardinal.mk_Iio_lt i hord
  rwa [mk_A₁] at h

/-- Each proper section of $S_Ω$ is countable. -/
theorem countable_section (x : SΩC) (hx : x < Ω) : (sec x).Countable := by
  lift x to A₁ using hx.ne with i
  simp only [sec, WithTop.Iio_coe]
  exact (A₁_Iio_countable i).image _

end Omega1Space
