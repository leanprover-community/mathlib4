/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.Embedding.TruncLE

/-! # The homology of a canonical truncation

Given an embedding of complex shapes `e : Embedding c c'`,
we relate the homology of `K : HomologicalComplex C c'` and of
`K.truncLE e : HomologicalComplex C c'`.

The main result is that `K.ιTruncLE e : K.truncLE e ⟶ K` induces a
quasi-isomorphism in degree `e.f i` for all `i`. (Note that the complex
`K.truncLE e` is exact in degrees that are not in the image of `e.f`.)

All the results are obtained by dualising the results in the file `Embedding.TruncGEHomology`.

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

namespace truncLE'

/-- `K.truncLE'ToRestriction e` is a quasi-isomorphism in degrees that are not at the boundary. -/
lemma quasiIsoAt_truncLE'ToRestriction (j : ι) (hj : ¬ e.BoundaryLE j)
    [(K.restriction e).HasHomology j] [(K.truncLE' e).HasHomology j] :
    QuasiIsoAt (K.truncLE'ToRestriction e) j := by
  dsimp only [truncLE'ToRestriction]
  have : (K.op.restriction e.op).HasHomology j :=
    inferInstanceAs ((K.restriction e).op.HasHomology j)
  rw [quasiIsoAt_unopFunctor_map_iff]
  exact truncGE'.quasiIsoAt_restrictionToTruncGE' K.op e.op j (by simpa)

instance truncLE'_hasHomology (i : ι) : (K.truncLE' e).HasHomology i :=
  inferInstanceAs ((K.op.truncGE' e.op).unop.HasHomology i)

end truncLE'

variable [HasZeroObject C]

instance (i' : ι') : (K.truncLE e).HasHomology i' :=
  inferInstanceAs ((K.op.truncGE e.op).unop.HasHomology i')

lemma quasiIsoAt_ιTruncLE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.ιTruncLE e) j' := by
  have := K.op.quasiIsoAt_πTruncGE e.op hj'
  exact inferInstanceAs (QuasiIsoAt ((unopFunctor _ _ ).map (K.op.πTruncGE e.op).op) j')

instance (i : ι) : QuasiIsoAt (K.ιTruncLE e) (e.f i) := K.quasiIsoAt_ιTruncLE e rfl

lemma quasiIso_ιTruncLE_iff_isSupported :
    QuasiIso (K.ιTruncLE e) ↔ K.IsSupported e := by
  rw [← quasiIso_opFunctor_map_iff, ← isSupported_op_iff]
  exact K.op.quasiIso_πTruncGE_iff_isSupported e.op

lemma acyclic_truncLE_iff_isSupportedOutside :
    (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e := by
  rw [← acyclic_op_iff, ← isSupportedOutside_op_iff]
  exact K.op.acyclic_truncGE_iff_isSupportedOutside e.op

variable {K L}

lemma quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ e) ↔ ∀ (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by
  rw [← quasiIso_opFunctor_map_iff]
  simp only [← quasiIsoAt_opFunctor_map_iff φ]
  apply quasiIso_truncGEMap_iff

end HomologicalComplex
