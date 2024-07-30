/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.Boundary
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The canonical truncation

Given an embedding `e : Embedding c c'` of complex shapes which
satisfies `e.IsTruncGE` and `K : HomologicalComplex C c'`,
we define `K.truncGE' e : HomologicalComplex C c`
and `K.truncGE e : HomologicalComplex C c'` which are the canonical
truncations of `K` relative to `e`.

For example, if `e` is the embedding `embeddingUpIntGE p` of `ComplexShape.up ℕ`
in `ComplexShape.up ℤ` which sends `n : ℕ` to `p + n` and `K : CochainComplex C ℤ`,
then `K.truncGE' e : CochainComplex C ℕ` is the following complex:

`Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where in degree `0`, the object `Q` identifies to the cokernel
of `K.X (p - 1) ⟶ K.X p` (this is `K.opcycles p`). Then, the
cochain complex `K.truncGE e` is indexed by `ℤ`, and has the
following shape:

`... ⟶ 0 ⟶ 0 ⟶ 0 ⟶ Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where `Q` is in degree `p`.

## TODO
* construct a morphism `K.πTruncGE e : K ⟶ K.truncGE e` and show that
it induces an isomorphism in homology in degrees in the image of `e.f`.

-/

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

namespace truncGE'

open Classical in
/-- The `X` field of `truncGE'`. -/
noncomputable def X (i : ι) : C :=
  if e.BoundaryGE i
  then K.opcycles (e.f i)
  else K.X (e.f i)

/-- The isomorphism `truncGE'.X K e i ≅ K.opcycles (e.f i)` when `e.BoundaryGE i` holds.-/
noncomputable def XIsoOpcycles {i : ι} (hi : e.BoundaryGE i) :
    X K e i ≅ K.opcycles (e.f i) :=
  eqToIso (if_pos hi)

/-- The isomorphism `truncGE'.X K e i ≅ K.X (e.f i)` when `e.BoundaryGE i` does not hold.-/
noncomputable def XIso {i : ι} (hi : ¬ e.BoundaryGE i) :
    X K e i ≅ K.X (e.f i) :=
  eqToIso (if_neg hi)

open Classical in
/-- The `d` field of `truncGE'`. -/
noncomputable def d (i j : ι) : X K e i ⟶ X K e j :=
  if hij : c.Rel i j
  then
    if hi : e.BoundaryGE i
    then (truncGE'.XIsoOpcycles K e hi).hom ≫ K.fromOpcycles (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
    else (XIso K e hi).hom ≫ K.d (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
  else 0

@[reassoc (attr := simp)]
lemma d_comp_d (i j k : ι) : d K e i j ≫ d K e j k = 0 := by
  dsimp [d]
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · rw [dif_pos hij, dif_pos hjk, dif_neg (e.not_boundaryGE_next hij)]
      split_ifs <;> simp
    · rw [dif_neg hjk, comp_zero]
  · rw [dif_neg hij, zero_comp]

end truncGE'

/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncGE`. -/
noncomputable def truncGE' : HomologicalComplex C c where
  X := truncGE'.X K e
  d := truncGE'.d K e
  shape _ _ h := dif_neg h

/-- The isomorphism `(K.truncGE' e).X i ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryGE i` does not hold. -/
noncomputable def truncGE'XIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.X i' :=
  (truncGE'.XIso K e hi) ≪≫ eqToIso (by subst hi'; rfl)

/-- The isomorphism `(K.truncGE' e).X i ≅ K.opcycles i'` when `e.f i = i'`
and `e.BoundaryGE i` holds. -/
noncomputable def truncGE'XIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.opcycles i' :=
  (truncGE'.XIsoOpcycles K e hi) ≪≫ eqToIso (by subst hi'; rfl)

lemma truncGE'_d_eq {i j : ι} (hij : c.Rel i j)  {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j')  (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIso e hi' hi).hom ≫ K.d i' j' ≫
      (K.truncGE'XIso e hj' (e.not_boundaryGE_next hij)).inv := by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij, dif_neg hi]
  subst hi' hj'
  simp [truncGE'XIso]

lemma truncGE'_d_eq_fromOpcycles {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hi : e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIsoOpcycles e hi' hi).hom ≫ K.fromOpcycles i' j' ≫
      (K.truncGE'XIso e hj' (e.not_boundaryGE_next hij)).inv := by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij, dif_pos hi]
  subst hi' hj'
  simp [truncGE'XIso, truncGE'XIsoOpcycles]

/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncGE`. -/
noncomputable def truncGE : HomologicalComplex C c' := (K.truncGE' e).extend e

/-- The isomorphism `(K.truncGE e).X i' ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryGE i` does not hold. -/
noncomputable def truncGEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.X i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIso e hi' hi

/-- The isomorphism `(K.truncGE e).X i' ≅ K.opcycles i'` when `e.f i = i'`
and `e.BoundaryGE i` holds. -/
noncomputable def truncGEXIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.opcycles i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIsoOpcycles e hi' hi

end HomologicalComplex
