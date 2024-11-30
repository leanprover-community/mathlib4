<<<<<<< HEAD
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Algebra.Homology.QuasiIso
=======
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
>>>>>>> origin/ext-change-of-universes

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
<<<<<<< HEAD
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace CategoryTheory.Limits.IsZero

variable {X : C} (hX : IsZero X)

lemma epi {Y : C} (f : Y ⟶ X) : Epi f where
  left_cancellation := by intros; apply hX.eq_of_src

lemma mono {Y : C} (f : X ⟶ Y) : Mono f where
  right_cancellation := by intros; apply hX.eq_of_tgt

end CategoryTheory.Limits.IsZero
=======
  {C : Type*} [Category C] [HasZeroMorphisms C]
>>>>>>> origin/ext-change-of-universes

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

namespace truncGE'

open Classical in
<<<<<<< HEAD
=======
/-- The `X` field of `truncGE'`. -/
>>>>>>> origin/ext-change-of-universes
noncomputable def X (i : ι) : C :=
  if e.BoundaryGE i
  then K.opcycles (e.f i)
  else K.X (e.f i)

<<<<<<< HEAD
=======
/-- The isomorphism `truncGE'.X K e i ≅ K.opcycles (e.f i)` when `e.BoundaryGE i` holds.-/
>>>>>>> origin/ext-change-of-universes
noncomputable def XIsoOpcycles {i : ι} (hi : e.BoundaryGE i) :
    X K e i ≅ K.opcycles (e.f i) :=
  eqToIso (if_pos hi)

<<<<<<< HEAD
=======
/-- The isomorphism `truncGE'.X K e i ≅ K.X (e.f i)` when `e.BoundaryGE i` does not hold.-/
>>>>>>> origin/ext-change-of-universes
noncomputable def XIso {i : ι} (hi : ¬ e.BoundaryGE i) :
    X K e i ≅ K.X (e.f i) :=
  eqToIso (if_neg hi)

open Classical in
<<<<<<< HEAD
=======
/-- The `d` field of `truncGE'`. -/
>>>>>>> origin/ext-change-of-universes
noncomputable def d (i j : ι) : X K e i ⟶ X K e j :=
  if hij : c.Rel i j
  then
    if hi : e.BoundaryGE i
    then (truncGE'.XIsoOpcycles K e hi).hom ≫ K.fromOpcycles (e.f i) (e.f j) ≫
<<<<<<< HEAD
      (XIso K e (e.not_mem_next_boundaryGE hij)).inv
    else (XIso K e hi).hom ≫ K.d (e.f i) (e.f j) ≫
      (XIso K e (e.not_mem_next_boundaryGE hij)).inv
=======
      (XIso K e (e.not_boundaryGE_next hij)).inv
    else (XIso K e hi).hom ≫ K.d (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
>>>>>>> origin/ext-change-of-universes
  else 0

@[reassoc (attr := simp)]
lemma d_comp_d (i j k : ι) : d K e i j ≫ d K e j k = 0 := by
  dsimp [d]
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
<<<<<<< HEAD
    · rw [dif_pos hij, dif_pos hjk, dif_neg (e.not_mem_next_boundaryGE hij)]
=======
    · rw [dif_pos hij, dif_pos hjk, dif_neg (e.not_boundaryGE_next hij)]
>>>>>>> origin/ext-change-of-universes
      split_ifs <;> simp
    · rw [dif_neg hjk, comp_zero]
  · rw [dif_neg hij, zero_comp]

end truncGE'

<<<<<<< HEAD
=======
/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncGE`. -/
>>>>>>> origin/ext-change-of-universes
noncomputable def truncGE' : HomologicalComplex C c where
  X := truncGE'.X K e
  d := truncGE'.d K e
  shape _ _ h := dif_neg h

<<<<<<< HEAD
=======
/-- The isomorphism `(K.truncGE' e).X i ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryGE i` does not hold. -/
>>>>>>> origin/ext-change-of-universes
noncomputable def truncGE'XIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.X i' :=
  (truncGE'.XIso K e hi) ≪≫ eqToIso (by subst hi'; rfl)

<<<<<<< HEAD
=======
/-- The isomorphism `(K.truncGE' e).X i ≅ K.opcycles i'` when `e.f i = i'`
and `e.BoundaryGE i` holds. -/
>>>>>>> origin/ext-change-of-universes
noncomputable def truncGE'XIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.opcycles i' :=
  (truncGE'.XIsoOpcycles K e hi) ≪≫ eqToIso (by subst hi'; rfl)

<<<<<<< HEAD
lemma truncGE'_d_eq {i j : ι} (hij : c.Rel i j)  {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j')  (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIso e hi' hi).hom ≫ K.d i' j' ≫
      (K.truncGE'XIso e hj' (e.not_mem_next_boundaryGE hij)).inv := by
=======
lemma truncGE'_d_eq {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIso e hi' hi).hom ≫ K.d i' j' ≫
      (K.truncGE'XIso e hj' (e.not_boundaryGE_next hij)).inv := by
>>>>>>> origin/ext-change-of-universes
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij, dif_neg hi]
  subst hi' hj'
  simp [truncGE'XIso]

lemma truncGE'_d_eq_fromOpcycles {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hi : e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIsoOpcycles e hi' hi).hom ≫ K.fromOpcycles i' j' ≫
<<<<<<< HEAD
      (K.truncGE'XIso e hj' (e.not_mem_next_boundaryGE hij)).inv := by
=======
      (K.truncGE'XIso e hj' (e.not_boundaryGE_next hij)).inv := by
>>>>>>> origin/ext-change-of-universes
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij, dif_pos hi]
  subst hi' hj'
  simp [truncGE'XIso, truncGE'XIsoOpcycles]

<<<<<<< HEAD
noncomputable def truncGE : HomologicalComplex C c' := (K.truncGE' e).extend e

=======
variable [HasZeroObject C]

/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncGE`. -/
noncomputable def truncGE : HomologicalComplex C c' := (K.truncGE' e).extend e

/-- The isomorphism `(K.truncGE e).X i' ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryGE i` does not hold. -/
>>>>>>> origin/ext-change-of-universes
noncomputable def truncGEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.X i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIso e hi' hi

<<<<<<< HEAD
=======
/-- The isomorphism `(K.truncGE e).X i' ≅ K.opcycles i'` when `e.f i = i'`
and `e.BoundaryGE i` holds. -/
>>>>>>> origin/ext-change-of-universes
noncomputable def truncGEXIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.opcycles i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIsoOpcycles e hi' hi

<<<<<<< HEAD
section

variable {K L M}

open Classical in
noncomputable def truncGE'Map : K.truncGE' e ⟶ L.truncGE' e where
  f i :=
    if hi : e.BoundaryGE i
    then
      (K.truncGE'XIsoOpcycles e rfl hi).hom ≫ opcyclesMap φ (e.f i) ≫
        (L.truncGE'XIsoOpcycles e rfl hi).inv
    else
      (K.truncGE'XIso e rfl hi).hom ≫ φ.f (e.f i) ≫ (L.truncGE'XIso e rfl hi).inv
  comm' i j hij := by
    dsimp
    rw [dif_neg (e.not_mem_next_boundaryGE hij)]
    by_cases hi : e.BoundaryGE i
    · rw [dif_pos hi]
      simp [truncGE'_d_eq_fromOpcycles _ e hij rfl rfl hi,
        ← cancel_epi (K.pOpcycles (e.f i))]
    · rw [dif_neg hi]
      simp [truncGE'_d_eq _ e hij rfl rfl hi]

lemma truncGE'Map_f_eq_opcyclesMap {i : ι} (hi : e.BoundaryGE i) {i' : ι'} (h : e.f i = i') :
    (truncGE'Map φ e).f i =
      (K.truncGE'XIsoOpcycles e h hi).hom ≫ opcyclesMap φ i' ≫
        (L.truncGE'XIsoOpcycles e h hi).inv := by
  subst h
  exact dif_pos hi

lemma truncGE'Map_f_eq {i : ι} (hi : ¬ e.BoundaryGE i) {i' : ι'} (h : e.f i = i') :
    (truncGE'Map φ e).f i =
      (K.truncGE'XIso e h hi).hom ≫ φ.f i' ≫ (L.truncGE'XIso e h hi).inv := by
  subst h
  exact dif_neg hi

variable (K) in
@[simp]
lemma truncGE'Map_id : truncGE'Map (𝟙 K) e = 𝟙 _ := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl]
  · simp [truncGE'Map_f_eq _ _ hi rfl]

@[reassoc, simp]
lemma truncGE'Map_comp : truncGE'Map (φ ≫ φ') e = truncGE'Map φ e ≫ truncGE'Map φ' e := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl, opcyclesMap_comp]
  · simp [truncGE'Map_f_eq _ _ hi rfl]

noncomputable def truncGEMap : K.truncGE e ⟶ L.truncGE e :=
  (e.extendFunctor C).map (truncGE'Map φ e)

variable (K) in
@[simp]
lemma truncGEMap_id : truncGEMap (𝟙 K) e = 𝟙 _ := by
  simp [truncGEMap, truncGE]

@[reassoc, simp]
lemma truncGEMap_comp : truncGEMap (φ ≫ φ') e = truncGEMap φ e ≫ truncGEMap φ' e := by
  simp [truncGEMap, truncGE]

end

namespace restrictionToTruncGE'

open Classical in
noncomputable def f (i : ι) : (K.restriction e).X i ⟶ (K.truncGE' e).X i :=
  if hi : e.BoundaryGE i
  then
    K.pOpcycles _ ≫ (K.truncGE'XIsoOpcycles e rfl hi).inv
  else
    (K.truncGE'XIso e rfl hi).inv

lemma f_eq_pOpcycles_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    f K e i = (K.restrictionXIso e hi').hom ≫ K.pOpcycles i' ≫
      (K.truncGE'XIsoOpcycles e hi' hi).inv := by
  dsimp [f]
  rw [dif_pos hi]
  subst hi'
  simp [restrictionXIso]

lemma f_eq_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    f K e i = (K.restrictionXIso e hi').hom ≫ (K.truncGE'XIso e hi' hi).inv := by
  dsimp [f]
  rw [dif_neg hi]
  subst hi'
  simp [restrictionXIso]

@[reassoc (attr := simp)]
lemma comm (i j : ι) :
    f K e i ≫ (K.truncGE' e).d i j = (K.restriction e).d i j ≫ f K e j := by
  by_cases hij : c.Rel i j
  · by_cases hi : e.BoundaryGE i
    · rw [f_eq_pOpcycles_iso_inv K e rfl hi, f_eq_iso_inv K e rfl (e.not_mem_next_boundaryGE hij),
        K.truncGE'_d_eq_fromOpcycles e hij rfl rfl hi]
      simp [restrictionXIso]
    · rw [f_eq_iso_inv K e rfl hi, f_eq_iso_inv K e rfl (e.not_mem_next_boundaryGE hij),
        K.truncGE'_d_eq e hij rfl rfl hi]
      simp [restrictionXIso]
  · simp [HomologicalComplex.shape _ _ _ hij]

end restrictionToTruncGE'

noncomputable def restrictionToTruncGE' : K.restriction e ⟶ K.truncGE' e where
  f := restrictionToTruncGE'.f K e

lemma restrictionToTruncGE'_hasLift : e.HasLift (K.restrictionToTruncGE' e) := by
  intro j hj i' _
  dsimp [restrictionToTruncGE']
  rw [restrictionToTruncGE'.f_eq_pOpcycles_iso_inv K e rfl hj]
  simp [restrictionXIso]

lemma restrictionToTruncGE'_f_eq_pOpcycles_iso_inv
    {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.restrictionToTruncGE' e).f i = (K.restrictionXIso e hi').hom ≫ K.pOpcycles i' ≫
      (K.truncGE'XIsoOpcycles e hi' hi).inv := by
  apply restrictionToTruncGE'.f_eq_pOpcycles_iso_inv

lemma restrictionToTruncGE'_f_eq_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.restrictionToTruncGE' e).f i =
      (K.restrictionXIso e hi').hom ≫ (K.truncGE'XIso e hi' hi).inv := by
  apply restrictionToTruncGE'.f_eq_iso_inv

lemma isIso_restrictionToTruncGE' (i : ι) (hi : ¬ e.BoundaryGE i) :
    IsIso ((K.restrictionToTruncGE' e).f i) := by
  rw [K.restrictionToTruncGE'_f_eq_iso_inv e rfl hi]
  infer_instance

variable {K L} in
@[reassoc (attr := simp)]
lemma restrictionToTruncGE'_naturality :
    K.restrictionToTruncGE' e ≫ truncGE'Map φ e =
      restrictionMap φ e ≫ L.restrictionToTruncGE' e := by
  ext i
  dsimp
  by_cases hi : e.BoundaryGE i
  · simp [restrictionToTruncGE'_f_eq_pOpcycles_iso_inv _ e rfl hi,
      truncGE'Map_f_eq_opcyclesMap φ e hi rfl, restrictionXIso]
  · simp [restrictionToTruncGE'_f_eq_iso_inv _ e rfl hi,
      truncGE'Map_f_eq φ e hi rfl, restrictionXIso]

attribute [local instance] epi_comp

instance (i : ι) : Epi ((K.restrictionToTruncGE' e).f i) := by
  by_cases hi : e.BoundaryGE i
  · rw [K.restrictionToTruncGE'_f_eq_pOpcycles_iso_inv e rfl hi]
    infer_instance
  · have := K.isIso_restrictionToTruncGE' e i hi
    infer_instance

noncomputable def πTruncGE : K ⟶ K.truncGE e :=
  e.liftExtend (K.restrictionToTruncGE' e) (K.restrictionToTruncGE'_hasLift e)

instance (i' : ι') : Epi ((K.πTruncGE e).f i') := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    dsimp [πTruncGE]
    rw [e.epi_liftExtend_f_iff _ _ hi]
    infer_instance
  · apply (isZero_extend_X _ _ _ (by simpa using hi')).epi

instance : Epi (K.πTruncGE e) := epi_of_epi_f _ (fun _ => inferInstance)

instance : (K.truncGE e).IsStrictlySupported e := by
  dsimp [truncGE]
  infer_instance

variable {K L} in
@[reassoc (attr := simp)]
lemma πTruncGE_naturality :
    K.πTruncGE e ≫ truncGEMap φ e = φ ≫ L.πTruncGE e := by
  apply (e.homEquiv _ _).injective
  ext1
  dsimp [truncGEMap, πTruncGE]
  rw [e.homRestrict_comp_extend, e.homRestrict_liftExtend, e.homRestrict_precomp,
    e.homRestrict_liftExtend, restrictionToTruncGE'_naturality]

instance {ι'' : Type*} {c'' : ComplexShape ι''} (e' : c''.Embedding c')
    [K.IsStrictlySupported e'] : (K.truncGE e).IsStrictlySupported e' where
  isZero := by
    intro i' hi'
    by_cases hi'' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi''
      by_cases hi''' : e.BoundaryGE i
      · rw [IsZero.iff_id_eq_zero, ← cancel_epi
          ((K.truncGE' e).extendXIso e hi ≪≫ K.truncGE'XIsoOpcycles e hi hi''').inv,
          ← cancel_epi (HomologicalComplex.pOpcycles _ _)]
        apply (K.isZero_X_of_isStrictlySupported e' i' hi').eq_of_src
      · exact (K.isZero_X_of_isStrictlySupported e' i' hi').of_iso
          ((K.truncGE' e).extendXIso e hi ≪≫ K.truncGE'XIso e hi hi''')
    · exact (K.truncGE e).isZero_X_of_isStrictlySupported e _ (by simpa using hi'')

instance [K.IsStrictlySupported e] (i : ι) : IsIso ((K.restrictionToTruncGE' e).f i) := by
  by_cases hi : e.BoundaryGE i
  · rw [K.restrictionToTruncGE'_f_eq_pOpcycles_iso_inv e rfl hi]
    have : IsIso (K.pOpcycles (e.f i)) := K.isIso_pOpcycles _ _ rfl (by
      obtain ⟨hi₁, hi₂⟩ := hi
      apply IsZero.eq_of_src
      apply K.isZero_X_of_isStrictlySupported e
      intro j hj
      apply hi₂ j
      rw [hj]
      exact hi₁)
    infer_instance
  · rw [K.restrictionToTruncGE'_f_eq_iso_inv e rfl hi]
    infer_instance

instance [K.IsStrictlySupported e] : IsIso (K.πTruncGE e) := by
  suffices ∀ (i' : ι'), IsIso ((K.πTruncGE e).f i') by
    apply Hom.isIso_of_components
  intro i'
  by_cases hn : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hn
    dsimp [πTruncGE]
    rw [e.isIso_liftExtend_f_iff _ _ hi]
    infer_instance
  · simp only [not_exists] at hn
    refine' ⟨0, _, _⟩
    all_goals
      apply (isZero_X_of_isStrictlySupported _ e i' hn).eq_of_src

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') [e.IsTruncGE]
    (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C] [CategoryWithHomology C]

@[simps]
noncomputable def truncGE'Functor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.truncGE' e
  map φ := HomologicalComplex.truncGE'Map φ e

@[simps]
noncomputable def restrictionToTruncGE'NatTrans :
    e.restrictionFunctor C ⟶ e.truncGE'Functor C where
  app K := K.restrictionToTruncGE' e

@[simps]
noncomputable def truncGEFunctor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.truncGE e
  map φ := HomologicalComplex.truncGEMap φ e

@[simps]
noncomputable def πTruncGENatTrans : 𝟭 _ ⟶ e.truncGEFunctor C where
  app K := K.πTruncGE e

end ComplexShape.Embedding
=======
end HomologicalComplex
>>>>>>> origin/ext-change-of-universes
