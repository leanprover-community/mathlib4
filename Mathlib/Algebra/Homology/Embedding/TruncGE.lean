import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace CategoryTheory.Limits.IsZero

variable {X : C} (hX : IsZero X)

lemma epi {Y : C} (f : Y ⟶ X) : Epi f where
  left_cancellation := by intros; apply hX.eq_of_src

lemma mono {Y : C} (f : X ⟶ Y) : Mono f where
  right_cancellation := by intros; apply hX.eq_of_tgt

end CategoryTheory.Limits.IsZero

namespace HomologicalComplex

variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i']

namespace truncGE'

open Classical in
noncomputable def X (i : ι) : C :=
  if e.BoundaryGE i
  then K.opcycles (e.f i)
  else K.X (e.f i)

noncomputable def XIsoOpcycles {i : ι} (hi : e.BoundaryGE i) :
    X K e i ≅ K.opcycles (e.f i) :=
  eqToIso (if_pos hi)

noncomputable def XIso {i : ι} (hi : ¬ e.BoundaryGE i) :
    X K e i ≅ K.X (e.f i) :=
  eqToIso (if_neg hi)

open Classical in
noncomputable def d (i j : ι) : X K e i ⟶ X K e j :=
  if hij : c.Rel i j
  then
    if hi : e.BoundaryGE i
    then (truncGE'.XIsoOpcycles K e hi).hom ≫ K.fromOpcycles (e.f i) (e.f j) ≫
      (XIso K e (e.not_mem_next_boundaryGE hij)).inv
    else (XIso K e hi).hom ≫ K.d (e.f i) (e.f j) ≫
      (XIso K e (e.not_mem_next_boundaryGE hij)).inv
  else 0

@[reassoc (attr := simp)]
lemma d_comp_d (i j k : ι) : d K e i j ≫ d K e j k = 0 := by
  dsimp [d]
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · rw [dif_pos hij, dif_pos hjk, dif_neg (e.not_mem_next_boundaryGE hij)]
      split_ifs <;> simp
    · rw [dif_neg hjk, comp_zero]
  · rw [dif_neg hij, zero_comp]

end truncGE'

noncomputable def truncGE' : HomologicalComplex C c where
  X := truncGE'.X K e
  d := truncGE'.d K e
  shape _ _ h := dif_neg h

noncomputable def truncGE'XIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.X i' :=
  (truncGE'.XIso K e hi) ≪≫ eqToIso (by subst hi'; rfl)

noncomputable def truncGE'XIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.opcycles i' :=
  (truncGE'.XIsoOpcycles K e hi) ≪≫ eqToIso (by subst hi'; rfl)

lemma truncGE'_d_eq {i j : ι} (hij : c.Rel i j)  {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j')  (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIso e hi' hi).hom ≫ K.d i' j' ≫
      (K.truncGE'XIso e hj' (e.not_mem_next_boundaryGE hij)).inv := by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij, dif_neg hi]
  subst hi' hj'
  simp [truncGE'XIso]

lemma truncGE'_d_eq_fromOpcycles {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hi : e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIsoOpcycles e hi' hi).hom ≫ K.fromOpcycles i' j' ≫
      (K.truncGE'XIso e hj' (e.not_mem_next_boundaryGE hij)).inv := by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij, dif_pos hi]
  subst hi' hj'
  simp [truncGE'XIso, truncGE'XIsoOpcycles]

noncomputable def truncGE : HomologicalComplex C c' := (K.truncGE' e).extend e

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

end HomologicalComplex
