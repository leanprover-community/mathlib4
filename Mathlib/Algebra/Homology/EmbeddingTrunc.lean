import Mathlib.Algebra.Homology.Embedding
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace ComplexShape.Embedding

variable (e : c.Embedding c')

def BoundaryGE (j : ι) : Prop :=
  c'.Rel (c'.prev (e.f j)) (e.f j) ∧ ∀ i, ¬c'.Rel (e.f i) (e.f j)

lemma not_mem_next_boundaryGE [e.IsRelIff] {j k : ι} (hk : c.Rel j k) :
    ¬ e.BoundaryGE k := by
  dsimp [BoundaryGE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [← e.rel_iff] using hk⟩

lemma mem_boundaryGE {i' : ι'} {j : ι} (hj : c'.Rel i' (e.f j))
    (hi' : ∀ i, e.f i ≠ i') :
    e.BoundaryGE j := by
  constructor
  · simpa only [c'.prev_eq' hj] using hj
  · intro i hi
    apply hi' i
    rw [← c'.prev_eq' hj, c'.prev_eq' hi]

end ComplexShape.Embedding

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

lemma isZero_truncGE_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.truncGE e).X i') :=
  (K.truncGE' e).isZero_extend_X _ _ hi'

noncomputable def truncGEXIsoOpcycles {i' : ι'} {i : ι} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.opcycles i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ truncGE'.XIsoOpcycles K e hi ≪≫
    eqToIso (by subst hi'; rfl)

noncomputable def truncGEXIso {i' : ι'} {i : ι} (hi' : e.f i = i') (hi : ¬e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.X i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ truncGE'.XIso K e hi ≪≫
    eqToIso (by subst hi'; rfl)

lemma truncGE_d_eq {i' j' : ι'} {i j : ι} (hij : c.Rel i j)
    (hi' : e.f i = i') (hj' : e.f j = j')
    (hi : ¬ e.BoundaryGE i) :
    (K.truncGE e).d i' j' = (K.truncGEXIso e hi' hi).hom ≫ K.d i' j' ≫
      (K.truncGEXIso e hj' (by
        subst hi' hj'
        exact e.not_mem_next_boundaryGE hij)).inv := by
  dsimp only [truncGE]
  rw [(K.truncGE' e).extend_d_eq e hi' hj', K.truncGE'_d_eq e hij hi' hj' hi]
  simp [truncGE'XIso, truncGEXIso]

lemma truncGE_d_eq_fromOpcycles {i' j' : ι'} {i j : ι} (hij : c.Rel i j)
    (hi' : e.f i = i') (hj' : e.f j = j')
    (hi : e.BoundaryGE i) :
    (K.truncGE e).d i' j' = (K.truncGEXIsoOpcycles e hi' hi).hom ≫ K.fromOpcycles i' j' ≫
      (K.truncGEXIso e hj' (by
        subst hi' hj'
        exact e.not_mem_next_boundaryGE hij)).inv := by
  dsimp only [truncGE]
  rw [(K.truncGE' e).extend_d_eq e hi' hj', K.truncGE'_d_eq_fromOpcycles e hij hi' hj' hi]
  simp [truncGE'XIso, truncGEXIso, truncGE'XIsoOpcycles, truncGEXIsoOpcycles]

namespace truncGEπ

open Classical
noncomputable def f (i' : ι') : K.X i' ⟶ (K.truncGE e).X i' :=
  if hi' : ∃ i, e.f i = i'
  then if hi : e.BoundaryGE hi'.choose
    then
      K.pOpcycles i' ≫ (K.truncGEXIsoOpcycles e hi'.choose_spec hi).inv
    else
      (K.truncGEXIso e hi'.choose_spec hi).inv
  else 0

lemma f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    f K e i' = 0 :=
  dif_neg (by rintro ⟨i, rfl⟩; exact hi' i rfl)

lemma f_eq_pOpcycles_comp_iso_inv {i' : ι'} {i : ι} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    f K e i' = K.pOpcycles i' ≫ (K.truncGEXIsoOpcycles e hi' hi).inv := by
  have hi'' : ∃ k, e.f k = i' := ⟨i, hi'⟩
  have : hi''.choose = i := e.injective_f (by rw [hi''.choose_spec, hi'])
  dsimp [f]
  rw [dif_pos hi'', dif_pos (by simpa only [this] using hi)]
  congr

lemma f_eq_iso_inv {i' : ι'} {i : ι} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    f K e i' = (K.truncGEXIso e hi' hi).inv := by
  have hi'' : ∃ k, e.f k = i' := ⟨i, hi'⟩
  have : hi''.choose = i := e.injective_f (by rw [hi''.choose_spec, hi'])
  dsimp [f]
  rw [dif_pos hi'', dif_neg (by simpa only [this] using hi)]
  congr

end truncGEπ

noncomputable def truncGEπ : K ⟶ K.truncGE e where
  f := truncGEπ.f K e
  comm' i' j' hij' := by
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      by_cases hi' : ∃ i, e.f i = i'
      · obtain ⟨i, rfl⟩ := hi'
        rw [← e.rel_iff] at hij'
        by_cases hi : e.BoundaryGE i
        · rw [truncGEπ.f_eq_pOpcycles_comp_iso_inv K e rfl hi,
            truncGEπ.f_eq_iso_inv K e rfl (e.not_mem_next_boundaryGE hij'),
            K.truncGE_d_eq_fromOpcycles e hij' rfl rfl hi,
            assoc, Iso.inv_hom_id_assoc, p_fromOpcycles_assoc]
        · rw [truncGEπ.f_eq_iso_inv K e rfl hi,
            truncGEπ.f_eq_iso_inv K e rfl (e.not_mem_next_boundaryGE hij'),
            K.truncGE_d_eq e hij' rfl rfl hi,
            Iso.inv_hom_id_assoc]
      · rw [truncGEπ.f_eq_zero K e i' (by simpa using hi'), zero_comp,
          truncGEπ.f_eq_pOpcycles_comp_iso_inv K e rfl
            (e.mem_boundaryGE hij' (by simpa using hi')),
            d_pOpcycles_assoc, zero_comp]
    · apply (K.isZero_truncGE_X e j' (by simpa using hj')).eq_of_tgt

end HomologicalComplex

namespace ComplexShape

@[simps!]
def embeddingNat : Embedding (up ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => n)
    (fun _ _ hij => by simpa using hij)
    (fun _ _ => Nat.cast_inj.symm)

instance : embeddingNat.IsRelIff := by
  dsimp [embeddingNat]
  infer_instance

instance : embeddingNat.IsTruncGE where
  mem_next hj := ⟨_, hj⟩

example (n : ℕ) : embeddingNat.BoundaryGE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _| n := n
    · rfl
    · simpa using h.2 n
  · rintro rfl
    exact embeddingNat.mem_boundaryGE (i' := -1) (by simp) (fun i => by simp)

end ComplexShape
