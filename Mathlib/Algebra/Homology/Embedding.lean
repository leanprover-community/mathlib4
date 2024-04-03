import Mathlib.Algebra.Homology.HomologicalComplex

-- mostly from LTE

open CategoryTheory Limits ZeroObject Category

variable {C : Type*} [Category C] [HasZeroMorphisms C]
  {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

lemma Option.eq_none_or_eq_some (x : Option ι) :
    x = none ∨ ∃ y, x = some y := by
  cases x
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

namespace ComplexShape

structure Embedding where
  f : ι → ι'
  injective_f : Function.Injective f
  rel {i₁ i₂ : ι} (h : c.Rel i₁ i₂) : c'.Rel (f i₁) (f i₂)

namespace Embedding

variable {c c'}
variable (e : Embedding c c')

class IsRelIff : Prop where
  rel' (i₁ i₂ : ι) (h : c'.Rel (e.f i₁) (e.f i₂)) : c.Rel i₁ i₂

lemma rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c.Rel i₁ i₂ ↔ c'.Rel (e.f i₁) (e.f i₂) := by
  constructor
  · exact e.rel
  · apply IsRelIff.rel'

section

variable (c c')
variable (f : ι → ι') (hf : Function.Injective f)
    (iff : ∀ (i₁ i₂ : ι), c.Rel i₁ i₂ ↔ c'.Rel (f i₁) (f i₂))

@[simps]
def mk' : Embedding c c' where
  f := f
  injective_f := hf
  rel h := (iff _ _).1 h

instance : (mk' c c' f hf iff).IsRelIff where
  rel' _ _ h := (iff _ _).2 h

end

class IsTruncGE extends e.IsRelIff : Prop where
  mem_next {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') :
    ∃ k, e.f k = k'

class IsTruncLE extends e.IsRelIff : Prop where
  mem_prev {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) :
    ∃ i, e.f i = i'

lemma mem_next [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') : ∃ k, e.f k = k' :=
  IsTruncGE.mem_next h

lemma mem_prev [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) : ∃ i, e.f i = i' :=
  IsTruncLE.mem_prev h

open Classical in
noncomputable def r (i' : ι') : Option ι :=
  if h : ∃ (i : ι), e.f i = i'
  then some h.choose
  else none

lemma r_eq_some {i : ι} {i' : ι'} (hi : e.f i = i') :
    e.r i' = some i := by
  have h : ∃ (i : ι), e.f i = i' := ⟨i, hi⟩
  have : h.choose = i := e.injective_f (h.choose_spec.trans (hi.symm))
  dsimp [r]
  rw [dif_pos ⟨i, hi⟩, this]

lemma r_eq_none (i' : ι') (hi : ∀ i, e.f i ≠ i') :
    e.r i' = none :=
  dif_neg (by
    rintro ⟨i, hi'⟩
    exact hi i hi')

lemma f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : ∃ (k : ι), e.f k = i'
  · obtain ⟨k, hk⟩ := h
    have : some i = some k := by
      rw [← e.r_eq_some hk, hi]
    rw [← hk]
    congr 1
    simpa using this
  · simp [r, dif_neg h] at hi

end Embedding

end ComplexShape

namespace HomologicalComplex

variable {c c'} {C : Type*} [Category C] [HasZeroMorphisms C]
  [HasZeroObject C]

section

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

noncomputable def X : Option ι → C
  | some x => K.X x
  | none => 0

noncomputable def XIso {i : Option ι} {j : ι} (hj : i = some j) :
    X K i ≅ K.X j := eqToIso (by subst hj; rfl)

lemma isZero_X {i : Option ι} (hi : i = none) :
    IsZero (X K i) := by
  subst hi
  exact Limits.isZero_zero _

noncomputable def d : ∀ (i j : Option ι), extend.X K i ⟶ extend.X K j
  | none, _ => 0
  | some i, some j => K.d i j
  | some _, none => 0

lemma d_none_eq_zero (i j : Option ι) (hi : i = none) :
    d K i j = 0 := by subst hi; rfl

lemma d_none_eq_zero' (i j : Option ι) (hj : j = none) :
    d K i j = 0 := by subst hj; cases i <;> rfl

lemma d_eq {i j : Option ι} {a b : ι}
    (hi : i = some a) (hj : j = some b) :
    d K i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).inv := by
  subst hi hj
  dsimp [XIso, d]
  erw [id_comp, comp_id]

variable {K L}

noncomputable def mapX : ∀ (i : Option ι), X K i ⟶ X L i
  | some i => φ.f i
  | none => 0

lemma mapX_some {i : Option ι} {a : ι} (hi : i = some a) :
    mapX φ i = (XIso K hi).hom ≫ φ.f a ≫ (XIso L hi).inv := by
  subst hi
  dsimp [XIso]
  erw [id_comp, comp_id]
  rfl

lemma mapX_none {i : Option ι} (hi : i = none) :
    mapX φ i = 0 := by subst hi; rfl

end extend

noncomputable def extend : HomologicalComplex C c' where
  X i' := extend.X K (e.r i')
  d i' j' := extend.d K (e.r i') (e.r j')
  shape i' j' h := by
    dsimp
    obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi']
    · obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero' K _ _ hj']
      · rw [extend.d_eq K hi hj,K.shape, zero_comp, comp_zero]
        obtain rfl := e.f_eq_of_r_eq_some hi
        obtain rfl := e.f_eq_of_r_eq_some hj
        intro hij
        exact h (e.rel hij)
  d_comp_d' i' j' k' _ _ := by
    dsimp
    obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi', zero_comp]
    · obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero K _ _ hj', comp_zero]
      · obtain hk'|⟨k, hk⟩ := (e.r k').eq_none_or_eq_some
        · rw [extend.d_none_eq_zero' K _ _ hk', comp_zero]
        · rw [extend.d_eq K hi hj,
            extend.d_eq K hj hk, assoc, assoc,
            Iso.inv_hom_id_assoc, K.d_comp_d_assoc, zero_comp, comp_zero]

noncomputable def extendXIso {i' : ι'} {i : ι} (h : e.f i = i') :
    (K.extend e).X i' ≅ K.X i :=
  extend.XIso K (e.r_eq_some h)

lemma isZero_extend_X' (i' : ι') (hi' : e.r i' = none) :
    IsZero ((K.extend e).X i') :=
  extend.isZero_X K hi'

lemma isZero_extend_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.extend e).X i') :=
  K.isZero_extend_X' e i' (by
    obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · exact hi'
    · exfalso
      exact hi' _ (e.f_eq_of_r_eq_some hi))

lemma extend_d_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).d i' j' = (K.extendXIso e hi).hom ≫ K.d i j ≫
      (K.extendXIso e hj).inv := by
  apply extend.d_eq

lemma extend_d_from_eq_zero (i' j' : ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Rel i (c.next i)) :
    (K.extend e).d i' j' = 0 := by
  obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
  · exact extend.d_none_eq_zero' _ _ _ hj'
  · rw [extend_d_eq K e hi (e.f_eq_of_r_eq_some hj), K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.next_eq' hij
    exact hi' hij

lemma extend_d_to_eq_zero (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j) :
    (K.extend e).d i' j' = 0 := by
  obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact extend.d_none_eq_zero _ _ _ hi'
  · rw [extend_d_eq K e (e.f_eq_of_r_eq_some hi) hj, K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.prev_eq' hij
    exact hj' hij

variable {K L M}

noncomputable def extendMap : K.extend e ⟶ L.extend e where
  f _ := extend.mapX φ _
  comm' i' j' _ := by
    dsimp
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      by_cases hj : ∃ j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj
        rw [K.extend_d_eq e hi hj, L.extend_d_eq e hi hj,
          extend.mapX_some φ (e.r_eq_some hi),
          extend.mapX_some φ (e.r_eq_some hj)]
        simp [extendXIso]
      · have hj' := e.r_eq_none j' (fun j'' hj'' => hj ⟨j'', hj''⟩)
        dsimp [extend]
        rw [extend.d_none_eq_zero' _ _ _ hj', extend.d_none_eq_zero' _ _ _ hj',
          comp_zero, zero_comp]
    · have hi' := e.r_eq_none i' (fun i'' hi'' => hi ⟨i'', hi''⟩)
      dsimp [extend]
      rw [extend.d_none_eq_zero _ _ _ hi', extend.d_none_eq_zero _ _ _ hi',
        comp_zero, zero_comp]

lemma extendMap_f {i : ι} {i' : ι'} (h : e.f i = i') :
    (extendMap φ e).f i' =
      (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e h).inv := by
  dsimp [extendMap]
  rw [extend.mapX_some φ (e.r_eq_some h)]
  rfl

lemma extendMap_f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    (extendMap φ e).f i' = 0 := by
  dsimp [extendMap]
  rw [extend.mapX_none φ (e.r_eq_none i' hi')]

@[reassoc (attr := simp)]
lemma extendMap_comp_f (i' : ι') :
    (extendMap (φ ≫ φ') e).f i' = (extendMap φ e).f i' ≫ (extendMap φ' e).f i' := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · simp [extendMap_f_eq_zero _ e i' (fun i hi => hi' ⟨i, hi⟩)]

@[reassoc (attr := simp)]
lemma extendMap_comp :
    extendMap (φ ≫ φ') e = extendMap φ e ≫ extendMap φ' e := by aesop_cat

variable (K L M)

@[simp]
lemma extendMap_id_f (i' : ι') : (extendMap (𝟙 K) e).f i' = 𝟙 _ := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]
lemma extendMap_id : extendMap (𝟙 K) e = 𝟙 _ := by aesop_cat

end

section

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

@[simps]
def restriction : HomologicalComplex C c where
  X i := K.X (e.f i)
  d _ _ := K.d _ _
  shape i j hij := K.shape _ _ (by simpa only [← e.rel_iff] using hij)

noncomputable def stupidTrunc : HomologicalComplex C c' := ((K.restriction e).extend e)

noncomputable def stupidTruncXIso {i : ι} {i' : ι'} (hi' : e.f i = i') :
    (K.stupidTrunc e).X i' ≅ K.X i' :=
  (K.restriction e).extendXIso e hi' ≪≫ eqToIso (by subst hi'; rfl)

lemma isZero_stupidTrunc_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.stupidTrunc e).X i') :=
  isZero_extend_X _ _ _ hi'

variable {K L}

@[simps]
def restrictionMap : K.restriction e ⟶ L.restriction e where
  f i := φ.f (e.f i)

noncomputable def stupidTruncMap : K.stupidTrunc e ⟶ L.stupidTrunc e := extendMap (restrictionMap φ e) e

variable (K)

@[simp]
lemma restrictionMap_id : restrictionMap (𝟙 K) e = 𝟙 _ := by aesop_cat

@[simp, reassoc]
lemma restrictionMap_comp :
    restrictionMap (φ ≫ φ') e = restrictionMap φ e ≫ restrictionMap φ' e := by aesop_cat

@[simp]
lemma stupidTruncMap_id_f (i' : ι') : (stupidTruncMap (𝟙 K) e).f i' = 𝟙 _ := by
  simp [stupidTruncMap, stupidTrunc]

@[simp]
lemma stupidTruncMap_id : stupidTruncMap (𝟙 K) e = 𝟙 _ := by aesop_cat


variable {K}

@[simp]
lemma stupidTruncMap_comp_f (i' : ι') :
    (stupidTruncMap (φ ≫ φ') e).f i' = (stupidTruncMap φ e).f i' ≫
      (stupidTruncMap φ' e).f i' := by
  simp [stupidTruncMap, stupidTrunc]

@[simp, reassoc]
lemma stupidTruncMap_comp :
    stupidTruncMap (φ ≫ φ') e = stupidTruncMap φ e ≫ stupidTruncMap φ' e := by aesop_cat

end

section

variable (K L : HomologicalComplex C c') (φ : K ⟶ L)
  (e : c.Embedding c') [e.IsTruncGE]

open Classical in
noncomputable def ιStupidTruncf (i' : ι') : (K.stupidTrunc e).X i' ⟶ K.X i' :=
  if h : ∃ (i : ι), e.f i = i'
  then (K.stupidTruncXIso e h.choose_spec).hom
  else 0

lemma ιStupidTruncf_eq (i : ι) :
    K.ιStupidTruncf e (e.f i) = ((K.restriction e).extendXIso e rfl).hom := by
  dsimp [ιStupidTruncf]
  rw [dif_pos ⟨i, rfl⟩]
  simp [extendXIso, extend.XIso, stupidTruncXIso]

noncomputable def ιStupidTrunc : K.stupidTrunc e ⟶ K where
  f := K.ιStupidTruncf e
  comm' i' j' hij' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      obtain ⟨j, rfl⟩ := e.mem_next hij'
      simp [ιStupidTruncf_eq, stupidTrunc, (K.restriction e).extend_d_eq e rfl rfl]
    · apply (K.isZero_stupidTrunc_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

lemma isIso_ιStupidTrunc_f {i' : ι'} {i : ι} (h : e.f i = i') :
    IsIso ((K.ιStupidTrunc e).f i') := by
  subst h
  dsimp [ιStupidTrunc]
  rw [ιStupidTruncf_eq]
  infer_instance

instance (i : ι) : IsIso ((K.ιStupidTrunc e).f (e.f i)) :=
  K.isIso_ιStupidTrunc_f e rfl

variable {K L}

@[reassoc (attr := simp)]
lemma ιStudicTrunc_naturality :
    stupidTruncMap φ e ≫ L.ιStupidTrunc e = K.ιStupidTrunc e ≫ φ := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [ιStupidTrunc, ιStupidTruncf_eq, stupidTruncMap, extendMap_f _ e rfl]
  · apply (K.isZero_stupidTrunc_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

end

section

variable (K L : HomologicalComplex C c') (φ : K ⟶ L)
  (e : c.Embedding c') [e.IsTruncLE]

open Classical in
noncomputable def πStupidTruncf (i' : ι') : K.X i' ⟶ (K.stupidTrunc e).X i' :=
  if h : ∃ (i : ι), e.f i = i'
  then (K.stupidTruncXIso e h.choose_spec).inv
  else 0

lemma πStupidTruncf_eq (i : ι) :
    K.πStupidTruncf e (e.f i) = ((K.restriction e).extendXIso e rfl).inv := by
  dsimp [πStupidTruncf]
  rw [dif_pos ⟨i, rfl⟩]
  simp [extendXIso, extend.XIso, stupidTruncXIso]

noncomputable def πStupidTrunc : K ⟶ K.stupidTrunc e where
  f := K.πStupidTruncf e
  comm' i' j' hij' := by
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      obtain ⟨i, rfl⟩ := e.mem_prev hij'
      simp [πStupidTruncf_eq, stupidTrunc, (K.restriction e).extend_d_eq e rfl rfl]
    · apply (K.isZero_stupidTrunc_X e j' (fun j hj => hj' ⟨j, hj⟩)).eq_of_tgt

lemma isIso_πStupidTrunc_f {i' : ι'} {i : ι} (h : e.f i = i') :
    IsIso ((K.πStupidTrunc e).f i') := by
  subst h
  dsimp [πStupidTrunc]
  rw [πStupidTruncf_eq]
  infer_instance

instance (i : ι) : IsIso ((K.πStupidTrunc e).f (e.f i)) :=
  K.isIso_πStupidTrunc_f e rfl

variable {K L}

@[reassoc (attr := simp)]
lemma πStudicTrunc_naturality :
    K.πStupidTrunc e ≫ stupidTruncMap φ e = φ ≫ L.πStupidTrunc e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [πStupidTrunc, πStupidTruncf_eq, stupidTruncMap, extendMap_f _ e rfl]
  · apply (L.isZero_stupidTrunc_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_tgt

end

end HomologicalComplex

namespace ComplexShape

namespace Embedding

variable {c c'}
variable (e : Embedding c c') (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

@[simps]
noncomputable def extendFunctor :
    HomologicalComplex C c ⥤ HomologicalComplex C c' where
  obj K := K.extend e
  map φ := HomologicalComplex.extendMap φ e

@[simps]
noncomputable def restrictionFunctor [e.IsRelIff] :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.restriction e
  map φ := HomologicalComplex.restrictionMap φ e

@[simps]
noncomputable def stupidTruncFunctor [e.IsRelIff] :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.stupidTrunc e
  map φ := HomologicalComplex.stupidTruncMap φ e

@[simps]
noncomputable def ιStupidTruncNatTrans [e.IsTruncGE] :
    e.stupidTruncFunctor C ⟶ 𝟭 _ where
  app K := K.ιStupidTrunc e

@[simps]
noncomputable def πStupidTruncNatTrans [e.IsTruncLE] :
    𝟭 _ ⟶ e.stupidTruncFunctor C  where
  app K := K.πStupidTrunc e

end Embedding

end ComplexShape
