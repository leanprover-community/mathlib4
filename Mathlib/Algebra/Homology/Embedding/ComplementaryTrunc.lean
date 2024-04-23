import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

lemma Int.exists_eq_add_nat_of_le (a b : ℤ) (hab : a ≤ b) :
    ∃ (k : ℕ), b = a + k := by
  obtain ⟨k, hk⟩ := Int.nonneg_def.1 hab
  exact ⟨k, by omega⟩

open CategoryTheory Limits

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

namespace ComplexShape

namespace Embedding

variable {C : Type*} [Category C] [HasZeroMorphisms C]

variable (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

structure AreComplementary : Prop where
  disjoint (i₁ : ι₁) (i₂ : ι₂) : e₁.f i₁ ≠ e₂.f i₂
  union (i : ι) : (∃ i₁, e₁.f i₁ = i) ∨ ∃ i₂, e₂.f i₂ = i

variable {e₁ e₂}

namespace AreComplementary

variable (ac : AreComplementary e₁ e₂)

lemma symm : AreComplementary e₂ e₁ where
  disjoint i₂ i₁ := (ac.disjoint i₁ i₂).symm
  union i := (ac.union i).symm

lemma exists_i₁ (i : ι) (hi : ∀ i₂, e₂.f i₂ ≠ i) :
    ∃ i₁, i = e₁.f i₁ := by
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · exact ⟨_, rfl⟩
  · exfalso
    exact hi i₂ rfl

lemma exists_i₂ (i : ι) (hi : ∀ i₁, e₁.f i₁ ≠ i) :
    ∃ i₂, i = e₂.f i₂ :=
  ac.symm.exists_i₁ i hi

variable (e₁ e₂) in
@[simp]
def fromSum : ι₁ ⊕ ι₂ → ι
  | Sum.inl i₁ => e₁.f i₁
  | Sum.inr i₂ => e₂.f i₂

def fromSum_bijective : Function.Bijective (fromSum e₁ e₂) := by
  constructor
  · rintro (i₁ | i₂) (j₁ | j₂) h
    · obtain rfl := e₁.injective_f h
      rfl
    · exfalso
      exact ac.disjoint _ _ h
    · exfalso
      exact ac.disjoint _ _ h.symm
    · obtain rfl := e₂.injective_f h
      rfl
  · intro n
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
    · exact ⟨Sum.inl i₁, rfl⟩
    · exact ⟨Sum.inr i₂, rfl⟩

noncomputable def equiv : ι₁ ⊕ ι₂ ≃ ι := Equiv.ofBijective _ (ac.fromSum_bijective)

@[simp] lemma equiv_inl (i₁ : ι₁) : ac.equiv (Sum.inl i₁) = e₁.f i₁ := rfl
@[simp] lemma equiv_inr (i₂ : ι₂) : ac.equiv (Sum.inr i₂) = e₂.f i₂ := rfl

section

variable {X : ι → Type*} (x₁ : ∀ i₁, X (e₁.f i₁)) (x₂ : ∀ i₂, X (e₂.f i₂))

variable (X) in
def aux (i j : ι) (hij : i = j) : X i ≃ X j := by
  subst hij
  rfl

@[simp]
lemma aux_trans {i j k : ι} (hij : i = j) (hjk : j = k) (x : X i):
    aux X j k hjk (aux X i j hij x) = aux X i k (hij.trans hjk) x := by
  subst hij hjk
  rfl

def desc' : ∀ (i : ι₁ ⊕ ι₂), X (ac.equiv i)
  | Sum.inl i₁ => x₁ i₁
  | Sum.inr i₂ => x₂ i₂

lemma desc'_inl (i : ι₁ ⊕ ι₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) :
    ac.desc' x₁ x₂ i = aux _ _ _ (by subst h; simp) (x₁ i₁) := by subst h; rfl

lemma desc'_inr (i : ι₁ ⊕ ι₂) (i₂ : ι₂) (h : Sum.inr i₂ = i) :
    ac.desc' x₁ x₂ i = aux _ _ _ (by subst h; simp) (x₂ i₂) := by subst h; rfl


noncomputable def desc (i : ι) : X i := aux _ _ _ (by simp) (ac.desc' x₁ x₂ (ac.equiv.symm i))

lemma desc_inl (i₁ : ι₁) : ac.desc x₁ x₂ (e₁.f i₁) = x₁ i₁ := by
  dsimp [desc]
  rw [ac.desc'_inl _ _ _ i₁ (ac.equiv.injective (by simp)), aux_trans]
  rfl

lemma desc_inr (i₂ : ι₂) : ac.desc x₁ x₂ (e₂.f i₂) = x₂ i₂ := by
  dsimp [desc]
  rw [ac.desc'_inr _ _ _ i₂ (ac.equiv.injective (by simp)), aux_trans]
  rfl

end

variable (K L : HomologicalComplex C c)

lemma isStrictlySupportedOutside₁_iff :
    K.IsStrictlySupportedOutside e₁ ↔ K.IsStrictlySupported e₂ := by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.isZero i₁⟩
  · intro _
    exact ⟨fun i₁ => K.isZero_X_of_isStrictlySupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩

lemma isStrictlySupportedOutside₂_iff :
    K.IsStrictlySupportedOutside e₂ ↔ K.IsStrictlySupported e₁ :=
  ac.symm.isStrictlySupportedOutside₁_iff K

lemma isSupportedOutside₁_iff :
    K.IsSupportedOutside e₁ ↔ K.IsSupported e₂ := by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.exactAt i₁⟩
  · intro _
    exact ⟨fun i₁ => K.exactAt_of_isSupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩

lemma isSupportedOutside₂_iff :
    K.IsSupportedOutside e₂ ↔ K.IsSupported e₁ :=
  ac.symm.isSupportedOutside₁_iff K

variable {K L}

lemma hom_ext' (φ : K ⟶ L) (hK : K.IsStrictlySupportedOutside e₂)
    (hL : L.IsStrictlySupportedOutside e₁) :
    φ = 0 := by
  ext i
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · apply (hL.isZero i₁).eq_of_tgt
  · apply (hK.isZero i₂).eq_of_src

lemma hom_ext [K.IsStrictlySupported e₁] [L.IsStrictlySupported e₂] (φ : K ⟶ L) :
    φ = 0 := by
  apply ac.hom_ext'
  · rw [ac.isStrictlySupportedOutside₂_iff]
    infer_instance
  · rw [ac.isStrictlySupportedOutside₁_iff]
    infer_instance

@[nolint unusedArguments]
def Boundary (_ : AreComplementary e₁ e₂) (i₁ : ι₁) (i₂ : ι₂) : Prop :=
  c.Rel (e₁.f i₁) (e₂.f i₂)

namespace Boundary

variable {ac}

section

variable {i₁ : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂)

lemma fst : e₁.BoundaryLE i₁ :=
  e₁.mem_boundaryLE h (fun _ => ac.disjoint _ _)

lemma snd : e₂.BoundaryGE i₂ :=
  e₂.mem_boundaryGE h (fun _ => ac.symm.disjoint _ _)

end

lemma fst_inj {i₁ i₁' : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary i₁' i₂) :
    i₁ = i₁' :=
  e₁.injective_f (c.prev_eq h h')

lemma snd_inj {i₁ : ι₁} {i₂ i₂' : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary i₁ i₂') :
    i₂ = i₂' :=
  e₂.injective_f (c.next_eq h h')

variable (ac)

lemma exists₁ {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    ∃ i₂, ac.Boundary i₁ i₂ := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₂, hi₂⟩ := ac.exists_i₂ (c.next (e₁.f i₁))
    (fun i₁' hi₁' => h₂ i₁' (by simpa only [← hi₁'] using h₁))
  exact ⟨i₂, by simpa only [hi₂] using h₁⟩

lemma exists₂ {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    ∃ i₁, ac.Boundary i₁ i₂ := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₁, hi₁⟩ := ac.exists_i₁ (c.prev (e₂.f i₂))
    (fun i₂' hi₂' => h₂ i₂' (by simpa only [← hi₂'] using h₁))
  exact ⟨i₁, by simpa only [hi₁] using h₁⟩

noncomputable def indexOfBoundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) : ι₂ :=
    (exists₁ ac h).choose

def of_boundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    ac.Boundary i₁ (indexOfBoundaryLE ac h) := (exists₁ ac h).choose_spec

noncomputable def indexOfBoundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) : ι₁ :=
    (exists₂ ac h).choose

def of_boundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    ac.Boundary (indexOfBoundaryGE ac h) i₂ := (exists₂ ac h).choose_spec

noncomputable def equiv : Subtype e₁.BoundaryLE ≃ Subtype e₂.BoundaryGE where
  toFun := fun ⟨i₁, h⟩ => ⟨_, (of_boundaryLE ac h).snd⟩
  invFun := fun ⟨i₂, h⟩ => ⟨_, (of_boundaryGE ac h).fst⟩
  left_inv := fun ⟨i₁, h⟩ => by
    ext
    have h' := of_boundaryLE ac h
    have h'' := of_boundaryGE ac h'.snd
    exact fst_inj h'' h'
  right_inv := fun ⟨i₂, h⟩ => by
    ext
    have h' := of_boundaryGE ac h
    have h'' := of_boundaryLE ac h'.fst
    exact snd_inj h'' h'

end Boundary

end AreComplementary

lemma embeddingUpInt_areComplementary (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    AreComplementary (embeddingUpIntLE n₀) (embeddingUpIntGE n₁) where
  disjoint i₁ i₂ := by dsimp; omega
  union i := by
    by_cases hi : i ≤ n₀
    · obtain ⟨k, rfl⟩ := Int.exists_eq_add_nat_of_le _ _ hi
      exact Or.inl ⟨k, by dsimp; omega⟩
    · obtain ⟨k, rfl⟩ := Int.exists_eq_add_nat_of_le n₁ i (by omega)
      exact Or.inr ⟨k, rfl⟩

end Embedding

end ComplexShape

namespace HomologicalComplex

section

variable {C : Type*} [Category C] [Abelian C]

variable (K : HomologicalComplex C c) {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c}
  [e₁.IsTruncLE] [e₂.IsTruncGE] (ac : e₁.AreComplementary e₂)

noncomputable def shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE e₁).X₃ ⟶ K.truncGE e₂ :=
  cokernel.desc _ (K.πTruncGE e₂) (ac.hom_ext _)

@[reassoc (attr := simp)]
lemma g_shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE e₁).g ≫ K.shortComplexTruncLEX₃ToTruncGE ac = K.πTruncGE e₂ :=
  cokernel.π_desc _ _ _

instance : QuasiIso (K.shortComplexTruncLEX₃ToTruncGE ac) where
  quasiIsoAt i := by
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
    · have h₁ := ((ac.isSupportedOutside₁_iff (K.truncGE e₂)).2 inferInstance).exactAt i₁
      have h₂ := (K.shortComplexTruncLE_X₃_isSupportedOutside e₁).exactAt i₁
      simpa only [quasiIsoAt_iff_exactAt _ _ h₂] using h₁
    · have := quasiIsoAt_shortComplexTruncLE_g K e₁ (e₂.f i₂) (fun _ => ac.disjoint _ _)
      rw [← quasiIsoAt_iff_comp_left (K.shortComplexTruncLE e₁).g
        (K.shortComplexTruncLEX₃ToTruncGE ac), g_shortComplexTruncLEX₃ToTruncGE]
      dsimp
      infer_instance

end

section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

variable (K : HomologicalComplex C c) {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c}
  [e₁.IsTruncLE] [e₂.IsTruncGE] (ac : e₁.AreComplementary e₂)

lemma ιStupidTrunc_πStupidTrunc :
    K.ιStupidTrunc e₂ ≫ K.πStupidTrunc e₁ = 0 := by
  ext n
  have h₁ : (K.stupidTrunc e₂).IsStrictlySupportedOutside e₁ := by
    rw [ac.isStrictlySupportedOutside₁_iff]
    infer_instance
  have h₂ : (K.stupidTrunc e₁).IsStrictlySupportedOutside e₂ := by
    rw [ac.isStrictlySupportedOutside₂_iff]
    infer_instance
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
  · apply IsZero.eq_of_src
    apply h₁.isZero
  · apply IsZero.eq_of_tgt
    apply h₂.isZero

@[simps]
noncomputable def shortComplexStupidTrunc : ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (K.ιStupidTrunc e₂) (K.πStupidTrunc e₁) (K.ιStupidTrunc_πStupidTrunc ac)

noncomputable def shortComplexStupidTruncSplitting₁ (n : ι₁) :
    ((K.shortComplexStupidTrunc ac).map (eval C _ (e₁.f n))).Splitting where
  r := 0
  s := (asIso ((K.πStupidTrunc e₁).f (e₁.f n))).inv
  f_r := by
    apply IsZero.eq_of_src
    dsimp
    apply IsStrictlySupportedOutside.isZero (e := e₁)
    rw [ac.isStrictlySupportedOutside₁_iff]
    infer_instance

noncomputable def shortComplexStupidTruncSplitting₂ (n : ι₂) :
    ((K.shortComplexStupidTrunc ac).map (eval C _ (e₂.f n))).Splitting where
  r := (asIso ((K.ιStupidTrunc e₂).f (e₂.f n))).inv
  s := 0
  s_g := by
    apply IsZero.eq_of_src
    dsimp
    apply IsStrictlySupportedOutside.isZero (e := e₂)
    rw [ac.isStrictlySupportedOutside₂_iff]
    infer_instance

noncomputable def shortComplexStupidTruncSplitting (n : ι) :
    ((K.shortComplexStupidTrunc ac).map (eval C _ n)).Splitting := by
  apply ac.desc (K.shortComplexStupidTruncSplitting₁ ac)
    (K.shortComplexStupidTruncSplitting₂ ac) n


end

end HomologicalComplex

namespace ComplexShape.Embedding.AreComplementary

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

variable {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c} (ac : e₁.AreComplementary e₂)
variable (K : HomologicalComplex C c)

lemma isZero_stupidTrunc_iff [e₁.IsRelIff] :
    IsZero (K.stupidTrunc e₁) ↔ K.IsStrictlySupported e₂ := by
  rw [K.isZero_stupidTrunc_iff, ac.isStrictlySupportedOutside₁_iff]

lemma isZero_stupidTrunc [e₁.IsRelIff] [K.IsStrictlySupported e₂] :
    IsZero (K.stupidTrunc e₁) := by
  rw [ac.isZero_stupidTrunc_iff]
  infer_instance

end ComplexShape.Embedding.AreComplementary
