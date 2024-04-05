import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

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

end HomologicalComplex
