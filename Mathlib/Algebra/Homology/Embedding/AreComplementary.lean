/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-!
# Complementary embeddings

Given two embeddings `e₁ : c₁.Embedding c` and `e₂ : c₂.Embedding c`
of complex shapes, we introduce a property `e₁.AreComplementary e₂`
saying that the image subsets of the indices of `c₁` and `c₂` form
a partition of the indices of `c`.

If `e₁.IsTruncLE` and `e₂.IsTruncGE`, and `K : HomologicalComplex C c`,
we construct a quasi-isomorphism `shortComplexTruncLEX₃ToTruncGE` between
the cokernel of `K.ιTruncLE e₁ : K.truncLE e₁ ⟶ K` and `K.truncGE e₂`.

-/

open CategoryTheory Limits

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

namespace ComplexShape

namespace Embedding

variable {C : Type*} [Category C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

/-- Two embedding `e₁` and `e₂` into a complex shape `c : ComplexShape ι`
are complementary when the range of `e₁.f` and `e₂.f` form a partition of `ι`. -/
structure AreComplementary : Prop where
  disjoint (i₁ : ι₁) (i₂ : ι₂) : e₁.f i₁ ≠ e₂.f i₂
  union (i : ι) : (∃ i₁, e₁.f i₁ = i) ∨ ∃ i₂, e₂.f i₂ = i

variable {e₁ e₂}

namespace AreComplementary

variable (ac : AreComplementary e₁ e₂)

include ac
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
/-- Given complementary embeddings of complex shapes
`e₁ : Embedding c₁ c` and `e₂ : Embedding c₂ c`, this is
the obvious map `ι₁ ⊕ ι₂ → ι` from the sum of the index
types of `c₁` and `c₂` to the index type of `c`. -/
@[simp]
def fromSum : ι₁ ⊕ ι₂ → ι
  | Sum.inl i₁ => e₁.f i₁
  | Sum.inr i₂ => e₂.f i₂

lemma fromSum_bijective : Function.Bijective (fromSum e₁ e₂) := by
  constructor
  · rintro (i₁ | i₂) (j₁ | j₂) h
    · obtain rfl := e₁.injective_f h
      rfl
    · exact (ac.disjoint _ _ h).elim
    · exact (ac.disjoint _ _ h.symm).elim
    · obtain rfl := e₂.injective_f h
      rfl
  · intro n
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
    · exact ⟨Sum.inl i₁, rfl⟩
    · exact ⟨Sum.inr i₂, rfl⟩

/-- Given complementary embeddings of complex shapes
`e₁ : Embedding c₁ c` and `e₂ : Embedding c₂ c`, this is
the obvious bijection `ι₁ ⊕ ι₂ ≃ ι` from the sum of the index
types of `c₁` and `c₂` to the index type of `c`. -/
noncomputable def equiv : ι₁ ⊕ ι₂ ≃ ι := Equiv.ofBijective _ (ac.fromSum_bijective)

@[simp] lemma equiv_inl (i₁ : ι₁) : ac.equiv (Sum.inl i₁) = e₁.f i₁ := rfl
@[simp] lemma equiv_inr (i₂ : ι₂) : ac.equiv (Sum.inr i₂) = e₂.f i₂ := rfl

section

variable {X : ι → Type*} (x₁ : ∀ i₁, X (e₁.f i₁)) (x₂ : ∀ i₂, X (e₂.f i₂))

variable (X) in
/-- Auxiliary definition for `desc`. -/
def desc.aux (i j : ι) (hij : i = j) : X i ≃ X j := by
  subst hij
  rfl

omit ac in
@[simp]
lemma desc.aux_trans {i j k : ι} (hij : i = j) (hjk : j = k) (x : X i) :
    desc.aux X j k hjk (aux X i j hij x) = desc.aux X i k (hij.trans hjk) x := by
  subst hij hjk
  rfl

/-- Auxiliary definition for `desc`. -/
def desc' : ∀ (i : ι₁ ⊕ ι₂), X (ac.equiv i)
  | Sum.inl i₁ => x₁ i₁
  | Sum.inr i₂ => x₂ i₂

lemma desc'_inl (i : ι₁ ⊕ ι₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) :
    ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst h; simp) (x₁ i₁) := by subst h; rfl

lemma desc'_inr (i : ι₁ ⊕ ι₂) (i₂ : ι₂) (h : Sum.inr i₂ = i) :
    ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst h; simp) (x₂ i₂) := by subst h; rfl

/-- If `ι₁` and `ι₂` are the index types of complementary embeddings into a
complex shape of index type `ι`, this is a constructor for (dependent) maps from `ι`,
which takes as inputs the "restrictions" to `ι₁` and `ι₂`. -/
noncomputable def desc (i : ι) : X i :=
  desc.aux _ _ _ (by simp) (ac.desc' x₁ x₂ (ac.equiv.symm i))

lemma desc_inl (i₁ : ι₁) : ac.desc x₁ x₂ (e₁.f i₁) = x₁ i₁ := by
  dsimp [desc]
  rw [ac.desc'_inl _ _ _ i₁ (ac.equiv.injective (by simp)), desc.aux_trans]
  rfl

lemma desc_inr (i₂ : ι₂) : ac.desc x₁ x₂ (e₂.f i₂) = x₂ i₂ := by
  dsimp [desc]
  rw [ac.desc'_inr _ _ _ i₂ (ac.equiv.injective (by simp)), desc.aux_trans]
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

/-- Variant of `hom_ext`. -/
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

/-- If `e₁` and `e₂` are complementary embeddings into a complex shape `c`,
indices `i₁` and `i₂` are at the boundary if `c.Rel (e₁.f i₁) (e₂.f i₂)`. -/
@[nolint unusedArguments]
def Boundary (_ : AreComplementary e₁ e₂) (i₁ : ι₁) (i₂ : ι₂) : Prop :=
  c.Rel (e₁.f i₁) (e₂.f i₂)

namespace Boundary

variable {ac}

section

variable {i₁ : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂)

include h

lemma fst : e₁.BoundaryLE i₁ :=
  e₁.boundaryLE h (fun _ => ac.disjoint _ _)

lemma snd : e₂.BoundaryGE i₂ :=
  e₂.boundaryGE h (fun _ => ac.symm.disjoint _ _)

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

/-- If `ac : AreComplementary e₁ e₂` (with `e₁ : ComplexShape.Embedding c₁ c` and
`e₂ : ComplexShape.Embedding c₂ c`), and `i₁` belongs to `e₁.BoundaryLE`,
then this is the (unique) index `i₂` of `c₂` such that `ac.Boundary i₁ i₂`. -/
noncomputable def indexOfBoundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) : ι₂ :=
    (exists₁ ac h).choose

lemma of_boundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    ac.Boundary i₁ (indexOfBoundaryLE ac h) := (exists₁ ac h).choose_spec

/-- If `ac : AreComplementary e₁ e₂` (with `e₁ : ComplexShape.Embedding c₁ c` and
`e₂ : ComplexShape.Embedding c₂ c`), and `i₂` belongs to `e₂.BoundaryGE`,
then this is the (unique) index `i₁` of `c₁` such that `ac.Boundary i₁ i₂`. -/
noncomputable def indexOfBoundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) : ι₁ :=
    (exists₂ ac h).choose

lemma of_boundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    ac.Boundary (indexOfBoundaryGE ac h) i₂ := (exists₂ ac h).choose_spec

/-- The bijection `Subtype e₁.BoundaryLE ≃ Subtype e₂.BoundaryGE` when
`e₁` and `e₂` are complementary embeddings of complex shapes. -/
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
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le hi
      exact Or.inl ⟨k, by dsimp; omega⟩
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le (show n₁ ≤ i by omega)
      exact Or.inr ⟨k, rfl⟩

end Embedding

end ComplexShape

namespace HomologicalComplex

section

variable {C : Type*} [Category C] [Abelian C]
  (K : HomologicalComplex C c) {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c}
  [e₁.IsTruncLE] [e₂.IsTruncGE] (ac : e₁.AreComplementary e₂)

/-- When `e₁` and `e₂` are complementary embeddings of complex shapes, with
`e₁.IsTruncLE` and `e₂.IsTruncGE`, then this is the canonical quasi-isomorphism
`(K.shortComplexTruncLE e₁).X₃ ⟶ K.truncGE e₂` where
`(K.shortComplexTruncLE e₁).X₃` is the cokernel of `K.ιTruncLE e₁ : K.truncLE e₁ ⟶ K`. -/
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

end HomologicalComplex
