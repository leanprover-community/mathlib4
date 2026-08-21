/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular

/-!
# Helper structure in order to construct pairings

In this file, we introduce a helper structure `Subcomplex.PairingCore`
in order to construct a pairing for a subcomplex of a simplicial set.
The main difference with `Subcomplex.Pairing` are that we provide
an index type `ι` and a function `dim : ι → ℕ` which allow to
parametrize type (II) and (I) simplices in such a way that, *definitionally*,
their dimensions are respectively `dim s` or `dim s + 1` for `s : ι`.

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- A helper structure in order to construct a pairing for a subcomplex of a
simplicial set `X`. The main difference with `Pairing` is that we provide
an index type `ι` and a function `dim : ι → ℕ` which allow to
parametrize type (I) simplices as `simplex s : X _⦋dim s + 1⦌` for `s : ι`,
and type (II) simplices as a face of `simplex s` in `X _⦋dim s⦌`. -/
structure PairingCore where
  /-- the index type -/
  ι : Type v
  /-- the dimension of each type (II) simplex -/
  dim (s : ι) : ℕ
  /-- the family of type (I) simplices -/
  simplex (s : ι) : X _⦋dim s + 1⦌
  /-- the corresponding type (II) simplex is the `1`-codimensional
    face given by this index -/
  index (s : ι) : Fin (dim s + 2)
  nonDegenerate₁ (s : ι) : simplex s ∈ X.nonDegenerate _
  nonDegenerate₂ (s : ι) : X.δ (index s) (simplex s) ∈ X.nonDegenerate _
  notMem₁ (s : ι) : simplex s ∉ A.obj _
  notMem₂ (s : ι) : X.δ (index s) (simplex s) ∉ A.obj _
  injective_type₁' {s t : ι} (h : S.mk (simplex s) = S.mk (simplex t)) : s = t
  injective_type₂' {s t : ι}
    (h : S.mk (X.δ (index s) (simplex s)) = S.mk (X.δ (index t) (simplex t))) : s = t
  type₁_ne_type₂' (s t : ι) : S.mk (simplex s) ≠ S.mk (X.δ (index t) (simplex t))
  surjective' (x : A.N) :
    ∃ (s : ι), x.toS = S.mk (simplex s) ∨ x.toS = S.mk (X.δ (index s) (simplex s))

variable {A}

/-- The `PairingCore` structure induced by a pairing. The opposite construction
is `PairingCore.pairing`. -/
noncomputable def Pairing.pairingCore (P : A.Pairing) [P.IsProper] :
    A.PairingCore where
  ι := P.II
  dim s := s.val.dim
  simplex s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).simplex
  index s := (P.isUniquelyCodimOneFace s).index rfl
  nonDegenerate₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).nonDegenerate
  nonDegenerate₂ s := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl]
    exact s.val.nonDegenerate
  notMem₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).notMem
  notMem₂ s := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl]
    exact s.val.notMem
  injective_type₁' {s t} _ := by
    apply P.p.injective
    rwa [Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff,
      ← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq,
      ← (P.p t).val.cast_eq_self (P.isUniquelyCodimOneFace t).dim_eq]
  injective_type₂' {s t} h := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl,
      (P.isUniquelyCodimOneFace t).δ_index rfl] at h
    rwa [Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff]
  type₁_ne_type₂' s t h := (P.ne (P.p s) t) (by
    rw [(P.isUniquelyCodimOneFace t).δ_index rfl] at h
    rwa [← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq,
      N.ext_iff, SSet.N.ext_iff])
  surjective' x := by
    obtain ⟨s, rfl | rfl⟩ := P.exists_or x
    · refine ⟨s, Or.inr ?_⟩
      simp [(P.isUniquelyCodimOneFace s).δ_index]
    · refine ⟨s, Or.inl ?_⟩
      nth_rw 1 [← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq]
      rfl

namespace PairingCore

variable (h : A.PairingCore)

/-- The type (I) simplices of `h : A.PairingCore`, as a family indexed by `h.ι`. -/
@[simps!]
def type₁ (s : h.ι) : A.N :=
  Subcomplex.N.mk (h.simplex s) (h.nonDegenerate₁ s) (h.notMem₁ s)

/-- The type (II) simplices of `h : A.PairingCore`, as a family indexed by `h.ι`. -/
@[simps!]
def type₂ (s : h.ι) : A.N :=
  Subcomplex.N.mk (X.δ (h.index s) (h.simplex s)) (h.nonDegenerate₂ s)
    (h.notMem₂ s)

lemma injective_type₁ : Function.Injective h.type₁ :=
  fun _ _ hst ↦ h.injective_type₁' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

lemma injective_type₂ : Function.Injective h.type₂ :=
  fun s t hst ↦ h.injective_type₂' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

lemma type₁_ne_type₂ (s t : h.ι) : h.type₁ s ≠ h.type₂ t := by
  simpa only [ne_eq, N.ext_iff, SSet.N.ext_iff] using! h.type₁_ne_type₂' s t

lemma surjective (x : A.N) :
    ∃ (s : h.ι), x = h.type₁ s ∨ x = h.type₂ s := by
  obtain ⟨s, _ | _⟩ := h.surjective' x
  · exact ⟨s, Or.inl (by rwa [N.ext_iff, SSet.N.ext_iff])⟩
  · exact ⟨s, Or.inr (by rwa [N.ext_iff, SSet.N.ext_iff])⟩

/-- The type (I) simplices of `h : A.PairingCore`, as a subset of `A.N`. -/
def I : Set A.N := Set.range h.type₁

/-- The type (II) simplices of `h : A.PairingCore`, as a subset of `A.N`. -/
def II : Set A.N := Set.range h.type₂

/-- The bijection `h.ι ≃ h.I` when `h : A.PairingCore`. -/
@[simps! apply_coe]
noncomputable def equivI : h.ι ≃ h.I := Equiv.ofInjective _ h.injective_type₁

/-- The bijection `h.ι ≃ h.II` when `h : A.PairingCore`. -/
@[simps! apply_coe]
noncomputable def equivII : h.ι ≃ h.II := Equiv.ofInjective _ h.injective_type₂

/-- The pairing induced by `h : A.PairingCore`. -/
@[simps I II]
noncomputable def pairing : A.Pairing where
  I := h.I
  II := h.II
  inter := by
    ext s
    simp only [I, II, Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false,
      iff_false, not_and, not_exists, forall_exists_index]
    rintro t rfl s
    exact (h.type₁_ne_type₂ t s).symm
  union := by
    ext s
    have := h.surjective s
    simp only [I, II, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    aesop
  p := h.equivII.symm.trans h.equivI

@[simp]
lemma pairing_p_equivII (x : h.ι) :
    DFunLike.coe (F := h.II ≃ h.I) h.pairing.p (h.equivII x) = h.equivI x := by
  simp [pairing]

@[simp]
lemma pairing_p_symm_equivI (x : h.ι) :
    DFunLike.coe (F := h.I ≃ h.II) h.pairing.p.symm (h.equivI x) = h.equivII x := by
  simp [pairing]

set_option backward.defeqAttrib.useBackward true in
lemma type₁_pairing (x : h.ι) :
    h.type₁ x = h.pairing.p (h.equivII x) := by
  simp +instances

/-- The condition that `h : A.PairingCore` is proper, i.e. for each `s : h.ι`,
the type (II) simplex `h.type₂ s` is uniquely a `1`-codimensional
face of the type (I) simplex `h.type₁ s`. -/
class IsProper : Prop where
  isUniquelyCodimOneFace (s : h.ι) :
    S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s).toS

lemma isUniquelyCodimOneFace [h.IsProper] (s : h.ι) :
    S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s).toS :=
  IsProper.isUniquelyCodimOneFace _

instance [X.Nonsingular] : h.IsProper where
  isUniquelyCodimOneFace s :=
    (S.IsUniquelyCodimOneFace.iff _ _).2
      (existsUnique_of_exists_of_unique ⟨_, rfl⟩
        (fun _ _ hi hj ↦ Nonsingular.δ_injective _
          (h.nonDegenerate₁ s) _ _ (hi.trans hj.symm)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [h.IsProper] : h.pairing.IsProper where
  isUniquelyCodimOneFace x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    simpa using h.isUniquelyCodimOneFace s

lemma isProper_pairing_iff :
    h.pairing.IsProper ↔ h.IsProper := by
  refine ⟨fun _ ↦ ⟨fun s ↦ ?_⟩, fun _ ↦ inferInstance⟩
  simpa [type₁_pairing] using h.pairing.isUniquelyCodimOneFace (h.equivII s)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma isUniquelyCodimOneFace_index [h.IsProper] (s : h.ι) :
    (h.isUniquelyCodimOneFace s).index rfl = h.index s := by
  symm
  simp [← (h.isUniquelyCodimOneFace s).δ_eq_iff]

set_option backward.isDefEq.respectTransparency false in
lemma isUniquelyCodimOneFace_index_coe
    [h.IsProper] (s : h.ι) {d : ℕ} (hd : h.dim s = d) :
    ((h.isUniquelyCodimOneFace s).index hd).val = (h.index s).val := by
  subst hd
  simp

/-- The condition that `h : A.PairingCore` involves only inner horns. -/
class IsInner where
  ne_zero (s : h.ι) : h.index s ≠ 0
  ne_last (s : h.ι) : h.index s ≠ Fin.last _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [h.IsInner] [h.IsProper] : h.pairing.IsInner where
  ne_zero x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_zero s
  ne_last x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_last s

/-- The ancestrality relation on the index type of `h : A.PairingCore`. -/
def AncestralRel (s t : h.ι) : Prop :=
  s ≠ t ∧ h.type₂ s < h.type₁ t

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma ancestralRel_iff (s t : h.ι) :
    h.AncestralRel s t ↔ h.pairing.AncestralRel (h.equivII s) (h.equivII t) := by
  simp [AncestralRel, Pairing.AncestralRel]

/-- When the ancestrality relation is well founded, we say that `h : A.PairingCore`
is regular. -/
class IsRegular (h : A.PairingCore) extends h.IsProper where
  wf (h) : WellFounded h.AncestralRel

set_option backward.isDefEq.respectTransparency.types false in
instance [h.IsRegular] : h.pairing.IsRegular where
  wf := by
    have := IsRegular.wf h
    rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
    exact ⟨fun ⟨f, hf⟩ ↦ this.false
      ⟨fun n ↦ h.equivII.symm (f n), fun n ↦ by simpa [ancestralRel_iff] using hf n⟩⟩

lemma isRegular_pairing_iff (h : A.PairingCore) :
    h.pairing.IsRegular ↔ h.IsRegular := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : h.IsProper := by
    rw [← isProper_pairing_iff]
    infer_instance
  constructor
  have := h.pairing.wf
  rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
  exact ⟨fun ⟨f, hf⟩ ↦ this.false
    ⟨fun n ↦ h.equivII (f n), fun n ↦ by simpa [ancestralRel_iff] using hf n⟩⟩

end PairingCore

end SSet.Subcomplex
