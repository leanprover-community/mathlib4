/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Cochains from or to single complexes

We introduce constructors `Cochain.fromSingleMk` and `Cocycle.fromSingleMk`
for cochains and cocycles from a single complex. We also introduce similar
definitions for cochains and cocyles to a single complex.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex

namespace HomComplex

variable {X : C} {K : CochainComplex C ℤ}

namespace Cochain

/-- Constructor for cochains from a single complex. -/
@[nolint unusedArguments]
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (_ : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n :=
  Cochain.single ((HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f) n

variable (X K) in
@[simp]
lemma fromSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    fromSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [fromSingleMk]

@[simp]
lemma fromSingleMk_v {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    (fromSingleMk f h).v p q h =
      (HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f := by
  simp [fromSingleMk]

lemma fromSingleMk_v_eq_zero {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (fromSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

lemma δ_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (n' q' : ℤ) (h' : p + n' = q') :
    δ n n' (fromSingleMk f h) = fromSingleMk (f ≫ K.d q q') h' := by
  by_cases hq : q + 1 = q'
  · dsimp only [fromSingleMk]
    rw [δ_single _ n n' (by lia) (p - 1) q' (by lia) hq]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K q q' (by simp; lia),
      fromSingleMk]

/-- Cochains of degree `n` from `(singleFunctor C p).obj X` to `K` identify
to `X ⟶ K.X q` when `p + n = q`. -/
noncomputable def fromSingleEquiv {p q n : ℤ} (h : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n ≃+ (X ⟶ K.X q) where
  toFun α := (HomologicalComplex.singleObjXSelf (.up ℤ) p X).inv ≫ α.v p q h
  invFun f := fromSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hp : p' = p
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  right_inv f := by simp
  map_add' := by simp

@[simp]
lemma fromSingleMk_add {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (f + g) h = fromSingleMk f h + fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_add _ _

@[simp]
lemma fromSingleMk_sub {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (f - g) h = fromSingleMk f h - fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_sub _ _

@[simp]
lemma fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (-f) h = -fromSingleMk f h :=
  (fromSingleEquiv h).symm.map_neg _

lemma fromSingleMk_surjective {p n : ℤ} (α : Cochain ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) :
    ∃ (f : X ⟶ K.X q), fromSingleMk f h = α :=
  (fromSingleEquiv h).symm.surjective α

/-- Constructor for cochains to a single complex. -/
@[nolint unusedArguments]
noncomputable def toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (_ : p + n = q) :
    Cochain K ((singleFunctor C q).obj X) n :=
  Cochain.single (f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv) n

variable (X K) in
@[simp]
lemma toSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    toSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [toSingleMk]

@[simp]
lemma toSingleMk_v {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    (toSingleMk f h).v p q h =
      f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv := by
  simp [toSingleMk]

lemma toSingleMk_v_eq_zero {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (toSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

lemma δ_toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (n' p' : ℤ) (h' : p' + n' = q) :
    δ n n' (toSingleMk f h) = n'.negOnePow • toSingleMk (K.d p' p ≫ f) h' := by
  by_cases hp : p' + 1 = p
  · dsimp only [toSingleMk]
    rw [δ_single _ n n' (by lia) p' (q + 1) (by lia) rfl]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K p' p (by simp; lia)]

/-- Cochains of degree `n` from `(singleFunctor C q).obj X` to `K` identify
to `K.X p ⟶ X` when `p + n = q`. -/
noncomputable def toSingleEquiv {p q n : ℤ} (h : p + n = q) :
    Cochain K ((singleFunctor C q).obj X) n ≃+ (K.X p ⟶ X) where
  toFun α := α.v p q h ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).hom
  invFun f := toSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hq : q' = q
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq).eq_of_tgt _ _
  right_inv f := by simp
  map_add' := by simp

@[simp]
lemma toSingleMk_add {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (f + g) h = toSingleMk f h + toSingleMk g h :=
  (toSingleEquiv h).symm.map_add _ _

@[simp]
lemma toSingleMk_sub {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (f - g) h = toSingleMk f h - toSingleMk g h :=
  (toSingleEquiv h).symm.map_sub _ _

@[simp]
lemma toSingleMk_neg {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (-f) h = -toSingleMk f h :=
  (toSingleEquiv h).symm.map_neg _

lemma toSingleMk_surjective {q n : ℤ} (α : Cochain K ((singleFunctor C q).obj X) n)
    (p : ℤ) (h : p + n = q) :
    ∃ (f : K.X p ⟶ X), toSingleMk f h = α :=
  (toSingleEquiv h).symm.surjective α

end Cochain

namespace Cocycle

/-- Constructor for cocycles from a single complex. -/
@[simps!]
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    Cocycle ((singleFunctor C p).obj X) K n :=
  Cocycle.mk (Cochain.fromSingleMk f h) _ rfl (by
    rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia), hf]
    simp)

lemma fromSingleMk_surjective {p n : ℤ} (α : Cocycle ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) (q' : ℤ) (hq' : q + 1 = q') :
    ∃ (f : X ⟶ K.X q) (hf : f ≫ K.d q q' = 0), fromSingleMk f h q' hq' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective α.1 q h
  have hα := α.δ_eq_zero (n + 1)
  rw [← hf, Cochain.δ_fromSingleMk _ _ _ q' (by lia)] at hα
  replace hα := Cochain.congr_v hα p q' (by lia)
  exact ⟨f, by simpa using hα, by ext : 1; assumption⟩

lemma fromSingleMk_add {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f + g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf + fromSingleMk g h q' hq' hg := by
  cat_disch

lemma fromSingleMk_sub {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f - g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf - fromSingleMk g h q' hq' hg := by
  cat_disch

lemma fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (-f) h q' hq' (by simp [hf]) = - fromSingleMk f h q' hq' hf := by
  cat_disch

variable (X K) in
@[simp]
lemma fromSingleMk_zero {p q : ℤ} {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') :
    fromSingleMk (0 : X ⟶ K.X q) h q' hq' (by simp) = 0 := by
  cat_disch

lemma fromSingleMk_mem_coboundaries_iff {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0)
    (q'' : ℤ) (hq'' : q'' + 1 = q) :
    fromSingleMk f h q' hq' hf ∈ coboundaries _ _ _ ↔
      ∃ (g : X ⟶ K.X q''), g ≫ K.d q'' q = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.fromSingleMk_surjective α q'' (by lia)
    refine ⟨g, ?_⟩
    rw [← hg, fromSingleMk_coe, Cochain.δ_fromSingleMk _ _ _ _ h] at hα
    exact (Cochain.fromSingleEquiv h).symm.injective hα
  · rintro ⟨g, rfl⟩
    exact ⟨Cochain.fromSingleMk g (by lia), Cochain.δ_fromSingleMk _ _ _ _ h⟩

/-- Constructor for cocycles to a single complex. -/
@[simps!]
noncomputable def toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    Cocycle K ((singleFunctor C q).obj X) n :=
  Cocycle.mk (Cochain.toSingleMk f h) _ rfl (by
    rw [Cochain.δ_toSingleMk _ _ _ p' (by lia), hf]
    simp)

lemma toSingleMk_surjective {q n : ℤ} (α : Cocycle K ((singleFunctor C q).obj X) n)
    (p : ℤ) (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p) :
    ∃ (f : K.X p ⟶ X) (hf : K.d p' p ≫ f = 0), toSingleMk f h p' hp' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.toSingleMk_surjective α.1 p h
  have hα := ((n + 1).negOnePow • α).δ_eq_zero (n + 1)
  rw [coe_units_smul, δ_units_smul, ← hf, Cochain.δ_toSingleMk _ _ _ p' (by lia),
    smul_smul, Int.units_mul_self, one_smul] at hα
  refine ⟨f, ?_, ?_⟩
  · simpa [← cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv] using
    Cochain.congr_v hα p' q (by lia)
  · ext : 1; assumption

lemma toSingleMk_add {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) :
    toSingleMk (f + g) h p' hp' (by simp [hf, hg]) =
      toSingleMk f h p' hp' hf + toSingleMk g h p' hp' hg := by
  cat_disch

lemma toSingleMk_sub {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) :
    toSingleMk (f - g) h p' hp' (by simp [hf, hg]) =
      toSingleMk f h p' hp' hf - toSingleMk g h p' hp' hg := by
  cat_disch

lemma toSingleMk_neg {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    toSingleMk (-f) h p' hp' (by simp [hf]) =
      - toSingleMk f h p' hp' hf := by
  cat_disch

variable (X K) in
@[simp]
lemma toSingleMk_zero {p q : ℤ} {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) :
    toSingleMk (0 : K.X p ⟶ X) h p' hp' (by simp) = 0 := by
  cat_disch

lemma toSingleMk_mem_coboundaries_iff {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    (p'' : ℤ) (hp'' : p + 1 = p'') :
    toSingleMk f h p' hp' hf ∈ coboundaries _ _ _ ↔
      ∃ (g : K.X p'' ⟶ X), K.d p p'' ≫ g = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.toSingleMk_surjective α p'' (by lia)
    refine ⟨n.negOnePow • g, ?_⟩
    rw [← hg, toSingleMk_coe, Cochain.δ_toSingleMk _ _ _ _ h] at hα
    exact (Cochain.toSingleEquiv h).symm.injective (by simpa)
  · rintro ⟨g, rfl⟩
    exact ⟨n.negOnePow • Cochain.toSingleMk g (by lia),
      by simp [Cochain.δ_toSingleMk _ _ _ _ h, smul_smul]⟩

end Cocycle

end HomComplex

end CochainComplex
