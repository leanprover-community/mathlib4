/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# Opposite categories of cochain complexes

We construct an equivalence of categories `CochainComplex.opEquivalence C`
between `(CochainComplex C ℤ)ᵒᵖ` and `CochainComplex Cᵒᵖ ℤ`, and we show
that two morphisms in `CochainComplex C ℤ` are homotopic iff they are
homotopic as morphisms in `CochainComplex Cᵒᵖ ℤ`.

-/

@[expose] public section

noncomputable section

open Opposite CategoryTheory Limits

variable (C : Type*) [Category* C]

namespace ComplexShape

/-- The embedding of the complex shape `up ℤ` in `down ℤ` given by `n ↦ -n`. -/
@[simps]
def embeddingUpIntDownInt : (up ℤ).Embedding (down ℤ) where
  f n := -n
  injective_f _ _ := by simp
  rel := by simp

instance : embeddingUpIntDownInt.IsRelIff where
  rel' := by dsimp; lia

/-- The embedding of the complex shape `down ℤ` in `up ℤ` given by `n ↦ -n`. -/
@[simps]
def embeddingDownIntUpInt : (down ℤ).Embedding (up ℤ) where
  f n := -n
  injective_f _ _ := by simp
  rel := by dsimp; lia

instance : embeddingDownIntUpInt.IsRelIff where
  rel' := by dsimp; lia

end ComplexShape

namespace ChainComplex

variable [HasZeroMorphisms C]

attribute [local simp] HomologicalComplex.XIsoOfEq in
/-- The equivalence of categories `ChainComplex C ℤ ≌ CochainComplex C ℤ`. -/
def cochainComplexEquivalence :
    ChainComplex C ℤ ≌ CochainComplex C ℤ where
  functor := ComplexShape.embeddingUpIntDownInt.restrictionFunctor C
  inverse := ComplexShape.embeddingDownIntUpInt.restrictionFunctor C
  unitIso :=
    NatIso.ofComponents (fun K ↦ HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ K.XIsoOfEq (by simp)))
  counitIso :=
    NatIso.ofComponents (fun K ↦ HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ K.XIsoOfEq (by simp)))

end ChainComplex

namespace CochainComplex

/-- The equivalence of categories `(CochainComplex C ℤ)ᵒᵖ ≌ CochainComplex Cᵒᵖ ℤ`. -/
def opEquivalence [HasZeroMorphisms C] :
    (CochainComplex C ℤ)ᵒᵖ ≌ CochainComplex Cᵒᵖ ℤ :=
  (HomologicalComplex.opEquivalence C (.up ℤ)).trans
    (ChainComplex.cochainComplexEquivalence _)

variable {C} [Preadditive C]

attribute [local simp] opEquivalence ChainComplex.cochainComplexEquivalence

section

variable {K L : CochainComplex C ℤ} {f g : K ⟶ L}

/-- Given an homotopy between morphisms of cochain complexes indexed by `ℤ`,
this is the corresponding homotopy between morphisms of cochain complexes
in the opposite category. -/
def homotopyOp (h : Homotopy f g) :
    Homotopy ((opEquivalence C).functor.map f.op)
      ((opEquivalence C).functor.map g.op) where
  hom p q := (h.hom (-q) (-p)).op
  zero p q hpq := by
    rw [h.zero, op_zero]
    dsimp at hpq ⊢
    lia
  comm n := by
    dsimp
    simp only [h.comm, op_add, add_left_inj]
    rw [add_comm]
    congr 1
    · rw [prevD_eq _ (j' := - (n + 1)) (by simp)]
      symm
      exact dNext_eq _ (i' := n + 1) (by simp)
    · rw [dNext_eq _ (i' := - (n - 1)) (by dsimp; lia)]
      symm
      exact prevD_eq _ (j' := n - 1) (by simp)

lemma homotopyOp_hom_eq (h : Homotopy f g)
    (p q p' q' : ℤ) (hp : p + p' = 0 := by lia) (hq : q + q' = 0 := by lia) :
    (homotopyOp h).hom p q =
      (L.XIsoOfEq (by dsimp; lia)).hom.op ≫ (h.hom q' p').op ≫
        (K.XIsoOfEq (by dsimp; lia)).hom.op := by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyOp]

/-- The homotopy between two morphisms of cochain complexes indexed by `ℤ`
which correspond to an homotopy between morphisms of cochain complexes
in the opposite category. -/
def homotopyUnop (h : Homotopy ((opEquivalence C).functor.map f.op)
    ((opEquivalence C).functor.map g.op)) :
    Homotopy f g where
  hom p q := (K.XIsoOfEq (by simp)).hom ≫ (h.hom (-q) (-p)).unop ≫ (L.XIsoOfEq (by simp)).hom
  zero p q hpq := by
    rw [h.zero, unop_zero, zero_comp, comp_zero]
    dsimp at hpq ⊢
    lia
  comm n := Quiver.Hom.op_inj (by
    have H (p q p' q' : ℤ) (hp : p = p') (hq : q = q') :
      h.hom p q = (L.XIsoOfEq (by simpa using hp.symm)).hom.op ≫ h.hom p' q' ≫
        (K.XIsoOfEq (by simpa)).hom.op := by
      subst hp hq
      simp
    obtain ⟨n, rfl⟩ : ∃ (m : ℤ), n = -m := ⟨-n , by simp⟩
    have := h.comm n
    dsimp at this
    rw [op_add, op_add, this, add_left_inj, add_comm]
    congr 1
    · refine (prevD_eq _ (j' := n - 1) (by dsimp; lia)).trans ?_
      rw [dNext_eq _ (i' := - (n - 1)) (by dsimp; lia)]
      dsimp
      simp [H (- -n) (- -(n - 1)) n (n - 1) (by lia) (by lia), ← op_comp_assoc]
    · refine (dNext_eq _ (i' := n + 1) (by dsimp)).trans ?_
      rw [prevD_eq _ (j' := - (n + 1)) (by simp)]
      dsimp
      simp [H (- -(n + 1)) (- -n) (n + 1) n (by simp) (by simp), ← op_comp_assoc, ← op_comp])

lemma homotopyUnop_hom_eq
    (h : Homotopy ((opEquivalence C).functor.map f.op)
      ((opEquivalence C).functor.map g.op))
    (p q p' q' : ℤ) (hp : p + p' = 0 := by lia) (hq : q + q' = 0 := by lia) :
    (homotopyUnop h).hom p q =
      (K.XIsoOfEq (by dsimp; lia)).hom ≫ (h.hom q' p').unop ≫
        (L.XIsoOfEq (by dsimp; lia)).hom := by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyUnop]

end

/-- Two morphisms of cochain complexes indexed by `ℤ` are homotopic iff
they are homotopic after the application of the functor
`(opEquivalence C).functor : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex Cᵒᵖ ℤ`. -/
def homotopyOpEquiv {K L : CochainComplex C ℤ} {f g : K ⟶ L} :
    Homotopy f g ≃ Homotopy ((opEquivalence C).functor.map f.op)
      ((opEquivalence C).functor.map g.op) where
  toFun h := homotopyOp h
  invFun h := homotopyUnop h
  left_inv h := by
    ext p q
    simp [homotopyUnop_hom_eq _ p q (-p) (-q),
      homotopyOp_hom_eq _ (-q) (-p) q p]
  right_inv h := by
    ext p q
    simp [homotopyOp_hom_eq _ p q (-p) (-q),
      homotopyUnop_hom_eq _ (-q) (-p) q p]

lemma exactAt_op {K : CochainComplex C ℤ} {n : ℤ} (hK : K.ExactAt n)
    (m : ℤ) (hm : n + m = 0 := by lia) :
    ((opEquivalence C).functor.obj (op K)).ExactAt m := by
  obtain rfl : n = -m := by lia
  rw [HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp),
    ← ShortComplex.exact_unop_iff]
  rwa [HomologicalComplex.exactAt_iff' _ (-(m + 1)) (-m) (-(m - 1)) (by grind [prev])
    (by grind [next])] at hK

lemma acyclic_op {K : CochainComplex C ℤ} (hK : K.Acyclic) :
   ((opEquivalence C).functor.obj (op K)).Acyclic :=
  fun n ↦ exactAt_op (hK (-n)) n

end CochainComplex
