/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The mapping cocone

Given a morphism `φ : K ⟶ L` of cochain complexes, the mapping cone
allows to obtain a triangle `K ⟶ L ⟶ mappingCone φ ⟶ ...`. In this
file, we define the mapping cocone, which fits in a rotated triangle:
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`.

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex Pretriangulated

open CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The mapping cocone of a morphism `φ : K ⟶ L` of cochain complexes: it is
`(mappingCone φ)⟦(-1 : ℤ)⟧`. -/
noncomputable def mappingCocone [HasHomotopyCofiber φ] :
    CochainComplex C ℤ := (mappingCone φ)⟦(-1 : ℤ)⟧

variable [HasHomotopyCofiber φ]

/-- The first projection `mappingCocone φ ⟶ K`. -/
noncomputable def fst : mappingCocone φ ⟶ K :=
  -((mappingCone.fst φ).leftShift (-1) 0 (add_neg_cancel 1)).homOf

/-- The second projection in `Cochain (mappingCocone φ) L (-1)`. -/
noncomputable def snd : Cochain (mappingCocone φ) L (-1) :=
  (mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)

/-- The left inclusion in `Cochain K (mappingCocone φ) 0`. -/
noncomputable def inl : Cochain K (mappingCocone φ) 0 :=
  (mappingCone.inl φ).rightShift (-1) 0 (zero_add _)

/-- The right inclusion in `Cocycle L (mappingCocone φ) 1`. -/
noncomputable def inr : Cocycle L (mappingCocone φ) 1 :=
  (Cocycle.ofHom (mappingCone.inr φ)).rightShift (-1) 1 (by lia)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inl_v_fst_f (p : ℤ) :
    (inl φ).v p p (add_zero p) ≫ (fst φ).f p = 𝟙 _ := by
  simp [inl, fst, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inl_v_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (inl φ).v p p (add_zero p) ≫ (snd φ).v p q hpq = 0 := by
  obtain rfl : q = p + -1 := by lia
  simp [inl, snd, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ hpq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inr_v_fst_f (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (fst φ).f q = 0 := by
  simp [inr, fst, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ hpq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inr_v_snd_v (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (snd φ).v q p (by lia) = 𝟙 _ := by
  simp [inr, snd, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

set_option backward.isDefEq.respectTransparency false in
lemma id_X (p q : ℤ) (hpq : p + -1 = q) :
    (fst φ).f p ≫ (inl φ).v p p (add_zero p) +
      (snd φ).v p q hpq ≫ (inr φ).1.v q p (by lia) = 𝟙 _ := by
  obtain rfl : q = p + -1 := by lia
  simp [fst, inl, snd, inr, mappingCocone,
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ hpq,
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Int.negOnePow_even 2 ⟨1, rfl⟩,
    mappingCone.id_X φ (p + -1) p (by lia)]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

/-- Constructor for cochains from `mappingCocone`. -/
noncomputable def descCochain : Cochain (mappingCocone φ) M m :=
  (-m + 1).negOnePow • (mappingCone.descCochain φ α β h).leftShift (-1) m (by lia)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inl_v_descCochain_v (p q : ℤ) (hpq : p + m = q) :
    (inl φ).v p p (add_zero _) ≫ (descCochain φ α β h).v p q hpq = α.v p q hpq := by
  simp [inl, descCochain, mappingCocone,
    Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia), smul_smul,
    Cochain.leftShift_v (n := n) _ (-1) m (by lia) _ _ hpq (p + -1) (by lia)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inr_v_descCochain_v (p q : ℤ) (hpq : p + 1 = q) (r : ℤ) (hr : q + m = r) :
    (inr φ).1.v p q hpq ≫ (descCochain φ α β h).v q r hr = β.v p r (by lia) := by
  obtain rfl : p = q + -1 := by lia
  simp [inr, descCochain, mappingCocone, smul_smul,
    Cochain.rightShift_v _ _ _ _ _ _ hpq _ (add_zero (q + -1)),
    Cochain.leftShift_v (n := n) _ _ _ _ _ r _ (q + -1) (by lia)]

@[simp]
lemma inl_comp_descCochain :
    (inl φ).comp (descCochain φ α β h) (zero_add m) = α := by
  cat_disch

@[simp]
lemma inr_comp_descCochain :
    (inr φ).1.comp (descCochain φ α β h) (by lia) = β := by
  ext p q hpq
  simp [Cochain.comp_v (n₂ := m) _ _ _ _ (p + 1) q rfl (by lia)]

set_option linter.hashCommand false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

#guard_msgs in
open Lean Elab Command Term Meta in
elab "#elab_if " cond:term " in " cmd:command : command => do
  if (← liftTermElabM do
    let e ← elabTerm cond none
    synthesizeSyntheticMVarsNoPostponing
    let e ← if (← isDefEq (← inferType e) (mkConst ``Bool)) then pure e else mkDecide e
    unsafe evalExpr Bool (mkConst ``Bool) e
  ) then elabCommand cmd

#elab_if Lean.versionString == "4.30.0-rc2" in
/--
[grind] Issues
  [issue] monomial expected, found numeral
        -1
      internalizing as variable
  [issue] monomial expected, found numeral
        -1
      internalizing as variable
  [issue] `grind linarith` term with unexpected instance
        (mappingCone.snd φ).v (p + -1) (p + -1) ⋯ ≫ (δ (m + 1) (m + 2) β).v (p + -1) q ⋯ +
          (m.negOnePow • (↑(mappingCone.fst φ)).v (p + -1) p ⋯ ≫ φ.f p ≫ β.v p q ⋯ +
            (↑(mappingCone.fst φ)).v (p + -1) p ⋯ ≫ (δ m (m + 1) α).v p q ⋯)
-/
#guard_msgs (substring := true) in
set_option backward.isDefEq.respectTransparency false in
lemma δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ m n (descCochain φ α β h) =
      (Cochain.ofHom (fst φ)).comp
        (δ m n α + m.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (zero_add n) +
      (snd φ).comp (δ n n' β) (by sorry) := by
  dsimp [descCochain, fst, snd, mappingCocone]
  ext p q hpq
  subst h
  obtain rfl : n' = m + 2 := by sorry
  simp [Cochain.δ_leftShift _ (-1) _ (m + 1) _ (m + 2) (by sorry),
    mappingCone.δ_descCochain (m := m) (n := m + 1) _ _ _ _ (m + 2) (by sorry),
    Cochain.leftShift_v (n := 1) _ _ _ _ p p _ (p + -1) (by sorry),
    Cochain.leftShift_v (n := m + 2) _ (-1) _ _ _ q _ (p + -1) (by sorry),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.comp_v (n₁ := 1) _ _ _ (p + -1) p _ (by sorry) hpq,
    Cochain.comp_v (n₂ := m + 2) _ _ _ p (p + -1) q rfl (by sorry),
    smul_smul, Int.negOnePow_add, Int.negOnePow_even 2 ⟨1, rfl⟩]
  /- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  grind

#elab_if Lean.versionString == "4.29.0" in
set_option backward.isDefEq.respectTransparency false in
lemma δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ m n (descCochain φ α β h) =
      (Cochain.ofHom (fst φ)).comp
        (δ m n α + m.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (zero_add n) +
      (snd φ).comp (δ n n' β) (by sorry) := by
  dsimp [descCochain, fst, snd, mappingCocone]
  ext p q hpq
  subst h
  obtain rfl : n' = m + 2 := by sorry
  simp [Cochain.δ_leftShift _ (-1) _ (m + 1) _ (m + 2) (by sorry),
    mappingCone.δ_descCochain (m := m) (n := m + 1) _ _ _ _ (m + 2) (by sorry),
    Cochain.leftShift_v (n := 1) _ _ _ _ p p _ (p + -1) (by sorry),
    Cochain.leftShift_v (n := m + 2) _ (-1) _ _ _ q _ (p + -1) (by sorry),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.comp_v (n₁ := 1) _ _ _ (p + -1) p _ (by sorry) hpq,
    Cochain.comp_v (n₂ := m + 2) _ _ _ p (p + -1) q rfl (by sorry),
    smul_smul, Int.negOnePow_add, Int.negOnePow_even 2 ⟨1, rfl⟩]
  /- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  grind
