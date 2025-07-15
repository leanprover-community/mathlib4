/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! Shifting cochains

Let `C` be a preadditive category. Given two cochain complexes (indexed by `ℤ`),
the type of cochains `HomComplex.Cochain K L n` of degree `n` was introduced
in `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean`. In this file, we
study how these cochains behave with respect to the shift on the complexes `K`
and `L`.

When `n`, `a`, `n'` are integers such that `h : n' + a = n`,
we obtain `rightShiftAddEquiv K L n a n' h : Cochain K L n ≃+ Cochain K (L⟦a⟧) n'`.
This definition does not involve signs, but the analogous definition
of `leftShiftAddEquiv K L n a n' h' : Cochain K L n ≃+ Cochain (K⟦a⟧) L n'`
when `h' : n + a = n'` does involve signs, as we follow the conventions
appearing in the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000].

## References
* [Brian Conrad, Grothendieck duality and base change][conrad2000]

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

namespace CochainComplex.HomComplex

namespace Cochain

variable (γ γ₁ γ₂ : Cochain K L n)

/-- The map `Cochain K L n → Cochain K (L⟦a⟧) n'` when `n' + a = n`. -/
def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cochain K (L⟦a⟧) n' :=
  Cochain.mk (fun p q hpq => γ.v p (p + n) rfl ≫
    (L.shiftFunctorObjXIso a q (p + n) (by omega)).inv)

lemma rightShift_v (a n' : ℤ) (hn' : n' + a = n) (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p + n = p') :
    (γ.rightShift a n' hn').v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a q p' (by rw [← hp', ← hpq, ← hn', add_assoc])).inv := by
  subst hp'
  dsimp only [rightShift]
  simp only [mk_v]

/-- The map `Cochain K L n → Cochain (K⟦a⟧) L n'` when `n + a = n'`. -/
def leftShift (a n' : ℤ) (hn' : n + a = n') : Cochain (K⟦a⟧) L n' :=
  Cochain.mk (fun p q hpq => (a * n' + ((a * (a-1))/2)).negOnePow •
    (K.shiftFunctorObjXIso a p (p + a) rfl).hom ≫ γ.v (p+a) q (by omega))

lemma leftShift_v (a n' : ℤ) (hn' : n + a = n') (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p' + n = q) :
    (γ.leftShift a n' hn').v p q hpq = (a * n' + ((a * (a - 1))/2)).negOnePow •
      (K.shiftFunctorObjXIso a p p'
        (by rw [← add_left_inj n, hp', add_assoc, add_comm a, hn', hpq])).hom ≫ γ.v p' q hp' := by
  obtain rfl : p' = p + a := by omega
  dsimp only [leftShift]
  simp only [mk_v]

/-- The map `Cochain K (L⟦a⟧) n' → Cochain K L n` when `n' + a = n`. -/
def rightUnshift {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => γ.v p (p + n') rfl ≫
    (L.shiftFunctorObjXIso a (p + n') q (by rw [← hpq, add_assoc, hn])).hom)

lemma rightUnshift_v {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n)
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p + n' = p') :
    (γ.rightUnshift n hn).v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a p' q (by rw [← hpq, ← hn, ← add_assoc, hp'])).hom := by
  subst hp'
  dsimp only [rightUnshift]
  simp only [mk_v]

/-- The map `Cochain (K⟦a⟧) L n' → Cochain K L n` when `n + a = n'`. -/
def leftUnshift {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => (a * n' + ((a * (a-1))/2)).negOnePow •
    (K.shiftFunctorObjXIso a (p - a) p (by omega)).inv ≫ γ.v (p-a) q (by omega))

lemma leftUnshift_v {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n')
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p' + n' = q) :
    (γ.leftUnshift n hn).v p q hpq = (a * n' + ((a * (a-1))/2)).negOnePow •
      (K.shiftFunctorObjXIso a p' p (by omega)).inv ≫ γ.v p' q (by omega) := by
  obtain rfl : p' = p - a := by omega
  rfl

/-- The map `Cochain K L n → Cochain (K⟦a⟧) (L⟦a⟧) n`. -/
def shift (a : ℤ) : Cochain (K⟦a⟧) (L⟦a⟧) n :=
  Cochain.mk (fun p q hpq => (K.shiftFunctorObjXIso a p _ rfl).hom ≫
    γ.v (p + a) (q + a) (by omega) ≫ (L.shiftFunctorObjXIso a q _ rfl).inv)

lemma shift_v (a : ℤ) (p q : ℤ) (hpq : p + n = q) (p' q' : ℤ)
    (hp' : p' = p + a) (hq' : q' = q + a) :
    (γ.shift a).v p q hpq = (K.shiftFunctorObjXIso a p p' hp').hom ≫
      γ.v p' q' (by rw [hp', hq', ← hpq, add_assoc, add_comm a, add_assoc]) ≫
      (L.shiftFunctorObjXIso a q q' hq').inv := by
  subst hp' hq'
  rfl

lemma shift_v' (a : ℤ) (p q : ℤ) (hpq : p + n = q) :
    (γ.shift a).v p q hpq = γ.v (p + a) (q + a) (by omega) := by
  simp only [shift_v γ a p q hpq _ _ rfl rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

@[simp]
lemma rightUnshift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (γ.rightShift a n' hn').rightUnshift n hn' = γ := by
  ext p q hpq
  simp only [rightUnshift_v _ n hn' p q hpq (p + n') rfl,
    γ.rightShift_v _ _ hn' p (p + n') rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.inv_hom_id, comp_id]

@[simp]
lemma rightShift_rightUnshift {a n' : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn' : n' + a = n) :
    (γ.rightUnshift n hn').rightShift a n' hn' = γ := by
  ext p q hpq
  simp only [(γ.rightUnshift n hn').rightShift_v a n' hn' p q hpq (p + n) rfl,
    γ.rightUnshift_v n hn' p (p + n) rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.hom_inv_id, comp_id]

@[simp]
lemma leftUnshift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (γ.leftShift a n' hn').leftUnshift n hn' = γ := by
  ext p q hpq
  rw [(γ.leftShift a n' hn').leftUnshift_v n hn' p q hpq (q-n') (by omega),
    γ.leftShift_v a n' hn' (q-n') q (by omega) p hpq, Linear.comp_units_smul,
    Iso.inv_hom_id_assoc, smul_smul, Int.units_mul_self, one_smul]

@[simp]
lemma leftShift_leftUnshift {a n' : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn' : n + a = n') :
    (γ.leftUnshift n hn').leftShift a n' hn' = γ := by
  ext p q hpq
  rw [(γ.leftUnshift n hn').leftShift_v a n' hn' p q hpq (q-n) (by omega),
    γ.leftUnshift_v n hn' (q-n) q (by omega) p hpq, Linear.comp_units_smul, smul_smul,
    Iso.hom_inv_id_assoc, Int.units_mul_self, one_smul]

@[simp]
lemma rightShift_add (a n' : ℤ) (hn' : n' + a = n) :
    (γ₁ + γ₂).rightShift a n' hn' = γ₁.rightShift a n' hn' + γ₂.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, add_v, add_comp]

@[simp]
lemma leftShift_add (a n' : ℤ) (hn' : n + a = n') :
    (γ₁ + γ₂).leftShift a n' hn' = γ₁.leftShift a n' hn' + γ₂.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by omega), add_v, comp_add, smul_add]

@[simp]
lemma shift_add (a : ℤ) :
    (γ₁ + γ₂).shift a = γ₁.shift a + γ₂.shift a := by
  ext p q hpq
  dsimp
  simp only [shift_v', add_v]

variable (K L)

/-- The additive equivalence `Cochain K L n ≃+ Cochain K L⟦a⟧ n'` when `n' + a = n`. -/
@[simps]
def rightShiftAddEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cochain K L n ≃+ Cochain K (L⟦a⟧) n' where
  toFun γ := γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by simp only [rightUnshift_rightShift]
  right_inv γ := by simp only [rightShift_rightUnshift]
  map_add' γ γ' := by simp only [rightShift_add]

/-- The additive equivalence `Cochain K L n ≃+ Cochain (K⟦a⟧) L n'` when `n + a = n'`. -/
@[simps]
def leftShiftAddEquiv (n a n' : ℤ) (hn' : n + a = n') :
    Cochain K L n ≃+ Cochain (K⟦a⟧) L n' where
  toFun γ := γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by simp only [leftUnshift_leftShift]
  right_inv γ := by simp only [leftShift_leftUnshift]
  map_add' γ γ' := by simp only [leftShift_add]

/-- The additive map `Cochain K L n →+ Cochain (K⟦a⟧) (L⟦a⟧) n`. -/
@[simps!]
def shiftAddHom (n a : ℤ) : Cochain K L n →+ Cochain (K⟦a⟧) (L⟦a⟧) n :=
  AddMonoidHom.mk' (fun γ => γ.shift a) (by intros; dsimp; simp only [shift_add])

variable (n)

@[simp]
lemma rightShift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain K L n).rightShift a n' hn' = 0 := by
  change rightShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]
lemma rightUnshift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain K (L⟦a⟧) n').rightUnshift n hn' = 0 := by
  change (rightShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]
lemma leftShift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain K L n).leftShift a n' hn' = 0 := by
  change leftShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]
lemma leftUnshift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain (K⟦a⟧) L n').leftUnshift n hn' = 0 := by
  change (leftShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]
lemma shift_zero (a : ℤ) :
    (0 : Cochain K L n).shift a = 0 := by
  change shiftAddHom K L n a 0 = 0
  apply map_zero

variable {K L n}

@[simp]
lemma rightShift_neg (a n' : ℤ) (hn' : n' + a = n) :
    (-γ).rightShift a n' hn' = -γ.rightShift a n' hn' := by
  change rightShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]
lemma rightUnshift_neg {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    (-γ).rightUnshift n hn = -γ.rightUnshift n hn := by
  change (rightShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]
lemma leftShift_neg (a n' : ℤ) (hn' : n + a = n') :
    (-γ).leftShift a n' hn' = -γ.leftShift a n' hn' := by
  change leftShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]
lemma leftUnshift_neg {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    (-γ).leftUnshift n hn = -γ.leftUnshift n hn := by
  change (leftShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]
lemma shift_neg (a : ℤ) :
    (-γ).shift a = -γ.shift a := by
  change shiftAddHom K L n a (-γ) = _
  apply map_neg

@[simp]
lemma rightUnshift_add {n' a : ℤ} (γ₁ γ₂ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    (γ₁ + γ₂).rightUnshift n hn = γ₁.rightUnshift n hn + γ₂.rightUnshift n hn := by
  change (rightShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

@[simp]
lemma leftUnshift_add {n' a : ℤ} (γ₁ γ₂ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    (γ₁ + γ₂).leftUnshift n hn = γ₁.leftUnshift n hn + γ₂.leftUnshift n hn := by
  change (leftShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

@[simp]
lemma rightShift_smul (a n' : ℤ) (hn' : n' + a = n) (x : R) :
    (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, smul_v, Linear.smul_comp]

@[simp]
lemma leftShift_smul (a n' : ℤ) (hn' : n + a = n') (x : R) :
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by omega), smul_v, Linear.comp_smul,
    smul_comm x]

@[simp]
lemma shift_smul (a : ℤ) (x : R) :
    (x • γ).shift a = x • (γ.shift a) := by
  ext p q hpq
  dsimp
  simp only [shift_v', smul_v]

variable (K L R)

/-- The linear equivalence `Cochain K L n ≃+ Cochain K L⟦a⟧ n'` when `n' + a = n` and
the category is `R`-linear. -/
@[simps!]
def rightShiftLinearEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cochain K L n ≃ₗ[R] Cochain K (L⟦a⟧) n' :=
  (rightShiftAddEquiv K L n a n' hn').toLinearEquiv
    (fun x γ => by dsimp; simp only [rightShift_smul])

/-- The additive equivalence `Cochain K L n ≃+ Cochain (K⟦a⟧) L n'` when `n + a = n'` and
the category is `R`-linear. -/
@[simps!]
def leftShiftLinearEquiv (n a n' : ℤ) (hn : n + a = n') :
    Cochain K L n ≃ₗ[R] Cochain (K⟦a⟧) L n' :=
  (leftShiftAddEquiv K L n a n' hn).toLinearEquiv
    (fun x γ => by dsimp; simp only [leftShift_smul])

/-- The linear map `Cochain K L n ≃+ Cochain (K⟦a⟧) (L⟦a⟧) n` when the category is `R`-linear. -/
@[simps!]
def shiftLinearMap (n a : ℤ) :
    Cochain K L n →ₗ[R] Cochain (K⟦a⟧) (L⟦a⟧) n where
  toAddHom := shiftAddHom K L n a
  map_smul' _ _ := by dsimp; simp only [shift_smul]

variable {K L R}

@[simp]
lemma rightShift_units_smul (a n' : ℤ) (hn' : n' + a = n) (x : Rˣ) :
    (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  apply rightShift_smul

@[simp]
lemma leftShift_units_smul (a n' : ℤ) (hn' : n + a = n') (x : Rˣ) :
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  apply leftShift_smul

@[simp]
lemma shift_units_smul (a : ℤ) (x : Rˣ) :
    (x • γ).shift a = x • (γ.shift a) := by
  ext p q hpq
  dsimp
  simp only [shift_v', units_smul_v]

@[simp]
lemma rightUnshift_smul {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) (x : R) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  change (rightShiftLinearEquiv  R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]
lemma rightUnshift_units_smul {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ)
    (hn : n' + a = n) (x : Rˣ) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  apply rightUnshift_smul

@[simp]
lemma leftUnshift_smul {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') (x : R) :
    (x • γ).leftUnshift n hn = x • γ.leftUnshift n hn := by
  change (leftShiftLinearEquiv  R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]
lemma leftUnshift_units_smul {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ)
    (hn : n + a = n') (x : Rˣ) :
    (x • γ).leftUnshift n hn = x • γ.leftUnshift n hn := by
  apply leftUnshift_smul

lemma rightUnshift_comp {m : ℤ} {a : ℤ} (γ' : Cochain L (M⟦a⟧) m) {nm : ℤ} (hnm : n + m = nm)
    (nm' : ℤ) (hnm' : nm + a = nm') (m' : ℤ) (hm' : m + a = m') :
    (γ.comp γ' hnm).rightUnshift nm' hnm' =
      γ.comp (γ'.rightUnshift m' hm') (by omega) := by
  ext p q hpq
  rw [(γ.comp γ' hnm).rightUnshift_v nm' hnm' p q hpq (p + n + m) (by omega),
    γ.comp_v γ' hnm p (p + n) (p + n + m) rfl rfl,
    comp_v _ _ (show n + m' = nm' by omega) p (p + n) q (by omega) (by omega),
    γ'.rightUnshift_v m' hm' (p + n) q (by omega) (p + n + m) rfl, assoc]

lemma leftShift_comp (a n' : ℤ) (hn' : n + a = n') {m t t' : ℤ} (γ' : Cochain L M m)
    (h : n + m = t) (ht' : t + a = t') :
    (γ.comp γ' h).leftShift a t' ht' = (a * m).negOnePow • (γ.leftShift a n' hn').comp γ'
      (by rw [← ht', ← h, ← hn', add_assoc, add_comm a, add_assoc]) := by
  ext p q hpq
  have h' : n' + m = t' := by omega
  dsimp
  simp only [Cochain.comp_v _ _ h' p (p + n') q rfl (by omega),
    γ.leftShift_v a n' hn' p (p + n') rfl (p + a) (by omega),
    (γ.comp γ' h).leftShift_v a t' (by omega) p q hpq (p + a) (by omega),
    smul_smul, Linear.units_smul_comp, assoc, Int.negOnePow_add, ← mul_assoc, ← h',
    comp_v _ _ h (p + a) (p + n') q (by omega) (by omega)]
  congr 2
  rw [add_comm n', mul_add, Int.negOnePow_add]

@[simp]
lemma leftShift_comp_zero_cochain (a n' : ℤ) (hn' : n + a = n') (γ' : Cochain L M 0) :
    (γ.comp γ' (add_zero n)).leftShift a n' hn' =
      (γ.leftShift a n' hn').comp γ' (add_zero n') := by
  rw [leftShift_comp γ a n' hn' γ' (add_zero _) hn', mul_zero, Int.negOnePow_zero, one_smul]

lemma δ_rightShift (a n' m' : ℤ) (hn' : n' + a = n) (m : ℤ) (hm' : m' + a = m) :
    δ n' m' (γ.rightShift a n' hn') = a.negOnePow • (δ n m γ).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by omega
    ext p q hpq
    dsimp
    rw [(δ n m γ).rightShift_v a m' hm' p q hpq _ rfl,
      δ_v n m hnm _ p (p+m) rfl (p+n) (p+1) (by omega) rfl,
      δ_v n' m' hnm' _ p q hpq (p+n') (p+1) (by omega) rfl,
      γ.rightShift_v a n' hn' p (p+n') rfl (p+n) rfl,
      γ.rightShift_v a n' hn' (p+1) q _ (p+m) (by omega)]
    simp only [shiftFunctorObjXIso, shiftFunctor_obj_d',
      Linear.comp_units_smul, assoc, HomologicalComplex.XIsoOfEq_inv_comp_d,
      add_comp, HomologicalComplex.d_comp_XIsoOfEq_inv, Linear.units_smul_comp, smul_add,
      add_right_inj, smul_smul]
    congr 1
    simp only [← hm', add_comm m', Int.negOnePow_add, ← mul_assoc,
      Int.units_mul_self, one_mul]
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by omega)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, rightShift_zero, smul_zero]

lemma δ_rightUnshift {a n' : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n)
    (m m' : ℤ) (hm' : m' + a = m) :
    δ n m (γ.rightUnshift n hn) = a.negOnePow • (δ n' m' γ).rightUnshift m hm' := by
  obtain ⟨γ', rfl⟩ := (rightShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [rightUnshift_rightShift, γ'.δ_rightShift a n' m' hn m hm', rightUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

lemma δ_leftShift (a n' m' : ℤ) (hn' : n + a = n') (m : ℤ) (hm' : m + a = m') :
    δ n' m' (γ.leftShift a n' hn') = a.negOnePow • (δ n m γ).leftShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by omega
    ext p q hpq
    dsimp
    rw [(δ n m γ).leftShift_v a m' hm' p q hpq (p+a) (by omega),
      δ_v n m hnm _ (p+a) q (by omega) (p+n') (p+1+a) (by omega) (by omega),
      δ_v n' m' hnm' _ p q hpq (p+n') (p+1) (by omega) rfl,
      γ.leftShift_v a n' hn' p (p+n') rfl (p+a) (by omega),
      γ.leftShift_v a n' hn' (p+1) q (by omega) (p+1+a) (by omega)]
    simp only [shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, id_comp, Linear.units_smul_comp, shiftFunctor_obj_d',
      Linear.comp_units_smul, smul_add, smul_smul]
    congr 2
    · rw [← hnm', add_comm n', mul_add, mul_one]
      simp only [Int.negOnePow_add, ← mul_assoc, Int.units_mul_self, one_mul]
    · simp only [← Int.negOnePow_add, ← hn', ← hm', ← hnm]
      congr 1
      linarith
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by omega)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, leftShift_zero, smul_zero]

lemma δ_leftUnshift {a n' : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n')
    (m m' : ℤ) (hm' : m + a = m') :
    δ n m (γ.leftUnshift n hn) = a.negOnePow • (δ n' m' γ).leftUnshift m hm' := by
  obtain ⟨γ', rfl⟩ := (leftShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [leftUnshift_leftShift, γ'.δ_leftShift a n' m' hn m hm', leftUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

@[simp]
lemma δ_shift (a m : ℤ) :
    δ n m (γ.shift a) = a.negOnePow • (δ n m γ).shift a := by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [shift_v', sub_add_cancel, shiftFunctor_obj_d',
      δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      δ_v n m hnm _ (p + a) (q + a) (by omega) (q - 1 + a) (p + 1 + a)
        (by omega) (by omega),
      smul_add, Linear.units_smul_comp, Linear.comp_units_smul, add_right_inj]
    rw [smul_comm]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, shift_zero, smul_zero]

lemma leftShift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (γ.rightShift a n' hn').leftShift a n hn' =
      (a * n + (a * (a - 1)) / 2).negOnePow • γ.shift a := by
  ext p q hpq
  simp only [leftShift_v _ a n hn' p q hpq (p + a) (by omega),
    rightShift_v _ a n' hn' (p + a) q (by omega) (q + a) (by omega), units_smul_v, shift_v']
  dsimp
  rw [id_comp, comp_id]

lemma rightShift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (γ.leftShift a n' hn').rightShift a n hn' =
      (a * n' + (a * (a - 1)) / 2).negOnePow • γ.shift a := by
  ext p q hpq
  simp only [rightShift_v _ a n hn' p q hpq (q + a) (by omega),
    leftShift_v _ a n' hn' p (q + a) (by omega) (p + a) (by omega), units_smul_v, shift_v']
  dsimp
  rw [id_comp, comp_id]

/-- The left and right shift of cochains commute only up to a sign. -/
lemma leftShift_rightShift_eq_negOnePow_rightShift_leftShift
    (a n' n'' : ℤ) (hn' : n' + a = n) (hn'' : n + a = n'') :
    (γ.rightShift a n' hn').leftShift a n hn' =
      a.negOnePow • (γ.leftShift a n'' hn'').rightShift a n hn'' := by
  rw [leftShift_rightShift, rightShift_leftShift, smul_smul, ← hn'', add_comm n a, mul_add,
    Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_mul_self,
    ← mul_assoc, ← mul_assoc, Int.units_mul_self, one_mul]

end Cochain

namespace Cocycle

/-- The map `Cocycle K L n → Cocycle K (L⟦a⟧) n'` when `n' + a = n`. -/
@[simps!]
def rightShift (γ : Cocycle K L n) (a n' : ℤ) (hn' : n' + a = n) :
    Cocycle K (L⟦a⟧) n' :=
  Cocycle.mk (γ.1.rightShift a n' hn') _ rfl (by
    simp only [Cochain.δ_rightShift _ a n' (n' + 1) hn' (n + 1) (by omega),
      δ_eq_zero, Cochain.rightShift_zero, smul_zero])

/-- The map `Cocycle K (L⟦a⟧) n' → Cocycle K L n` when `n' + a = n`. -/
@[simps!]
def rightUnshift {n' a : ℤ} (γ : Cocycle K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    Cocycle K L n :=
  Cocycle.mk (γ.1.rightUnshift n hn) _ rfl (by
    rw [Cochain.δ_rightUnshift _ n hn (n + 1) (n + 1 - a) (by omega),
      δ_eq_zero, Cochain.rightUnshift_zero, smul_zero])

/-- The map `Cocycle K L n → Cocycle (K⟦a⟧) L n'` when `n + a = n'`. -/
@[simps!]
def leftShift (γ : Cocycle K L n) (a n' : ℤ) (hn' : n + a = n') :
    Cocycle (K⟦a⟧) L n' :=
  Cocycle.mk (γ.1.leftShift a n' hn') _ rfl (by
    simp only [Cochain.δ_leftShift _ a n' (n' + 1) hn' (n + 1) (by omega),
      δ_eq_zero, Cochain.leftShift_zero, smul_zero])

/-- The map `Cocycle (K⟦a⟧) L n' → Cocycle K L n` when `n + a = n'`. -/
@[simps!]
def leftUnshift {n' a : ℤ} (γ : Cocycle (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    Cocycle K L n :=
  Cocycle.mk (γ.1.leftUnshift n hn) _ rfl (by
    rw [Cochain.δ_leftUnshift _ n hn (n + 1) (n + 1 + a) rfl,
      δ_eq_zero, Cochain.leftUnshift_zero, smul_zero])

/-- The map `Cocycle K L n → Cocycle (K⟦a⟧) (L⟦a⟧) n`. -/
@[simps!]
def shift (γ : Cocycle K L n) (a : ℤ) :
    Cocycle (K⟦a⟧) (L⟦a⟧) n :=
  Cocycle.mk (γ.1.shift a) _ rfl
    (by simp only [Cochain.δ_shift, δ_eq_zero, Cochain.shift_zero, smul_zero])

end Cocycle

end CochainComplex.HomComplex
