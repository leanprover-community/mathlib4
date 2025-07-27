/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.PiProd
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Order.Interval.Finset.Nat
/-!

# ℕ-indexed products as sequential limits

Given sequences `M N : ℕ → C` of objects with morphisms `f n : M n ⟶ N n` for all `n`, this file
exhibits `∏ M` as the limit of the tower

```
⋯ → ∏_{n < m + 1} M n × ∏_{n ≥ m + 1} N n → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```

Further, we prove that the transition maps in this tower are epimorphisms, in the case when each
`f n` is an epimorphism and `C` has finite biproducts.
-/

namespace CategoryTheory.Limits.SequentialProduct

variable {C : Type*} {M N : ℕ → C}

lemma functorObj_eq_pos {n m : ℕ} (h : m < n) :
    (fun i ↦ if _ : i < n then M i else N i) m = M m := dif_pos h

lemma functorObj_eq_neg {n m : ℕ} (h : ¬(m < n)) :
    (fun i ↦ if _ : i < n then M i else N i) m = N m := dif_neg h

variable [Category C] (f : ∀ n, M n ⟶ N n) [HasProductsOfShape ℕ C]

variable (M N) in
/-- The product of the `m` first objects of `M` and the rest of the rest of `N` -/
noncomputable def functorObj : ℕ → C :=
  fun n ↦ ∏ᶜ (fun m ↦ if _ : m < n then M m else N m)

/-- The projection map from `functorObj M N n` to `M m`, when `m < n` -/
noncomputable def functorObjProj_pos (n m : ℕ) (h : m < n) :
    functorObj M N n ⟶ M m :=
  Pi.π (fun m ↦ if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_pos (by omega))

/-- The projection map from `functorObj M N n` to `N m`, when `m ≥ n` -/
noncomputable def functorObjProj_neg (n m : ℕ) (h : ¬(m < n)) :
    functorObj M N n ⟶ N m :=
  Pi.π (fun m ↦ if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_neg (by omega))

/-- The transition maps in the sequential limit of products -/
noncomputable def functorMap : ∀ n,
    functorObj M N (n + 1) ⟶ functorObj M N n := by
  intro n
  refine Limits.Pi.map fun m ↦ if h : m < n then eqToHom ?_ else
    if h' : m < n + 1 then eqToHom ?_ ≫ f m ≫ eqToHom ?_ else eqToHom ?_
  all_goals split_ifs; try rfl; try omega

lemma functorMap_commSq_succ (n : ℕ) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE (by omega : n ≤ n + 1)).op ≫ Pi.π _ n ≫
      eqToHom (functorObj_eq_neg (by omega : ¬(n < n))) =
        (Pi.π (fun i ↦ if _ : i < (n + 1) then M i else N i) n) ≫
          eqToHom (functorObj_eq_pos (by omega)) ≫ f n := by
  simp [functorMap]

lemma functorMap_commSq_aux {n m k : ℕ} (h : n ≤ m) (hh : ¬(k < m)) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE h).op ≫ Pi.π _ k ≫
      eqToHom (functorObj_eq_neg (by omega : ¬(k < n))) =
        (Pi.π (fun i ↦ if _ : i < m then M i else N i) k) ≫
          eqToHom (functorObj_eq_neg hh) := by
  induction' h using Nat.leRec with m h ih
  · simp
  · specialize ih (by omega)
    have : homOfLE (by omega : n ≤ m + 1) =
        homOfLE (by omega : n ≤ m) ≫ homOfLE (by omega : m ≤ m + 1) := by simp
    rw [this, op_comp, Functor.map_comp]
    slice_lhs 2 4 => rw [ih]
    simp only [Functor.ofOpSequence_obj, homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ,
      functorMap, dite_eq_ite, limMap_π_assoc, Discrete.functor_obj_eq_as, Discrete.natTrans_app]
    split_ifs
    simp [dif_neg (by omega : ¬(k < m))]

lemma functorMap_commSq {n m : ℕ} (h : ¬(m < n)) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE (by omega : n ≤ m + 1)).op ≫ Pi.π _ m ≫
      eqToHom (functorObj_eq_neg (by omega : ¬(m < n))) =
        (Pi.π (fun i ↦ if _ : i < m + 1 then M i else N i) m) ≫
          eqToHom (functorObj_eq_pos (by omega)) ≫ f m := by
  cases m with
  | zero =>
      have : n = 0 := by omega
      subst this
      simp [functorMap]
  | succ m =>
      rw [← functorMap_commSq_succ f (m + 1)]
      simp only [Functor.ofOpSequence_obj, homOfLE_leOfHom, dite_eq_ite,
        Functor.ofOpSequence_map_homOfLE_succ]
      have : homOfLE (by omega : n ≤ m + 1 + 1) =
          homOfLE (by omega : n ≤ m + 1) ≫ homOfLE (by omega : m + 1 ≤ m + 1 + 1) := by simp
      rw [this, op_comp, Functor.map_comp]
      simp only [Functor.ofOpSequence_obj, homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ,
        Category.assoc]
      congr 1
      exact functorMap_commSq_aux f (by omega) (by omega)

/--
The cone over the tower
```
⋯ → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```
with cone point `∏ M`. This is a limit cone, see `CategoryTheory.Limits.SequentialProduct.isLimit`.
-/
noncomputable def cone : Cone (Functor.ofOpSequence (functorMap f)) where
  pt := ∏ᶜ M
  π := by
    refine NatTrans.ofOpSequence
      (fun n ↦ Limits.Pi.map fun m ↦ if h : m < n then eqToHom (functorObj_eq_pos h).symm else
        f m ≫ eqToHom (functorObj_eq_neg h).symm) (fun n ↦ ?_)
    apply Limits.Pi.hom_ext
    intro m
    simp only [Functor.const_obj_obj, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.const_obj_map, Category.id_comp, limMap_π, Discrete.functor_obj_eq_as,
      Discrete.natTrans_app, Functor.ofOpSequence_map_homOfLE_succ, functorMap, Category.assoc,
      limMap_π_assoc]
    split
    · simp [dif_pos (by omega : m < n + 1)]
    · split
      all_goals simp

lemma cone_π_app (n : ℕ) : (cone f).π.app ⟨n⟩ =
    Limits.Pi.map fun m ↦ if h : m < n then eqToHom (functorObj_eq_pos h).symm else
    f m ≫ eqToHom (functorObj_eq_neg h).symm := rfl

@[reassoc]
lemma cone_π_app_comp_Pi_π_pos (m n : ℕ) (h : n < m) : (cone f).π.app ⟨m⟩ ≫
    Pi.π (fun i ↦ if _ : i < m then M i else N i) n =
    Pi.π _ n ≫ eqToHom (functorObj_eq_pos h).symm := by
  simp only [Functor.const_obj_obj, dite_eq_ite, Functor.ofOpSequence_obj, cone_π_app, limMap_π,
    Discrete.functor_obj_eq_as, Discrete.natTrans_app]
  rw [dif_pos h]

@[reassoc]
lemma cone_π_app_comp_Pi_π_neg (m n : ℕ) (h : ¬(n < m)) : (cone f).π.app ⟨m⟩ ≫ Pi.π _ n =
    Pi.π _ n ≫ f n ≫ eqToHom (functorObj_eq_neg h).symm := by
  simp only [Functor.const_obj_obj, dite_eq_ite, Functor.ofOpSequence_obj, cone_π_app, limMap_π,
    Discrete.functor_obj_eq_as, Discrete.natTrans_app]
  rw [dif_neg h]

/--
The cone over the tower
```
⋯ → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```
with cone point `∏ M` is indeed a limit cone.
-/
noncomputable def isLimit : IsLimit (cone f) where
  lift s := Pi.lift fun m ↦
    s.π.app ⟨m + 1⟩ ≫ Pi.π (fun i ↦ if _ : i < m + 1 then M i else N i) m ≫
      eqToHom (dif_pos (by omega : m < m + 1))
  fac s := by
    intro ⟨n⟩
    apply Pi.hom_ext
    intro m
    by_cases h : m < n
    · simp only [Category.assoc, cone_π_app_comp_Pi_π_pos f _ _ h]
      simp only [dite_eq_ite, Functor.ofOpSequence_obj, limit.lift_π_assoc, Fan.mk_pt,
        Discrete.functor_obj_eq_as, Fan.mk_π_app, Category.assoc, eqToHom_trans]
      have hh : m + 1 ≤ n := by omega
      rw [← s.w (homOfLE hh).op]
      simp only [Functor.const_obj_obj, Functor.ofOpSequence_obj, homOfLE_leOfHom,
        Category.assoc]
      congr
      induction' hh using Nat.leRec with n hh ih
      · simp
      · have : homOfLE (Nat.le_succ_of_le hh) = homOfLE hh ≫ homOfLE (Nat.le_succ n) := by simp
        rw [this, op_comp, Functor.map_comp]
        simp only [Functor.ofOpSequence_obj, Nat.succ_eq_add_one, homOfLE_leOfHom,
          Functor.ofOpSequence_map_homOfLE_succ, Category.assoc]
        have h₁ : (if _ : m < m + 1 then M m else N m) = if _ : m < n then M m else N m := by
          rw [dif_pos (by omega), dif_pos (by omega)]
        have h₂ : (if _ : m < n then M m else N m) = if _ : m < n + 1 then M m else N m := by
          rw [dif_pos h, dif_pos (by omega)]
        rw [← eqToHom_trans h₁ h₂]
        slice_lhs 2 4 => rw [ih (by omega)]
        simp only [functorMap, dite_eq_ite, Pi.π, limMap_π_assoc, Discrete.functor_obj_eq_as,
          Discrete.natTrans_app]
        split_ifs
        rw [dif_pos (by omega)]
        simp
    · simp only [Category.assoc]
      rw [cone_π_app_comp_Pi_π_neg f _ _ h]
      simp only [dite_eq_ite, Functor.ofOpSequence_obj, limit.lift_π_assoc, Fan.mk_pt,
        Discrete.functor_obj_eq_as, Fan.mk_π_app, Category.assoc]
      slice_lhs 2 4 => erw [← functorMap_commSq f h]
      simp
  uniq s m h := by
    apply Pi.hom_ext
    intro n
    simp only [Functor.ofOpSequence_obj, dite_eq_ite, limit.lift_π, Fan.mk_pt,
      Fan.mk_π_app, ← h ⟨n + 1⟩, Category.assoc]
    slice_rhs 2 3 => erw [cone_π_app_comp_Pi_π_pos f (n + 1) _ (by omega)]
    simp

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasCountableProducts C] [∀ n, Epi (f n)]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

lemma functorMap_epi (n : ℕ) : Epi (functorMap f n) := by
  rw [functorMap, Pi.map_eq_prod_map (P := fun m : ℕ ↦ m < n + 1)]
  apply (config := { allowSynthFailures := true }) epi_comp
  apply (config := { allowSynthFailures := true }) epi_comp
  apply (config := { allowSynthFailures := true }) prod.map_epi
  · apply (config := { allowSynthFailures := true }) Pi.map_epi
    intro ⟨_, _⟩
    split
    all_goals infer_instance
  · apply (config := { allowSynthFailures := true }) IsIso.epi_of_iso
    apply (config := { allowSynthFailures := true }) Pi.map_isIso
    intro ⟨_, _⟩
    split
    all_goals infer_instance
end

end CategoryTheory.Limits.SequentialProduct
