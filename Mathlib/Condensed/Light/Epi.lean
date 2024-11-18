/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.PiProd
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Coherent.SequentialLimit
import Mathlib.Condensed.Light.Limits
/-!

# Epimorphisms of light condensed objects

This file characterises epimorphisms in light condensed sets and modules as the locally surjective
morphisms. Here, the condition of locally surjective is phrased in terms of continuous surjections
of light profinite sets.
-/

universe v u w u' v'

open CategoryTheory Sheaf Limits ConcreteCategory GrothendieckTopology

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike
  Abelian.hasFiniteBiproducts

namespace LightCondensed

variable (A : Type u') [Category.{v'} A] [ConcreteCategory.{w} A]
  [PreservesFiniteProducts (CategoryTheory.forget A)]

variable {X Y : LightCondensed.{u} A} (f : X ⟶ Y)

lemma isLocallySurjective_iff_locallySurjective_on_lightProfinite : IsLocallySurjective f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [coherentTopology.isLocallySurjective_iff,
    regularTopology.isLocallySurjective_iff]
  simp_rw [LightProfinite.effectiveEpi_iff_surjective]

end LightCondensed

namespace LightCondSet

variable {X Y : LightCondSet.{u}} (f : X ⟶ Y)

lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R] {X Y : LightCondMod.{u} R} (f : X ⟶ Y)

lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

instance : (LightCondensed.forget R).ReflectsEpimorphisms where
  reflects f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.val).mpr hf

instance : (LightCondensed.forget R).PreservesEpimorphisms where
  preserves f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.val).mp hf

end LightCondMod

namespace LightCondensed

variable (R : Type*) [Ring R]
variable {F : ℕᵒᵖ ⥤ LightCondMod R} {c : Cone F} (hc : IsLimit c)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))

include hc hF in
lemma epi_π_app_zero_of_epi : Epi (c.π.app ⟨0⟩) := by
  apply Functor.epi_of_epi_map (forget R)
  change Epi (((forget R).mapCone c).π.app ⟨0⟩)
  apply coherentTopology.epi_π_app_zero_of_epi
  · simp only [LightProfinite.effectiveEpi_iff_surjective]
    exact fun _ h ↦ Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit _) h
  · have := (freeForgetAdjunction R).isRightAdjoint
    exact isLimitOfPreserves _ hc
  · exact fun _ ↦ (forget R).map_epi _

section Products

section General

variable {C : Type*}
variable {M N : ℕ → C} -- [∀ n, Epi (f n)]

private lemma functorObj_eq_pos {n m : ℕ} (h : m < n) :
    (fun i ↦ if _ : i < n then M i else N i) m = M m := dif_pos h

private lemma functorObj_eq_neg {n m : ℕ} (h : ¬(m < n)) :
    (fun i ↦ if _ : i < n then M i else N i) m = N m := dif_neg h

variable [Category C] (f : ∀ n, M n ⟶ N n)
variable [HasProductsOfShape ℕ C]

private noncomputable def functorObj : ℕ → C :=
  fun n ↦ ∏ᶜ (fun m ↦ if _ : m < n then M m else N m)

private noncomputable def functorObjProj (n : ℕ) : (functorObj (M := M) (N := N)) n ⟶ N n :=
  Pi.π (fun m ↦ if _ : m < n then M m else N m) n ≫ eqToHom (functorObj_eq_neg (by omega))

private noncomputable def functorObjProj_pos (n m : ℕ) (h : m < n) :
    (functorObj (M := M) (N := N)) n ⟶ M m :=
  Pi.π (fun m ↦ if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_pos (by omega))

private noncomputable def functorObjProj_neg (n m : ℕ) (h : ¬(m < n)) :
    (functorObj (M := M) (N := N)) n ⟶ N m :=
  Pi.π (fun m ↦ if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_neg (by omega))

private noncomputable def functorMap : ∀ n,
    functorObj (M := M) (N := N) (n + 1) ⟶ functorObj (M := M) (N := N) n := by
  intro n
  refine Limits.Pi.map fun m ↦ if h : m < n then eqToHom ?_ else
    if h' : m < n + 1 then eqToHom ?_ ≫ f m ≫ eqToHom ?_ else eqToHom ?_
  · split_ifs
    · rfl
    · omega
  all_goals split_ifs; rfl

private lemma functorMap_commSq_succ (n : ℕ) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE (by omega : n ≤ n+1)).op ≫ Pi.π _ n ≫
      eqToHom (functorObj_eq_neg (by omega : ¬(n < n))) =
        (Pi.π (fun i ↦ if _ : i < (n + 1) then M i else N i) n) ≫
          eqToHom (functorObj_eq_pos (by omega)) ≫ f n := by
  simp [functorMap]

private lemma functorMap_commSq_aux {n m k : ℕ} (h : n ≤ m) (hh : ¬(k < m)) :
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

private lemma functorMap_commSq {n m : ℕ} (h : ¬(m < n)) :
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
        Functor.ofOpSequence_map_homOfLE_succ, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
        one_ne_zero]
      have : homOfLE (by omega : n ≤ m + 1 + 1) =
          homOfLE (by omega : n ≤ m + 1) ≫ homOfLE (by omega : m + 1 ≤ m + 1 + 1) := by simp
      rw [this, op_comp, Functor.map_comp]
      simp only [Functor.ofOpSequence_obj, homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ,
        Category.assoc, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero]
      congr 1
      exact functorMap_commSq_aux f (by omega) (by omega)

private noncomputable def cone : Cone (Functor.ofOpSequence (functorMap f)) where
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
    split_ifs
    · simp [dif_pos (by omega : m < n + 1)]
    · by_cases h' : m < n + 1
      · simp [dif_pos h']
      · simp [dif_neg h']

private lemma cone_π_app (n : ℕ) : (cone f).π.app ⟨n⟩ =
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

private noncomputable def isLimit : IsLimit (cone f) where
  lift s := Pi.lift fun m ↦
    s.π.app ⟨m + 1⟩ ≫ Pi.π (fun i ↦ if _ : i < m + 1 then M i else N i) m ≫
      eqToHom (dif_pos (by omega : m < m + 1))
  fac s := by
    intro ⟨n⟩
    apply Pi.hom_ext
    intro m
    by_cases h : m < n
    · simp only [le_refl, Category.assoc, cone_π_app_comp_Pi_π_pos f _ _ h]
      simp only [dite_eq_ite, Functor.ofOpSequence_obj, le_refl, limit.lift_π_assoc, Fan.mk_pt,
        Discrete.functor_obj_eq_as, Fan.mk_π_app, Category.assoc, eqToHom_trans]
      have hh : m + 1 ≤ n := by omega
      rw [← s.w (homOfLE hh).op]
      simp only [Functor.const_obj_obj, Functor.ofOpSequence_obj, homOfLE_leOfHom, le_refl,
        Category.assoc]
      congr
      induction' hh using Nat.leRec with n hh ih
      · simp
      · have : homOfLE (Nat.le_succ_of_le hh) = homOfLE hh ≫ homOfLE (Nat.le_succ n) := by simp
        rw [this, op_comp, Functor.map_comp]
        simp only [Functor.ofOpSequence_obj, Nat.succ_eq_add_one, homOfLE_leOfHom,
          Functor.ofOpSequence_map_homOfLE_succ, le_refl, Category.assoc]
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
    · simp only [le_refl, Category.assoc]
      rw [cone_π_app_comp_Pi_π_neg f _ _ h]
      simp only [dite_eq_ite, Functor.ofOpSequence_obj, le_refl, limit.lift_π_assoc, Fan.mk_pt,
        Discrete.functor_obj_eq_as, Fan.mk_π_app, Category.assoc]
      slice_lhs 2 4 => erw [← functorMap_commSq f h]
      simp
  uniq s m h := by
    apply Pi.hom_ext
    intro n
    simp only [Functor.ofOpSequence_obj, le_refl, dite_eq_ite, limit.lift_π, Fan.mk_pt,
      Fan.mk_π_app, ← h ⟨n + 1⟩, Category.assoc]
    slice_rhs 2 3 => erw [cone_π_app_comp_Pi_π_pos f (n + 1) _ le_rfl]
    simp

end General

variable {R : Type u} [Ring R] {M N : ℕ → LightCondMod.{u} R} (f : ∀ n, M n ⟶ N n) [∀ n, Epi (f n)]

instance (n : ℕ) : Epi (functorMap f n) := by
  rw [functorMap, Pi.map_eq_prod_map (P := fun m : ℕ ↦ m < n + 1)]
  apply (config := { allowSynthFailures := true }) epi_comp
  apply (config := { allowSynthFailures := true }) epi_comp
  apply (config := { allowSynthFailures := true }) prod.map_epi
  · apply (config := { allowSynthFailures := true }) Pi.map_epi
    intro ⟨j, hj⟩
    split_ifs with hh
    · by_cases j < n
      · split_ifs
        infer_instance
      · split_ifs
        infer_instance
    · dsimp at hh
      omega
  · apply (config := { allowSynthFailures := true }) IsIso.epi_of_iso
    apply (config := { allowSynthFailures := true }) Pi.map_isIso
    intro ⟨i, hi⟩
    split_ifs with hh
    · dsimp at hh
      omega
    · by_cases i < n
      · omega
      · split_ifs
        infer_instance

instance : Epi (Limits.Pi.map f) := by
  let F : ℕᵒᵖ ⥤ LightCondMod R := Functor.ofOpSequence (functorMap f)
  have : Limits.Pi.map f = (cone f).π.app ⟨0⟩ := rfl
  rw [this]
  have := epi_π_app_zero_of_epi R (isLimit f) (fun n ↦ by simp; infer_instance)
  infer_instance

instance : (lim (J := Discrete ℕ) (C := LightCondMod R)).PreservesEpimorphisms where
  preserves f _ := by
    have : lim.map f = (Pi.isoLimit _).inv ≫ Limits.Pi.map (f.app ⟨·⟩) ≫ (Pi.isoLimit _).hom := by
      apply limit.hom_ext
      intro ⟨n⟩
      simp only [lim_obj, lim_map, limMap, IsLimit.map, limit.isLimit_lift, limit.lift_π,
        Cones.postcompose_obj_pt, limit.cone_x, Cones.postcompose_obj_π, NatTrans.comp_app,
        Functor.const_obj_obj, limit.cone_π, Pi.isoLimit, Limits.Pi.map, Category.assoc,
        limit.conePointUniqueUpToIso_hom_comp, Pi.cone_pt, Pi.cone_π, Discrete.natTrans_app,
        Discrete.functor_obj_eq_as]
      erw [IsLimit.conePointUniqueUpToIso_inv_comp_assoc]
      rfl
    rw [this]
    infer_instance

end Products

end LightCondensed
