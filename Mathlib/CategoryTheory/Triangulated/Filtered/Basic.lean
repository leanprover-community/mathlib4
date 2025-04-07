/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw, Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Shift.Predicate
import Mathlib.CategoryTheory.Triangulated.Lemmas

/-!
# Filtered Triangulated Categories

-/

--set_option diagnostics true

noncomputable section

open CategoryTheory Preadditive Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory

open Category Pretriangulated ZeroObject

/-
We work in a preadditive category `C` equipped with an additive shift.
-/
variable {C : Type u} [Category.{v, u} C]

attribute [local instance] endofunctorMonoidalCategory

section

variable [HasShift C (ℤ × ℤ)]

instance Shift₁ : HasShift C ℤ where
  shift := (Discrete.addMonoidalFunctor (AddMonoidHom.inl ℤ ℤ)).comp HasShift.shift
  shiftMonoidal := by
    have := HasShift.shiftMonoidal (C := C) (A := ℤ × ℤ)
    infer_instance

variable (C) in
def FilteredShift := C

instance : Category (FilteredShift C) := by
  dsimp only [FilteredShift]
  infer_instance

noncomputable instance : HasShift (FilteredShift C) (ℤ × ℤ) := by
  dsimp only [FilteredShift]
  infer_instance

noncomputable instance : HasShift (FilteredShift C) ℤ where
  shift := (Discrete.addMonoidalFunctor (AddMonoidHom.inr ℤ ℤ)).comp HasShift.shift
  shiftMonoidal := by
    have := HasShift.shiftMonoidal (C := C) (A := ℤ × ℤ)
    infer_instance

instance [HasZeroObject C] : HasZeroObject (FilteredShift C) := by
  dsimp only [FilteredShift]
  infer_instance

instance [Preadditive C] : Preadditive (FilteredShift C) := by
  dsimp only [FilteredShift]
  infer_instance

variable (C) in
def shiftFunctor₂ (n : ℤ) : C ⥤ C := shiftFunctor (FilteredShift C) n

instance [Preadditive C] (n : ℤ) [(shiftFunctor C (Prod.mk (0 : ℤ) n)).Additive] :
    (shiftFunctor (FilteredShift C) n).Additive := by
  change (shiftFunctor C (Prod.mk 0 n)).Additive
  infer_instance

instance [Preadditive C] (n : ℤ) [(shiftFunctor C (Prod.mk (0 : ℤ) n)).Additive] :
    (shiftFunctor₂ C n).Additive := by
  change (shiftFunctor C (Prod.mk 0 n)).Additive
  infer_instance

instance AdditiveShift₁ [Preadditive C] (n : ℤ) [(shiftFunctor C (Prod.mk n (0 : ℤ))).Additive] :
    (shiftFunctor C n).Additive := by
  change Functor.Additive (shiftFunctor C (n, (0 : ℤ)))
  exact inferInstance

lemma shift₁FunctorZero_eq_shiftFunctorZero :
    shiftFunctorZero C ℤ = shiftFunctorZero C (ℤ × ℤ) := by
  rw [shiftFunctorZero, shiftFunctorZero, Iso.symm_eq_iff]
  apply Iso.ext
  rw [Functor.Monoidal.εIso_hom, Functor.Monoidal.εIso_hom]
  erw [Functor.LaxMonoidal.comp_ε]
  simp; rfl

lemma shift₁FunctorAdd_eq_shiftFunctorAdd (a b : ℤ) :
    shiftFunctorAdd C a b = shiftFunctorAdd C (a, (0 : ℤ)) (b, (0 : ℤ)) := by
  dsimp [shiftFunctorAdd]
  rw [Iso.symm_eq_iff]
  ext1
  dsimp [Functor.Monoidal.μIso_hom]
  erw [Functor.LaxMonoidal.comp_μ]
  simp only [Discrete.addMonoidalFunctor_obj, AddMonoidHom.inl_apply,
    Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, eqToIso_refl, Discrete.functor_map_id, comp_id]
  rfl

instance Shift₂CommShift₁ (n : ℤ) : (shiftFunctor₂ C n).CommShift ℤ where
iso m := (shiftFunctorAdd' C (m, (0 : ℤ)) ((0 : ℤ), n) (m, n) (by simp only [Prod.mk_add_mk,
    add_zero, zero_add])).symm.trans (shiftFunctorAdd' C ((0 : ℤ), n) (m, (0 : ℤ)) (m, n)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]))
zero := by
  simp only
  rw [← shiftFunctorComm_eq]
  ext X
  rw [Functor.CommShift.isoZero_hom_app, shift₁FunctorZero_eq_shiftFunctorZero]
  change _ =  (shiftFunctor C ((0 : ℤ), n)).map ((shiftFunctorZero C (ℤ × ℤ)).hom.app X) ≫
    (shiftFunctorZero C (ℤ × ℤ)).inv.app ((shiftFunctor C ((0 : ℤ), n)).obj X)
  rw [shiftFunctorZero_inv_app_shift]
  slice_rhs 1 2 => rw [← Functor.map_comp]
  simp only [Functor.id_obj, Iso.hom_inv_id_app, Functor.map_id, id_comp]
  rw [← Iso.symm_hom, shiftFunctorComm_symm]
  rfl
add := by sorry
-- compiles on 2025-04-07
/-  intro a b
  dsimp
  ext A
  simp only [Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.CommShift.isoAdd_hom_app, Functor.map_comp, assoc]
  rw [shift₁FunctorAdd_eq_shiftFunctorAdd]
  have eq1 := shiftFunctorAdd'_assoc_inv_app ((a,0) : ℤ × ℤ) (b,0) (0,n) (a+b,0) (b,n) (a+b,n)
    sorry sorry sorry A
  rw [← cancel_epi ((shiftFunctor C (0, n)).map
    ((shiftFunctorAdd' C (a, 0) (b, 0) (a + b, 0) sorry).hom.app A))] at eq1
  conv_lhs at eq1 => slice 1 2; rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rw [id_comp] at eq1
  have eq2 := shiftFunctorAdd'_assoc_hom_app ((0,n) : ℤ × ℤ) (a,0) (b,0) (a,n) (a+b,0) (a+b,n)
    sorry sorry sorry A
  rw [← cancel_mono ((shiftFunctorAdd' C (a, 0) (b, 0) (a + b, 0) sorry).inv.app
    ((shiftFunctor C (0, n)).obj A))] at eq2
  conv_rhs at eq2 => slice 2 3; rw [Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, assoc, comp_id] at eq2
  rw [eq1, ← eq2]
  simp only [Functor.comp_obj, assoc]
  congr 2
  · dsimp [shiftFunctor₂, FilteredShift]; sorry
  · have eq : (shiftFunctorAdd' C (a, 0) (b, n) (a + b, n) sorry).inv.app A ≫
        (shiftFunctorAdd' C (a, n) (b, 0) (a + b, n) sorry).hom.app A =
        (shiftFunctorAdd' C (0, n) (b, 0) (b, n) sorry).hom.app ((shiftFunctor C a).obj A) ≫
        (shiftFunctor C b).map ((shiftFunctorAdd' C (a, 0) (0, n) (a, n) sorry).inv.app A) := by
      have := shiftFunctorAdd'_assoc_inv_app ((a,0) : ℤ × ℤ) (0,n) (b,0) (a,n) (b,n) (a+b,n)
        sorry sorry sorry A
      rw [← cancel_mono ((shiftFunctorAdd' C (a, n) (b, 0) (a + b, n) sorry).hom.app A)] at this
      rw [assoc, Iso.inv_hom_id_app] at this
      simp only [Functor.comp_obj, comp_id, assoc] at this
      erw [this]
      slice_rhs 1 2 => erw [Iso.hom_inv_id_app]
      simp only [Functor.comp_obj, id_comp]
    conv_lhs => rw[ ← assoc, ← assoc, eq]
    simp only [Functor.comp_obj, assoc, NatIso.cancel_natIso_hom_left]
    sorry -/

end

set_option quotPrecheck false in
/-- shifting an object `X` by `(0, n)` is obtained by the notation `X⟪n⟫` -/
notation -- Any better notational suggestions?
X "⟪" n "⟫" => (@shiftFunctor C _ _ _ Shift₂ n).obj X

set_option quotPrecheck false in
/-- shifting a morphism `f` by `(0, n)` is obtained by the notation `f⟪n⟫'` -/
notation f "⟪" n "⟫'" => (@shiftFunctor C _ _ _ Shift₂ n).map f

namespace Triangulated

variable (C)
variable [HasShift C (ℤ × ℤ)] [Preadditive C] [HasZeroObject C]

/-- Definition of a filtered pretriangulated category.
-/
class FilteredTriangulated [∀ p : ℤ × ℤ, Functor.Additive (shiftFunctor C p)]
  [hC : Pretriangulated C]
where
  /-- the second shift acts by triangulated functors -/
  shift₂_triangle : ∀ (n : ℤ), (@shiftFunctor C _ _ _ Shift₂ n).IsTriangulated
  /-- morphism into the object with shifted filtration -/
  α : 𝟭 C ⟶ @shiftFunctor C _ _ _ Shift₂ 1
  /-- objets with filtration concentrated in degree `≤ n` -/
  LE : ℤ → Triangulated.Subcategory C
  /-- objets with filtration concentrated in degree `≥ n` -/
  GE : ℤ → Triangulated.Subcategory C
  LE_closedUnderIsomorphisms : ∀ (n : ℤ), ClosedUnderIsomorphisms (LE n).P := by infer_instance
  GE_closedUnderIsomorphisms : ∀ (n : ℤ), ClosedUnderIsomorphisms (GE n).P := by infer_instance
  LE_zero_le : (LE 0).P ≤ (LE 1).P
  GE_one_le : (GE 1).P ≤ (GE 0).P
  LE_shift : ∀ (n a n' : ℤ), a + n = n' → ∀ (X : C), (LE n).P X → (LE n').P (X⟪a⟫)
  GE_shift : ∀ (n a n' : ℤ), a + n = n' → ∀ (X : C), (GE n).P X → (GE n').P (X⟪a⟫)
  zero' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (GE 1).P X → (LE 0).P Y → f = 0
  adj_left : ∀ ⦃X Y : C⦄, (GE 1).P X → (LE 0).P Y → Function.Bijective
    (fun (f : Y⟪1⟫ ⟶ X) ↦ (α.app Y ≫ f : Y ⟶ X))
  adj_right : ∀ ⦃X Y : C⦄, (GE 1).P X → (LE 0).P Y → Function.Bijective
    (fun (f : Y ⟶ X) ↦ (f ≫ α.app X : Y ⟶ (X⟪1⟫)))
  LE_exhaustive : ∀ (X : C), ∃ (n : ℤ), (LE n).P X
  GE_exhaustive : ∀ (X : C), ∃ (n : ℤ), (GE n).P X
  α_s : ∀ (X : C), (α.app X)⟪1⟫' = α.app (X⟪1⟫)
  exists_triangle_one_zero : ∀ (X : C), ∃ (A : C) (B : C) (_ : (GE 1).P A) (_ : (LE 0).P B)
    (f : A ⟶ X) (g : X ⟶ B) (h : B ⟶ A⟦1⟧),
    Triangle.mk f g h ∈ distinguishedTriangles

namespace FilteredTriangulated

attribute [instance] LE_closedUnderIsomorphisms GE_closedUnderIsomorphisms

variable {C}

variable [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C]

lemma α_vs_second_shift_aux1 (n : ℕ) : ∀ (X : C),
    (@shiftFunctor C _ _ _ Shift₂ n).map (α.app X) = α.app ((@shiftFunctor C _ _ _ Shift₂ n).obj X)
    ≫ (@shiftFunctorComm C _ _ _ Shift₂ n 1).hom.app X := by
  induction' n with n hn
  · intro X
    simp only [Int.Nat.cast_ofNat_Int, Functor.id_obj, Functor.comp_obj]
    have : (@shiftFunctorComm C _ _ _ Shift₂ 0 1).hom.app X =
        ((@shiftFunctorZero C _ _ _ Shift₂).hom.app X)⟪1⟫' ≫
        (@shiftFunctorZero C _ _ _ Shift₂).inv.app (X⟪1⟫) := by
      simp only [Functor.comp_obj, Functor.id_obj]
      rw [← cancel_mono ((@shiftFunctorComm C _ _ _ Shift₂ 0 1).inv.app X), ← shiftFunctorComm_symm]
      simp only [Functor.comp_obj, Iso.symm_hom, Iso.symm_inv, Iso.inv_hom_id_app, assoc]
      rw [@shiftFunctorComm_zero_hom_app C _ _ _ Shift₂]
      simp only [Functor.id_obj, Iso.inv_hom_id_app_assoc]
      rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    rw [this]
    have := hP.α.naturality ((@shiftFunctorZero C _ _ _ Shift₂).hom.app X)
    simp only [Functor.id_obj, Functor.id_map] at this
    rw [← assoc, ← this]
    simp only [Functor.id_obj, assoc]
    rw [← cancel_mono ((@shiftFunctorZero C ℤ _ _ Shift₂).hom.app (X⟪1⟫))]
    simp only [Functor.id_obj, NatTrans.naturality, Functor.id_map, assoc, Iso.inv_hom_id_app,
      comp_id]
  · intro X
    have heq : (@shiftFunctorComm C _ _ _ Shift₂ ↑(n + 1) 1).hom.app X =
        ((@shiftFunctorAdd' C _ _ _ Shift₂ n 1 ↑(n + 1) rfl).hom.app X)⟪1⟫'
        ≫ ((@shiftFunctorComm C _ _ _ Shift₂ n 1).hom.app X)⟪1⟫'
        ≫ (@shiftFunctorAdd' C _ _ _ Shift₂ n 1 ↑(n + 1) rfl).inv.app (X⟪1⟫):= by
      simp only [Functor.comp_obj]
      rw [@shiftFunctorComm_eq C ℤ _ _ Shift₂ n 1 ↑(n + 1) rfl]
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_obj, Functor.map_comp,
        assoc]
      rw [← assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id, id_comp]
      rw [← cancel_epi ((@shiftFunctorComm C _ _ _ Shift₂ ↑(n + 1) 1).inv.app X)]
      conv_rhs => rw [← shiftFunctorComm_symm, Iso.symm_inv]
      conv_lhs => rw [Iso.inv_hom_id_app]
      rw [← assoc, @shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd'_hom_app C _ _ _ Shift₂
        1 1 n ↑(n + 1) (by simp only [add_comm, Nat.cast_add, Nat.cast_one])]
      simp only [Functor.comp_obj, shiftFunctorComm_eq_refl, Iso.refl_hom, NatTrans.id_app,
        Functor.map_id, id_comp, assoc]
      rw [@shiftFunctorComm_eq C _ _ _ Shift₂ 1 n ↑(n + 1) (by simp only [add_comm,
        Nat.cast_add, Nat.cast_one])]
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_obj, assoc,
        Iso.hom_inv_id_app, comp_id]
    rw [heq]
    have := (@shiftFunctorAdd' C _ _ _ Shift₂ n 1 (n + 1) rfl).hom.naturality (α.app X)
    rw [← cancel_mono ((@shiftFunctorAdd' C _ _ _ Shift₂ n 1 ↑(n + 1) rfl).hom.app (X⟪1⟫))]
    rw [assoc, assoc, assoc, Iso.inv_hom_id_app]; erw [comp_id, this]
    simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map]
    rw [hn X]
    simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp]
    rw [← assoc, ← assoc]
    congr 1
    rw [hP.α_s (X⟪n⟫)]
    exact hP.α.naturality ((@shiftFunctorAdd' C _ _ _ Shift₂ n 1 ↑(n + 1) rfl).hom.app X)

lemma α_vs_second_shift_aux2 (n : ℕ) : ∀ (X : C),
    (@shiftFunctor C _ _ _ Shift₂ (-n)).map (α.app X) =
    α.app ((@shiftFunctor C _ _ _ Shift₂ (-n)).obj X)
    ≫ (@shiftFunctorComm C _ _ _ Shift₂ (-n) 1).hom.app X := by
  induction' n with n hn
  · exact α_vs_second_shift_aux1 0
  · intro X
    apply Functor.Faithful.map_injective (F := @shiftFunctor C _ _ _ Shift₂ 1)
    simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp]
    rw [← cancel_epi ((@shiftFunctorAdd' C _ _ _ Shift₂ (-(n + 1)) 1 (-n) (by linarith)).hom.app X)]
    erw [← (@shiftFunctorAdd' C _ _ _ Shift₂ (-(n + 1)) 1 (-n)
      (by linarith)).hom.naturality (α.app X)]
    have heq : ((@shiftFunctorComm C _ _ _ Shift₂ (-(n + 1)) 1).hom.app X)⟪1⟫' =
        ((@shiftFunctorAdd' C _ _ _ Shift₂ (-(n + 1)) 1 (-n) (by linarith)).inv.app X)⟪1⟫' ≫
        (@shiftFunctorComm C _ _ _ Shift₂ (-n) 1).hom.app X ≫
        (@shiftFunctorAdd' C _ _ _ Shift₂ (-(n + 1)) 1 (-n) (by linarith)).hom.app (X⟪1⟫) := by
      simp only [Functor.comp_obj]
      rw [@shiftFunctorComm_eq C ℤ _ _ Shift₂ (-(n + 1)) 1 (-n) (by linarith)]
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_obj, Functor.map_comp]
      congr 1
      rw [@shiftFunctorComm_eq C ℤ _ _ Shift₂ (-n) 1 (-n + 1) (by linarith)]
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_obj, assoc]
      rw [← @shiftFunctorAdd'_assoc_hom_app C _ _ _ Shift₂ 1 (-(n + 1)) 1 (-n) (-n) (-n + 1)
        (by linarith) (by linarith) (by linarith)]
      simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc]
    erw [heq]
    rw [← assoc, ← assoc, ← assoc]
    congr 1
    erw [hP.α_s (X⟪-(n + 1)⟫)]
    have := hP.α.naturality ((@shiftFunctorAdd' C _ _ _ Shift₂ (-(n + 1)) 1 (-n)
      (by linarith)).hom.app X)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map] at this
    rw [this]
    slice_rhs 2 3 => rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    simp only [Functor.id_obj, Functor.comp_obj, id_comp]
    rw [hn X]

lemma α_vs_second_shift (n : ℤ) (X : C) :
    (@shiftFunctor C _ _ _ Shift₂ n).map (α.app X) = α.app ((@shiftFunctor C _ _ _ Shift₂ n).obj X)
    ≫ (@shiftFunctorComm C _ _ _ Shift₂ n 1).hom.app X := by
  by_cases h : 0 ≤ n
  · rw [Int.eq_natAbs_of_zero_le h]
    exact α_vs_second_shift_aux1 _ X
  · have h' : n = - ↑n.natAbs := by
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt (lt_of_not_le h)), neg_neg]
    rw [h']
    exact α_vs_second_shift_aux2 _ X

lemma exists_triangle (A : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∃ (X Y : C) (_ : (GE n₁).P X) (_ : (LE n₀).P Y) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := exists_triangle_one_zero (A⟪-n₀⟫)
  let T := (@Functor.mapTriangle _ _ _ _ _ _ (@shiftFunctor C _ _ _ Shift₂ n₀)
    (Shift₂CommShift₁ n₀)).obj (Triangle.mk f g h)
  let e := (@shiftEquiv' C _ _ _ Shift₂ (-n₀) n₀ (by rw [neg_add_cancel])).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
    refine isomorphic_distinguished _ (@Functor.IsTriangulated.map_distinguished _ _ _ _ _ _
      (@shiftFunctor C _ _ _ Shift₂ n₀) (Shift₂CommShift₁ n₀) _ _ _ _ _ _ _ _
      (shift₂_triangle n₀) _ mem) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    all_goals dsimp; simp [T]
  exact ⟨_, _, GE_shift _ _ _ (by omega) _ hX, LE_shift _ _ _ (by omega) _ hY, _, _, _, hT'⟩

/- Are the following two lemmas even useful?-/
lemma predicateShift_LE (n n' a : ℤ) (hn' : n = n') :
    (PredicateShift (LE n).P a) = (hP.LE n').P := by
  ext X; sorry
--  simp only [PredicateShift, Triangulated.Subcategory.shift_iff, hn']
-- might need to add lemmas from jriou_lozalization

lemma predicateShift_GE (a n n' : ℤ) (hn' : n = n') :
    (PredicateShift (GE n).P a) = (hP.GE n').P := by
  ext X; sorry
--  simp only [PredicateShift, hn', Triangulated.Subcategory.shift_iff]
-- might need to add lemmas from jriou_lozalization

lemma LE_monotone : Monotone (fun n ↦ (hP.LE n).P) := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), (LE n).P ≤ (hP.LE (n + a)).P
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX =>
    (LE_closedUnderIsomorphisms (n + 1)).of_iso ((@shiftEquiv' C _ _ _ Shift₂
    (-n) n (by rw [neg_add_cancel])).unitIso.symm.app X) (LE_shift 1 n (n + 1) rfl _
    (LE_zero_le _ (LE_shift n (-n) 0 (by rw [neg_add_cancel]) X hX)))
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (ha n).trans (hb (n+a))
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

lemma GE_antitone : Antitone (fun n ↦ (hP.GE n).P) := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), (GE (n + a)).P ≤ (hP.GE n).P
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX =>
    (GE_closedUnderIsomorphisms n).of_iso ((@shiftEquiv' C _ _ _ Shift₂
    (-n) n (by rw [neg_add_cancel])).unitIso.symm.app X) (GE_shift 0 n n (by rw [add_zero]) _
    (GE_one_le _ (GE_shift (n + 1) (-n) 1 (by rw [neg_add_cancel_left]) X hX)))
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc ]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

/-- Given a filtration `F` on a pretriangulated category `C`, the property `IsLE X n`
holds if `X : C` is `≤ n` for the filtration. -/
class IsLE (X : C) (n : ℤ) : Prop where
  le : (hP.LE n).P X

/-- Given a filtration `F` on a pretriangulated category `C`, the property `IsGE X n`
holds if `X : C` is `≥ n` for the filtration. -/
class IsGE (X : C) (n : ℤ) : Prop where
  ge : (hP.GE n).P X

lemma mem_of_isLE (X : C) (n : ℤ) [IsLE X n] : (LE n).P X := IsLE.le
lemma mem_of_isGE (X : C) (n : ℤ) [IsGE X n] : (GE n).P X := IsGE.ge

-- Should the following be instances or lemmas? Let's make them instances and see what happens.
instance zero_isLE (n : ℤ) : IsLE (0 : C) n := {le := (LE n).zero}
instance zero_isGE (n : ℤ) : IsGE (0 : C) n := {ge := (GE n).zero}
instance shift_isLE_of_isLE (X : C) (n a : ℤ) [IsLE X n] : IsLE (X⟦a⟧) n :=
  {le := (LE n).shift X a (mem_of_isLE X n)}
instance shift_isGE_of_isGE (X : C) (n a : ℤ) [IsGE X n] : IsGE (X⟦a⟧) n :=
  {ge := (GE n).shift X a (mem_of_isGE X n)}

instance LE_ext₁ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsLE T.obj₂ n]
    [IsLE T.obj₃ n] : IsLE T.obj₁ n :=
  {le := (LE n).ext₁ T hT (mem_of_isLE T.obj₂ n) (mem_of_isLE T.obj₃ n)}

instance LE_ext₂ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsLE T.obj₁ n]
    [IsLE T.obj₃ n] : IsLE T.obj₂ n :=
  {le := (LE n).ext₂ T hT (mem_of_isLE T.obj₁ n) (mem_of_isLE T.obj₃ n)}

instance LE_ext₃ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsLE T.obj₁ n]
    [IsLE T.obj₂ n] : IsLE T.obj₃ n :=
  {le := (LE n).ext₃ T hT (mem_of_isLE T.obj₁ n) (mem_of_isLE T.obj₂ n)}

instance GE_ext₁ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsGE T.obj₂ n]
    [IsGE T.obj₃ n] : IsGE T.obj₁ n :=
  {ge := (GE n).ext₁ T hT (mem_of_isGE T.obj₂ n) (mem_of_isGE T.obj₃ n)}

instance GE_ext₂ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsGE T.obj₁ n]
    [IsGE T.obj₃ n] : IsGE T.obj₂ n :=
  {ge := (GE n).ext₂ T hT (mem_of_isGE T.obj₁ n) (mem_of_isGE T.obj₃ n)}

instance GE_ext₃ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsGE T.obj₁ n]
    [IsGE T.obj₂ n] : IsGE T.obj₃ n :=
  {ge := (GE n).ext₃ T hT (mem_of_isGE T.obj₁ n) (mem_of_isGE T.obj₂ n)}

lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [IsLE X n] : IsLE Y n where
  le := mem_of_iso (LE n).P e (mem_of_isLE X n)

lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [IsGE X n] : IsGE Y n where
  ge := mem_of_iso (GE n).P e (mem_of_isGE X n)

lemma isLE_of_LE (X : C) (p q : ℤ) (hpq : p ≤ q) [IsLE X p] : IsLE X q where
  le := LE_monotone hpq _ (mem_of_isLE X p)

lemma isGE_of_GE (X : C) (p q : ℤ) (hpq : p ≤ q) [IsGE X q] : IsGE X p where
  ge := GE_antitone hpq _ (mem_of_isGE X q)

lemma isLE_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [IsLE X n] :
    IsLE (X⟪a⟫) n' :=
  ⟨LE_shift n a n' hn' X (mem_of_isLE X n)⟩

lemma isGE_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [IsGE X n] :
    IsGE (X⟪a⟫) n' :=
  ⟨GE_shift n a n' hn' X (mem_of_isGE X n)⟩

lemma isLE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [IsLE (X⟪a⟫) n'] :
    IsLE X n := by
  have h := isLE_shift (X⟪a⟫) n' (-a) n (by linarith)
  exact isLE_of_iso (show ((X⟪a⟫)⟪-a⟫) ≅ X from
  (@shiftEquiv C _ _ _ Shift₂ a).unitIso.symm.app X) n

lemma isGE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [IsGE (X⟪a⟫) n'] :
    IsGE X n := by
  have h := isGE_shift (X⟪a⟫) n' (-a) n (by linarith)
  exact isGE_of_iso (show ((X⟪a⟫)⟪-a⟫) ≅ X from
  (@shiftEquiv C _ _ _ Shift₂ a).unitIso.symm.app X) n

lemma isLE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n = n') :
    IsLE (X⟪a⟫) n' ↔ IsLE X n := by
  constructor
  · intro
    exact isLE_of_shift X n a n' hn'
  · intro
    exact isLE_shift X n a n' hn'

lemma isGE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n = n') :
    IsGE (X⟪a⟫) n' ↔ IsGE X n := by
  constructor
  · intro
    exact isGE_of_shift X n a n' hn'
  · intro
    exact isGE_shift X n a n' hn'

lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [IsGE X n₁] [IsLE Y n₀] : f = 0 := by
  have := isLE_shift Y n₀ (-n₀) 0 (by simp only [neg_add_cancel])
  have := isGE_shift X n₁ (-n₀) (n₁-n₀) (by linarith)
  have := isGE_of_GE (X⟪-n₀⟫) 1 (n₁-n₀) (by linarith)
  apply (@shiftFunctor C _ _ _ Shift₂ (-n₀)).map_injective
  simp only [Functor.map_zero]
  apply zero'
  · apply mem_of_isGE
  · apply mem_of_isLE

lemma zero_of_isGE_of_isLE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    (_ : IsGE X n₁) (_ : IsLE Y n₀) : f = 0 :=
  zero f n₀ n₁ h

lemma isZero (X : C) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [IsGE X n₁] [IsLE X n₀] : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact zero _ n₀ n₁ h

lemma isLE₁ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : hP.IsLE T.obj₂ n)
    (h₃ : hP.IsLE T.obj₃ n) : hP.IsLE T.obj₁ n where
  le := (hP.LE n).ext₁ T hT h₁.le h₃.le

lemma isLE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : hP.IsLE T.obj₁ n)
    (h₃ : hP.IsLE T.obj₃ n) : hP.IsLE T.obj₂ n where
  le := (hP.LE n).ext₂ T hT h₁.le h₃.le

lemma isLE₃ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : hP.IsLE T.obj₁ n)
    (h₃ : hP.IsLE T.obj₂ n) : hP.IsLE T.obj₃ n where
  le := (hP.LE n).ext₃ T hT h₁.le h₃.le

lemma isGE₁ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : hP.IsGE T.obj₂ n)
    (h₃ : hP.IsGE T.obj₃ n) : hP.IsGE T.obj₁ n where
  ge := (hP.GE n).ext₁ T hT h₁.ge h₃.ge

lemma isGE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : hP.IsGE T.obj₁ n)
    (h₃ : hP.IsGE T.obj₃ n) : hP.IsGE T.obj₂ n where
  ge := (hP.GE n).ext₂ T hT h₁.ge h₃.ge

lemma isGE₃ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : hP.IsGE T.obj₁ n)
    (h₃ : hP.IsGE T.obj₂ n) : hP.IsGE T.obj₃ n where
  ge := (hP.GE n).ext₃ T hT h₁.ge h₃.ge

def core (X : C) : Prop := (LE 0).P X ∧ (GE 0).P X

lemma mem_core_iff (X : C) :
    core X ↔ IsLE X 0 ∧ IsGE X 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨mem_of_isLE _ _, mem_of_isGE _ _⟩

def tCore : Triangulated.Subcategory C where
  P := core
  zero' := by
    existsi 0, isZero_zero C
    rw [mem_core_iff]
    exact ⟨inferInstance, inferInstance⟩
  shift X n hX := by
    rw [mem_core_iff] at hX ⊢
    have := hX.1; have := hX.2
    exact ⟨inferInstance, inferInstance⟩
  ext₂' T dT hT₁ hT₃ := by
    apply le_isoClosure
    rw [mem_core_iff] at hT₁ hT₃ ⊢
    constructor
    · have := hT₁.1; have := hT₃.1
      exact LE_ext₂ T dT 0
    · have := hT₁.2; have := hT₃.2
      exact GE_ext₂  T dT 0

lemma mem_tCore_iff (X : C) :
    tCore.P X ↔ IsLE X 0 ∧ IsGE X 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨mem_of_isLE _ _, mem_of_isGE _ _⟩

instance : ClosedUnderIsomorphisms (tCore (C := C)).P where
  of_iso {X Y} e hX := by
    rw [mem_tCore_iff] at hX ⊢
    have := hX.1
    have := hX.2
    constructor
    · exact isLE_of_iso e 0
    · exact isGE_of_iso e 0

/-- Doc string, why the "'"?-/
abbrev Core' := (tCore (C := C)).category

/-- Doc string, why the "'"?-/
abbrev ιCore' : Core' (C := C) ⥤ C := fullSubcategoryInclusion _

instance : Functor.Additive (ιCore' (C := C)) := sorry

instance : Functor.Full (ιCore' (C := C)) := sorry

instance : Functor.Faithful (ιCore' (C := C)) := sorry


instance (X : Core') : IsLE (C := C) (ιCore'.obj X) 0 := ⟨X.2.1⟩
instance (X : Core') : IsGE (C := C) (ιCore'.obj X) 0 := ⟨X.2.2⟩
instance (X : Core') : IsLE X.1 0 (C := C) := ⟨X.2.1⟩
instance (X : Core') : IsGE X.1 0 (C := C) := ⟨X.2.2⟩

lemma ιCore_obj_mem_core (X : Core') : core (C := C) (ιCore'.obj X) := X.2

/-
def ιHeartDegree (n : ℤ) : t.Heart' ⥤ C :=
  t.ιHeart' ⋙ shiftFunctor C (-n)

noncomputable def ιHeartDegreeCompShiftIso (n : ℤ) : t.ιHeartDegree n ⋙ shiftFunctor C n ≅
    t.ιHeart' :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)) ≪≫
    Functor.rightUnitor _
-/

variable (C)

class HasCore where
  H : Type*
  [cat : Category H]
  [preadditive : Preadditive H]
  ι : H ⥤ C
  additive_ι : ι.Additive := by infer_instance
  fullι : ι.Full := by infer_instance
  faithful_ι : ι.Faithful := by infer_instance
  hι : ι.essImage = setOf tCore.P := by simp

variable {C}

def hasCoreFullSubcategory : HasCore C where
  H := Core'
  ι := ιCore'
  hι := by
    ext X
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      refine ClosedUnderIsomorphisms.of_iso (Functor.essImage.getIso h ) ?_
      exact (Functor.essImage.witness h).2
    · intro h
      change (fullSubcategoryInclusion core).obj ⟨X, h⟩ ∈ _
      exact Functor.obj_mem_essImage _ _

variable [ht : HasCore C]

def Core := ht.H

instance : Category (Core (C := C)) := ht.cat

def ιCore : Core (C := C) ⥤ C := ht.ι

instance : Preadditive (Core (C := C)) := ht.preadditive
instance : (ιCore (C := C)).Full := ht.fullι
instance : (ιCore (C := C)).Faithful := ht.faithful_ι
instance : (ιCore (C := C)).Additive := ht.additive_ι

-- Add instances saying that the core is triangulated and the inclusion is a triangulated functor.

lemma ιCore_obj_mem (X : Core (C := C)) : tCore.P (ιCore.obj X) := by
  change (ιCore.obj X) ∈ setOf tCore.P
  rw [← ht.hι]
  exact ιCore.obj_mem_essImage X

instance (X : Core) : IsLE (C := C) (ιCore.obj X) 0 :=
  ⟨(ιCore_obj_mem X).1⟩

instance (X : Core) : IsGE (C := C) (ιCore.obj X) 0 :=
  ⟨(ιCore_obj_mem X).2⟩

lemma mem_essImage_ιCore_iff (X : C) :
    X ∈ ιCore.essImage ↔ tCore.P X := by
  dsimp [ιCore]
  rw [ht.hι, Set.mem_setOf_eq]

noncomputable def coreMk (X : C) (hX : tCore.P X) : Core (C := C) :=
  Functor.essImage.witness ((mem_essImage_ιCore_iff X).2 hX)

noncomputable def ιCoreObjCoreMkIso (X : C) (hX : tCore.P X) :
    ιCore.obj (coreMk X hX) ≅ X :=
  Functor.essImage.getIso ((mem_essImage_ιCore_iff X).2 hX)

@[simps obj]
noncomputable def liftCore {D : Type*} [Category D]
    (G : D ⥤ C) (hF : ∀ (X : D), tCore.P (G.obj X)) :
    D ⥤ Core (C := C) where
  obj X := coreMk (G.obj X) (hF X)
  map {X Y} f := ιCore.preimage ((ιCoreObjCoreMkIso _ (hF X)).hom ≫ G.map f ≫
      (ιCoreObjCoreMkIso _ (hF Y)).inv)
  map_id X := ιCore.map_injective (by simp)
  map_comp f g := ιCore.map_injective (by simp)

@[simp, reassoc]
lemma ιCore_map_liftCore_map {D : Type*} [Category D]
    (G : D ⥤ C) (hF : ∀ (X : D), tCore.P (G.obj X)) {X Y : D} (f : X ⟶ Y) :
    ιCore.map ((liftCore G hF).map f) =
      (ιCoreObjCoreMkIso _ (hF X)).hom ≫ G.map f ≫
        (ιCoreObjCoreMkIso _ (hF Y)).inv := by
  simp [liftCore]

noncomputable def liftCoreιCore {D : Type*} [Category D]
    (G : D ⥤ C) (hF : ∀ (X : D), tCore.P (G.obj X)) :
    liftCore G hF ⋙ ιCore ≅ G :=
  NatIso.ofComponents (fun X => ιCoreObjCoreMkIso _ (hF X)) (by aesop_cat)

end FilteredTriangulated

end Triangulated

#exit

namespace Subcategory

variable {C}
variable (S : Subcategory C) (t : TStructure C)

class HasInducedTStructure : Prop :=
  exists_triangle_zero_one (A : C) (hA : S.P A) :
    ∃ (X Y : C) (_ : t.LE 0 X) (_ : t.GE 1 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧) (_ : Triangle.mk f g h ∈ distTriang C),
    X ∈ S.ι.essImage ∧ Y ∈ S.ι.essImage

variable [h : S.HasInducedTStructure t]

def tStructure : TStructure S.category where
  LE n X := t.LE n (S.ι.obj X)
  GE n X := t.GE n (S.ι.obj X)
  LE_closedUnderIsomorphisms n := ⟨fun {X Y} e hX => mem_of_iso (t.LE n) (S.ι.mapIso e) hX⟩
  GE_closedUnderIsomorphisms n := ⟨fun {X Y} e hX => mem_of_iso (t.GE n) (S.ι.mapIso e) hX⟩
  LE_shift n a n' h X hX := mem_of_iso (t.LE n') ((S.ι.commShiftIso a).symm.app X)
    (t.LE_shift n a n' h (S.ι.obj X) hX)
  GE_shift n a n' h X hX := mem_of_iso (t.GE n') ((S.ι.commShiftIso a).symm.app X)
    (t.GE_shift n a n' h (S.ι.obj X) hX)
  zero' {X Y} f hX hY := S.ι.map_injective (by
    rw [Functor.map_zero]
    exact t.zero' (S.ι.map f) hX hY)
  LE_zero_le X hX := t.LE_zero_le _ hX
  GE_one_le X hX := t.GE_one_le _ hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT, ⟨X', ⟨e⟩⟩, ⟨Y', ⟨e'⟩⟩⟩ :=
      h.exists_triangle_zero_one A.1 A.2
    refine' ⟨X', Y', mem_of_iso (t.LE 0) e.symm hX, mem_of_iso (t.GE 1) e'.symm hY,
      S.ι.preimage (e.hom ≫ f), S.ι.preimage (g ≫ e'.inv),
      S.ι.preimage (e'.hom ≫ h ≫ e.inv⟦(1 : ℤ)⟧' ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app X'),
      isomorphic_distinguished _ hT _ _⟩
    refine' Triangle.isoMk _ _ e (Iso.refl _) e' _ _ _
    · dsimp
      simp
    · dsimp
      simp
    · dsimp
      simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
        Category.comp_id, Iso.cancel_iso_hom_left, ← Functor.map_comp, Iso.inv_hom_id,
        Functor.map_id]

@[simp]
lemma mem_tStructure_heart_iff (X : S.category) :
    (S.tStructure t).heart X ↔ t.heart X.1 := by
  rfl

lemma tStructure_isLE_iff (X : S.category) (n : ℤ) :
    (S.tStructure t).IsLE X n ↔ t.IsLE (S.ι.obj X) n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

lemma tStructure_isGE_iff (X : S.category) (n : ℤ) :
    (S.tStructure t).IsGE X n ↔ t.IsGE (S.ι.obj X) n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

end Subcategory

end Triangulated

end CategoryTheory


end FilteredTriangulated
