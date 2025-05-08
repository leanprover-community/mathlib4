/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw, Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.Lemmas
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.Tactic.Linarith

/-!
# Filtered Triangulated Categories

-/

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
zero := sorry
add := sorry

end

set_option quotPrecheck false in
/-- shifting an object `X` by `(0, n)` is obtained by the notation `X⟪n⟫` -/
notation -- Any better notational suggestions?
X "⟪" n "⟫" => (shiftFunctor₂ C n).obj X

set_option quotPrecheck false in
/-- shifting a morphism `f` by `(0, n)` is obtained by the notation `f⟪n⟫'` -/
notation f "⟪" n "⟫'" => (shiftFunctor₂ C n).map f

open ObjectProperty

variable (C)
variable [HasShift C (ℤ × ℤ)] [Preadditive C] [HasZeroObject C]

/-- Definition A.1.1(1):
Definition of a filtered pretriangulated category.
-/
class FilteredTriangulated [∀ p : ℤ × ℤ, Functor.Additive (shiftFunctor C p)]
  [hC : Pretriangulated C]
where
  /-- the second shift acts by triangulated functors -/
  shift₂_triangle : ∀ (n : ℤ), (shiftFunctor₂ C n).IsTriangulated
  /-- morphism into the object with shifted filtration -/
  α : 𝟭 C ⟶ shiftFunctor₂ C 1
  /-- objets with filtration concentrated in degree `≤ n` -/
  LE : ℤ → Triangulated.Subcategory C
  /-- objets with filtration concentrated in degree `≥ n` -/
  GE : ℤ → Triangulated.Subcategory C
  LE_closedUnderIsomorphisms : ∀ (n : ℤ), IsClosedUnderIsomorphisms (LE n).P :=
    by infer_instance
  GE_closedUnderIsomorphisms : ∀ (n : ℤ), IsClosedUnderIsomorphisms (GE n).P :=
    by infer_instance
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

open ObjectProperty

variable {C}

variable [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C]

instance (n : ℤ) : (shiftFunctor₂ C n).IsTriangulated := hP.shift₂_triangle n

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
    (LE_closedUnderIsomorphisms (n + 1)).of_iso ((shiftEquiv' (FilteredShift C)
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
    (GE_closedUnderIsomorphisms n).of_iso ((shiftEquiv' (FilteredShift C)
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
  le := prop_of_iso (LE n).P e (mem_of_isLE X n)

lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [IsGE X n] : IsGE Y n where
  ge := prop_of_iso (GE n).P e (mem_of_isGE X n)

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
  (shiftEquiv (FilteredShift C) a).unitIso.symm.app X) n

lemma isGE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [IsGE (X⟪a⟫) n'] :
    IsGE X n := by
  have h := isGE_shift (X⟪a⟫) n' (-a) n (by linarith)
  exact isGE_of_iso (show ((X⟪a⟫)⟪-a⟫) ≅ X from
  (shiftEquiv (FilteredShift C) a).unitIso.symm.app X) n

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

end FilteredTriangulated

open FilteredTriangulated

attribute [instance] LE_closedUnderIsomorphisms GE_closedUnderIsomorphisms

variable {C}

variable [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hCP : FilteredTriangulated C]

variable {D : Type u₀} [Category.{v₀} D]
variable [HasShift D (ℤ × ℤ)] [Preadditive D] [HasZeroObject D]
  [∀ p : ℤ × ℤ, Functor.Additive (shiftFunctor D p)]
  [hD : Pretriangulated D] [hDP : FilteredTriangulated D]

variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ] [Preadditive A] [HasZeroObject A]
  [∀ p : ℤ, Functor.Additive (shiftFunctor A p)] [Pretriangulated A]

variable {B : Type u₂} [Category.{v₂} B] [HasShift B ℤ] [Preadditive B] [HasZeroObject B]
  [∀ p : ℤ, Functor.Additive (shiftFunctor B p)] [Pretriangulated B]


namespace Functor

/-- Definition A.1.1(2).
A filtered triangulated functor is a functor `F : C ⥤ D` that commutes with
both shifts (i.e. with the shifts from `ℤ × ℤ`), that sends the objects of `LE 0`
(resp. `GE 0`) to objects of `LE 0` (resp. `GE 0`) and that is compatible with the
morphisms `α`.
-/
class IsFilteredTriangulated (F : C ⥤ D) [F.CommShift (ℤ × ℤ)] where
  preserves_LE : ∀ (X : C), IsLE X 0 → IsLE (F.obj X) 0
  preserves_GE : ∀ (X : C), IsGE X 0 → IsGE (F.obj X) 0
  commutes_α : ∀ (X : C),
    hDP.α.app (F.obj X) ≫ (F.commShiftIso ((0,1) : ℤ × ℤ)).inv.app X = F.map (hCP.α.app X)

end Functor

section Over

variable (C A) in
/--
Definition A.1.1(3), first part:
Filtered triangulated category over a triangulated category.
-/
structure isFilteredTriangulated_over where
  functor : A ⥤ C
  commShift : functor.CommShift ℤ
  triangulated : functor.IsTriangulated
  ff : functor.FullyFaithful
  essImage (X : C) : functor.essImage X ↔ IsLE X 0 ∧ IsGE X 0

lemma isFilteredTriangulated_over_image (L : isFilteredTriangulated_over C A) (X : A) :
    IsLE (L.functor.obj X) 0 ∧ IsGE (L.functor.obj X) 0 := by
  rw [← L.essImage]
  exact Functor.obj_mem_essImage _ _

-- This gives an equivalence of categories from `A` to the full subcategory of
-- objects of `C` that are `LE 0` and `GE 0`.
def isFilteredTriangulated_over_equiv (L : isFilteredTriangulated_over C A) :
    A ⥤ ObjectProperty.FullSubcategory (fun (X : C) ↦ IsLE X 0 ∧ IsGE X 0) :=
  ObjectProperty.lift _ L.functor (isFilteredTriangulated_over_image L)

instance (L : isFilteredTriangulated_over C A) :
    Functor.IsEquivalence (isFilteredTriangulated_over_equiv L) where
      faithful := by
        have := L.ff.faithful
        exact instFaithfulFullSubcategoryLift _ _ (isFilteredTriangulated_over_image L)
      full := by
        have := L.ff.full
        exact instFullFullSubcategoryLift _ _ (isFilteredTriangulated_over_image L)
      essSurj :=
        {mem_essImage X := by
           obtain ⟨Y, h⟩ := (L.essImage X.1).mpr X.2
           exact ⟨Y, Nonempty.intro (InducedCategory.isoMk (Classical.choice h))⟩
        }

def isFilteredTriangulated_over_equiv_inv_comp (L : isFilteredTriangulated_over C A) :
    (isFilteredTriangulated_over_equiv L).inv ⋙ L.functor ≅ ObjectProperty.ι _ :=
  Iso.inverseCompIso (ObjectProperty.liftCompιIso _ _ _).symm
  (G := (isFilteredTriangulated_over_equiv L).asEquivalence)

/--
Definition A.1.1(3), second part:
Lifting of a triangulated functor.
-/
structure Functor.filteredLifting (L₁ : isFilteredTriangulated_over C A)
    (L₂ : isFilteredTriangulated_over D B) (F : A ⥤ B)
    [F.CommShift ℤ] [F.IsTriangulated] where
  functor : C ⥤ D
  commShift : functor.CommShift (ℤ × ℤ)
  triang : functor.IsFilteredTriangulated
  compat : F ⋙ L₂.functor ≅ L₁.functor ⋙ functor
-- I am guessing that the compatibility isomorphism should satisfy some compatibilities,
-- notably with the "commutation with shifts" isomorphisms.

end Over

section Truncation

-- Prop A.1.3 (i)
-- First sentence.

instance LE_reflective (n : ℤ) : Reflective (ObjectProperty.ι
    (FilteredTriangulated.LE (C := C) n).P) := sorry

instance GE_coreflective (n : ℤ) : Coreflective (ObjectProperty.ι
    (FilteredTriangulated.GE (C := C) n).P) := sorry

def truncLE (n : ℤ) : C ⥤ C := reflector (ObjectProperty.ι
    (FilteredTriangulated.LE (C := C) n).P) ⋙ (ObjectProperty.ι
    (FilteredTriangulated.LE (C := C) n).P)
-- The "left adjoint" of the inclusion.

def truncGE (n : ℤ) : C ⥤ C := coreflector (ObjectProperty.ι
    (FilteredTriangulated.GE (C := C) n).P) ⋙ (ObjectProperty.ι
    (FilteredTriangulated.GE (C := C) n).P)
-- The "right adjoint" of the inclusion.

instance (X : C) (n : ℤ) : IsLE ((truncLE n).obj X) n := sorry

instance (X : C) (n : ℤ) : IsGE ((truncGE n).obj X) n := sorry

def essImage_of_LE (X : C) (n : ℤ) [IsLE X n] : (ObjectProperty.ι
    (FilteredTriangulated.LE (C := C) n).P).essImage X := sorry

def essImage_of_GE (X : C) (n : ℤ) [IsGE X n] : (ObjectProperty.ι
    (FilteredTriangulated.GE (C := C) n).P).essImage X := sorry

def truncLEπ (n : ℤ) : 𝟭 _ ⟶ truncLE (C := C) n :=
  (reflectorAdjunction (FilteredTriangulated.LE (C := C) n).P.ι).unit
-- Unit of the adjunction.

instance truncLEπ_iso_of_LE (X : C) (n : ℤ) [IsLE X n] : IsIso ((truncLEπ n).app X) :=
  Functor.essImage.unit_isIso (essImage_of_LE X n)

noncomputable def descTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [IsLE Y n] :
    (truncLE n).obj X ⟶ Y := sorry

@[reassoc (attr := simp)]
lemma π_descTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [IsLE Y n] :
    (truncLEπ n).app X ≫ descTruncLE f n = f := sorry

def truncGEι (n : ℤ) : truncGE (C := C) n ⟶ 𝟭 _ :=
  (coreflectorAdjunction (FilteredTriangulated.GE (C := C) n).P.ι).counit
-- Counit of the adjunction.

instance truncGEι_iso_of_GE (X : C) (n : ℤ) [IsGE X n] : IsIso ((truncGEι n).app X) :=
  Functor.essImage.counit_isIso (essImage_of_GE X n)

def liftTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [IsGE X n] :
    X ⟶ (truncGE n).obj Y := sorry

@[reassoc (attr := simp)]
lemma liftTruncGE_ι {X Y : C} (f : X ⟶ Y) (n : ℤ) [IsGE X n] :
    liftTruncGE f n ≫ (truncGEι n).app Y = f := sorry

-- Second sentence.
-- The truncation functors are triangulated.
instance (n : ℤ) : (truncLE (C := C) n).CommShift ℤ := sorry

instance (n : ℤ) : (truncLE (C := C) n).IsTriangulated := sorry

instance (n : ℤ) : (truncGE (C := C) n).CommShift ℤ := sorry

instance (n : ℤ) : (truncGE (C := C) n).IsTriangulated := sorry

-- The truncation functors preserve the subcategories `hCP.LE m` and `hCP.GE m` for
-- every `m : ℤ`.

instance (n m : ℤ) (X : C) [IsLE X m] : IsLE ((truncLE n).obj X) m := sorry

instance (n m : ℤ) (X : C) [IsGE X m] : IsGE ((truncLE n).obj X) m := sorry

instance (n m : ℤ) (X : C) [IsLE X m] : IsLE ((truncGE n).obj X) m := sorry

instance (n m : ℤ) (X : C) [IsGE X m] : IsGE ((truncGE n).obj X) m := sorry

abbrev truncGE_onLE (n m : ℤ) :
    (FilteredTriangulated.LE (C := C) m).P.FullSubcategory ⥤
    (FilteredTriangulated.LE (C := C) m).P.FullSubcategory := by
  refine ObjectProperty.lift _ ?_ (fun X ↦ ?_)
  · exact ObjectProperty.ι _ ⋙ truncGE n
  · have : IsLE X.1 m := {le := X.2}
    exact (instIsLEObjTruncGE n m X.1).le

/-
def truncGE_onLE_comp (n m :  ℤ) :
    truncGE_onLE (C := C) n m ⋙ (FilteredTriangulated.LE m).P.ι ≅
    (FilteredTriangulated.LE m).P.ι ⋙ truncGE n := Iso.refl _
-/

abbrev truncLE_onGE (n m : ℤ) :
    (FilteredTriangulated.GE (C := C) m).P.FullSubcategory ⥤
    (FilteredTriangulated.GE (C := C) m).P.FullSubcategory := by
  refine ObjectProperty.lift _ ?_ (fun X ↦ ?_)
  · exact ObjectProperty.ι _ ⋙ truncLE n
  · have : IsGE X.1 m := {ge := X.2}
    exact (instIsGEObjTruncLE n m X.1).ge

-- Prop A.1.3 (ii)

abbrev truncLEGE (a b : ℤ) : C ⥤ C := truncGE a ⋙ truncLE b

abbrev truncGELE (a b : ℤ) : C ⥤ C := truncLE b ⋙ truncGE a

def truncLEGEToGELE (a b : ℤ) : truncLEGE (C := C) a b ⟶ truncGELE a b := by
  set u : TwoSquare (FilteredTriangulated.LE (C := C) b).P.ι (truncGE_onLE a b) (truncGE a)
      (FilteredTriangulated.LE b).P.ι := by
    refine {app X := ?_, naturality X Y f := ?_}
    · dsimp; exact 𝟙 _
    · dsimp; simp
  exact (Functor.associator _ _ _).inv ≫ whiskerRight ((mateEquiv (reflectorAdjunction _)
    (reflectorAdjunction _)).symm u) _ ≫ (Functor.associator _ _ _).hom ≫
    whiskerLeft (reflector (FilteredTriangulated.LE b).P.ι) (𝟙 _)  ≫
    (Functor.associator _ _ _).inv

instance truncLEGEIsoGELE (a b : ℤ) : IsIso (truncLEGEToGELE a b (C := C)) := sorry

lemma truncLEGEToGELE_comm (a b : ℤ) :
    truncGEι (C := C) b ≫ truncLEπ a =
    whiskerLeft (truncGE b) (truncLEπ a) ≫ truncLEGEToGELE b a ≫
    whiskerLeft (truncLE a) (truncGEι b) := by
  ext X
  dsimp [truncLEGEToGELE, truncGEι, truncLEπ]
  simp only [Functor.map_id, id_comp, comp_id, assoc]
  erw [id_comp]
  have := (reflectorAdjunction (FilteredTriangulated.LE (C := C) a).P.ι).unit.naturality
  have := (reflectorAdjunction (FilteredTriangulated.LE (C := C) a).P.ι).counit.naturality
  sorry

lemma truncLEGEToGELE_uniq {a b : ℤ} {X : C}
    {f : (truncLEGE b a).obj X ⟶ (truncGELE b a).obj X}
    (comm : (truncGEι b).app X ≫ (truncLEπ a).app X =
    (truncLEπ a).app ((truncGE b).obj X) ≫ f ≫ (truncGEι b).app ((truncLE a).obj X)) :
    f = (truncLEGEToGELE b a).app X := sorry

-- Prop A.1.3 (iii) but with general indices

-- Existence. Version with and without the `n + 1`.
-- This is cheating in a way, because the connecting morphism in the triangle is not arbitrary,
-- it's given by the axioms. (The statements are still okay thanks to the uniqueness.)

def truncLEδGE' (n m : ℤ) (h : n + 1 = m) :
    truncLE n ⟶ truncGE m ⋙ shiftFunctor C (1 : ℤ) := sorry

@[simps!]
noncomputable def triangleGELE' (n m : ℤ) (h : n + 1 = m) : C ⥤ Triangle C :=
  Triangle.functorMk (truncGEι m) (truncLEπ n) (truncLEδGE' n m h)

lemma triangleGELE'_distinguished (n m : ℤ) (h : n + 1 = m) (X : C) :
    (triangleGELE' n m h).obj X ∈ distTriang C := sorry

def truncLEδGE (n : ℤ) :
    truncLE n ⟶ truncGE (n + 1) ⋙ shiftFunctor C (1 : ℤ) := truncLEδGE' n (n + 1) rfl

@[simps!]
def triangleGELE (n : ℤ) : C ⥤ Triangle C := triangleGELE' n (n + 1) rfl

lemma triangleGELE_distinguished (n : ℤ) (X : C) :
    (triangleGELE n).obj X ∈ distTriang C :=
  triangleGELE'_distinguished n (n + 1) rfl X

-- Uniqueness.
-- Here we are cheating too, because the maps are specific ones!

def truncGELE_le_up (a b c : ℤ) (h : b ≤ c) :
    truncGELE (C := C) a b ⟶ truncGELE a c := by
  dsimp [truncGELE]
  sorry

def truncGELE_le_down (a b c : ℤ) (h : a ≤ b) :
    truncGELE (C := C) a c ⟶ truncGELE b c := sorry

def truncGELE_δ (a b c : ℤ) :
    truncGELE (C := C) (b + 1) c ⟶ truncGELE a b ⋙ shiftFunctor C (1 : ℤ) := sorry

def truncGELE_triangle (a b c : ℤ) (h : a ≤ b) (h' : b ≤ c) : C ⥤ Triangle C :=
  Triangle.functorMk (truncGELE_le_up a b c h') (truncGELE_le_down a (b + 1) c (by linarith))
  (truncGELE_δ a b c)

lemma truncGELE_triangle_distinguished (a b c : ℤ) (h : a ≤ b) (h' : b ≤ c) (X : C) :
    (truncGELE_triangle a b c h h').obj X ∈ distTriang C := sorry

-- Prop A.1.3 (iv): we need to explain what compatibilities are hidden under the
-- adjective "canonical".
-- Here, there is an isomorphism given by the universal property of the
-- adjoint.

-- Also, we actually want the isomorphisms for "second" shifts
-- by any integer, compatible with the zero and the addition, like in `Functor.CommShift`.
-- Let's introduce a new structure for this. (It should be a class really.)

def familyCommShift.isoZero (F : ℤ → (C ⥤ C)) (n n' : ℤ) (h : n' = n) :
    shiftFunctor₂ C 0 ⋙ F n ≅ F n' ⋙ shiftFunctor₂ C 0 :=
  Functor.CommShift.isoZero (F n) ℤ ≪≫ eqToIso (X := F n ⋙ shiftFunctor₂ C 0)
  (Y := F n' ⋙ shiftFunctor₂ C 0) (by rw [h])

def familyCommShift.isoAdd (F : ℤ → (C ⥤ C)) (n a b n' n'' : ℤ)
    (e₁ : shiftFunctor₂ C a ⋙ F n ≅ F n' ⋙ shiftFunctor₂ C a)
    (e₂ : shiftFunctor₂ C b ⋙ F n' ≅ F n'' ⋙ shiftFunctor₂ C b) :
    shiftFunctor₂ C (a + b) ⋙ F n ≅ F n'' ⋙ shiftFunctor₂ C (a + b) :=
  isoWhiskerRight (shiftFunctorAdd' (FilteredShift C) b a (a + b) (add_comm _ _)) (F n)
  ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft (shiftFunctor₂ C b) e₁ ≪≫
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₂ (shiftFunctor₂ C a) ≪≫
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (F n'')
  (shiftFunctorAdd' (FilteredShift C) b a (a + b) (add_comm _ _)).symm

structure familyCommShift (F : ℤ → (C ⥤ C)) where
  iso (n m n' : ℤ) (h : n' + m = n) : shiftFunctor₂ C m ⋙ F n ≅ F n' ⋙ shiftFunctor₂ C m
  zero (n n' : ℤ) (h : n' = n) :
      iso n 0 n' (by simp [h]) = familyCommShift.isoZero F n n' h
  add (n a b n' n'' : ℤ) (h : n' + a = n) (h' : n'' + b = n') :
      iso n (a + b) n'' (by rw [add_comm a b, ← add_assoc, h', h]) =
      familyCommShift.isoAdd F n a b n' n'' (iso n a n' h) (iso n' b n'' h')

variable (C) in
abbrev shiftFunctor₂' (n m n' : ℤ) (h : n' + m = n) :
    (FilteredTriangulated.LE (C := C) n').P.FullSubcategory ⥤
    (FilteredTriangulated.LE (C := C) n).P.FullSubcategory where
      obj X := ⟨(shiftFunctor₂ C m).obj X.1,
        ((isLE_shift_iff X.1 n' m n (by rw [add_comm, h])).mpr {le := X.2}).le⟩
      map := (shiftFunctor₂ C m).map
      map_id X := (shiftFunctor₂ C m).map_id X.1
      map_comp := (shiftFunctor₂ C m).map_comp

-- Maybe this construction and the next should use `conjugateEquiv` instead?
def truncLE_commShift_hom (n m n' : ℤ) (h : n' + m = n) :
    shiftFunctor₂ C m ⋙ truncLE n ⟶ truncLE n' ⋙ shiftFunctor₂ C m := by
  set u : TwoSquare (FilteredTriangulated.LE (C := C) n').P.ι (shiftFunctor₂' C n m n' h)
      (shiftFunctor₂ C m) (FilteredTriangulated.LE n).P.ι :=
    {app X := 𝟙 _, naturality X Y f := by dsimp; rw [id_comp, comp_id]}
  refine (Functor.associator _ _ _).inv ≫ whiskerRight ((mateEquiv (reflectorAdjunction _)
    (reflectorAdjunction _)).symm u) _ ≫ (Functor.associator _ _ _).hom ≫
    whiskerLeft _ (𝟙 _)

instance (n m n' : ℤ) (h : n' + m = n) : IsIso (truncLE_commShift_hom (C := C) n m n' h) := sorry

def truncLE_commShift : familyCommShift (fun n ↦ truncLE (C := C) n) where
  iso n m n' h := asIso (truncLE_commShift_hom (C := C) n m n' h)
  zero := sorry
  add := sorry

variable (C) in
abbrev shiftFunctor₂'' (n m n' : ℤ) (h : n' + m = n) :
    (FilteredTriangulated.GE (C := C) n').P.FullSubcategory ⥤
    (FilteredTriangulated.GE (C := C) n).P.FullSubcategory where
      obj X := ⟨(shiftFunctor₂ C m).obj X.1,
        ((isGE_shift_iff X.1 n' m n (by rw [add_comm, h])).mpr {ge := X.2}).ge⟩
      map := (shiftFunctor₂ C m).map
      map_id X := (shiftFunctor₂ C m).map_id X.1
      map_comp := (shiftFunctor₂ C m).map_comp

def truncGE_commShift_inv (n m n' : ℤ) (h : n' + m = n) :
    truncGE n' ⋙ shiftFunctor₂ C m ⟶ shiftFunctor₂ C m ⋙ truncGE n := by
  set u : TwoSquare (shiftFunctor₂'' C n m n' h) (FilteredTriangulated.GE (C := C) n').P.ι
      (FilteredTriangulated.GE (C := C) n).P.ι (shiftFunctor₂ C m) :=
    {app X := 𝟙 _, naturality X Y f := by dsimp; rw [id_comp, comp_id]}
  refine ?_ ≫ whiskerRight ((mateEquiv (coreflectorAdjunction _) (coreflectorAdjunction _) u)) _
    ≫ (Functor.associator _ _ _).hom
  exact 𝟙 _

instance (n m n' : ℤ) (h : n' + m = n) : IsIso (truncGE_commShift_inv (C := C) n m n' h) := sorry

def truncGE_commShift : familyCommShift (fun n ↦ truncGE (C := C) n) where
  iso n m n' h := (asIso (truncGE_commShift_inv n m n' h)).symm
  zero := sorry
  add := sorry

end Truncation

/-
The next thing in the paper is the definition, when we have a filtered triangulated category `C`
over a triangulated category `A`, of the "graded pieces" functors `Gr n : C ⥤ A`, which use
an arbitrary quasi-inverse of the fully faithful functor `i : A ⥤ C` on the essential image of
`i`.

Rather than using an arbitrary quasi-inverse, it makes things much simpler to use the one
given by the "forget the filtration" functor `ω : C ⥤ A`, which has the addditional pleasant
property that it is defined on all of `C` and so avoids an `ObjectProperty.lift`. For this,
we need to change the order of statements and do Proposition A.1.6 first (this is possible as
that proposition makes no use of the functors `Gr n`).
-/

-- First a technical definition. (Is this really useful?)
variable {E E' M : Type*} [Category E] [Category E'] [AddMonoid M] [HasShift E M]

structure leftCommShift (G : M → (E ⥤ E')) where
  iso (a b c : M) (h : a = c + b) : shiftFunctor E b ⋙ G a ≅ G c
  zero (a c : M) (h : a = c) : iso a 0 c (by rw [add_zero, h]) =
      isoWhiskerRight (shiftFunctorZero E M) (G a) ≪≫ Functor.leftUnitor _ ≪≫
      eqToIso (by rw [h])
  add (a b b' c c' : M) (h : a = c + b) (h' : c = c' + b') :
      iso a (b' + b) c' (by rw [← add_assoc, ← h', h]) =
      isoWhiskerRight (shiftFunctorAdd E b' b) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (iso a b c h) ≪≫ iso c b' c' h'

section Forget

variable (L : isFilteredTriangulated_over C A)

-- Proposition A.1.6 asserts the existence of a "forget the filtration" functor
-- `C ⥤ A` with a slew of properties that uniquely characterize it.

-- Let's start with the existence statements.

def ForgetFiltration (L : isFilteredTriangulated_over C A) : C ⥤ A := sorry

-- Property (a). Note that this is an existence statement (it asserts the existence
-- of an adjunction).

def ForgetFiltration_leftAdjoint :
    Adjunction (ObjectProperty.ι (fun (X : C) ↦ IsLE X 0) ⋙ ForgetFiltration L)
    (ObjectProperty.lift _ L.functor
    (fun X ↦ (isFilteredTriangulated_over_image L X).1)) := sorry

-- Property (b). Same remark as for (a).

def ForgetFiltration_rightAdjoint :
    Adjunction (ObjectProperty.lift _ L.functor
    (fun X ↦ (isFilteredTriangulated_over_image L X).2))
    (ObjectProperty.ι (fun (X : C) ↦ IsGE X 0) ⋙ ForgetFiltration L) := sorry

/-
Property (a) gives an isomorphism `L.functor ≫ ForgetFiltration ≅ 𝟭 A` (by taking the counit
of the adjunction), and property (b) gives an isomorphism in the other direction
(by taking the unit of the adjunction). Although this is not stated in the paper, we want these
isomorphisms to be inverses of each other.
-/

lemma ForgetFiltration_iso_comp :
    (ForgetFiltration_rightAdjoint L).unit ≫ (ForgetFiltration_leftAdjoint L).counit = 𝟙 _ := sorry

-- Property (c).

lemma ForgetFiltration_shift (X : C) : IsIso ((ForgetFiltration L).map (hCP.α.app X)) := sorry

-- This implies a full `leftCommShift` structure on `ForgetFiltration`.
-- I don't want to define this, since the existence of the `leftCommShift` structure (given by `α`)
-- should probably replace property (c).

def ForgetFiltration_commShift :
    leftCommShift (fun (n : ℤ) ↦ ForgetFiltration (C := C) L) (E := FilteredShift C) := sorry

-- Property (d).

lemma ForgetFiltration_ff (X Y : C) (hX : IsLE X 0) (hY : IsGE Y 0) :
    Function.Bijective (fun (f : X ⟶ Y) ↦ (ForgetFiltration L).map f) := sorry

-- The functor should also be triangulated.
-- (This actually follows from the other conditions, but is
-- not stated in the paper. Note that the first instance contains
-- data! So I am actually cheating here, because the data is determined
-- by the other properties of `ForgetFiltration`.)

instance : (ForgetFiltration L).CommShift ℤ := sorry

instance : (ForgetFiltration L).IsTriangulated := sorry

-- The uniqueness statements are painful to state because we don't just want an
-- isomorphism, we want it to respect the extra structure (i.e. the adjunction).

def ForgetFiltration_uniq_left (G : C ⥤ A)
    (left_adj : Adjunction (ObjectProperty.ι (fun (X : C) ↦ IsLE X 0) ⋙ G)
    (ObjectProperty.lift _ L.functor
    (fun X ↦ (isFilteredTriangulated_over_image L X).1)))
    (shift : ∀ (X : C), IsIso (G.map (hCP.α.app X))) :
    ForgetFiltration L ≅ G := sorry

lemma ForgetFiltration_uniq_left_compat (G : C ⥤ A)
    (left_adj : Adjunction (ObjectProperty.ι (fun (X : C) ↦ IsLE X 0) ⋙ G)
    (ObjectProperty.lift _ L.functor
    (fun X ↦ (isFilteredTriangulated_over_image L X).1)))
    (shift : ∀ (X : C), IsIso (G.map (hCP.α.app X))) :
    left_adj = Adjunction.ofNatIsoLeft (ForgetFiltration_leftAdjoint L)
    (isoWhiskerLeft _ (ForgetFiltration_uniq_left L G left_adj shift)) := sorry

lemma ForgetFiltration_uniq_left_uniq (G : C ⥤ A)
    (left_adj : Adjunction (ObjectProperty.ι (fun (X : C) ↦ IsLE X 0) ⋙ G)
    (ObjectProperty.lift _ L.functor
    (fun X ↦ (isFilteredTriangulated_over_image L X).1)))
    (shift : ∀ (X : C), IsIso (G.map (hCP.α.app X))) (e : ForgetFiltration L ≅ G)
    (compat : left_adj = Adjunction.ofNatIsoLeft (ForgetFiltration_leftAdjoint L)
    (isoWhiskerLeft _ e)) :
    e = ForgetFiltration_uniq_left L G left_adj shift := sorry

-- Second uniqueness statement: this is similar, let's not state it.

/- Property (a) implies that we have an isomorphism `L.functor ≫ ForgetFiltration ≅ 𝟭 A`.
Property (b) gives an isomorphism in the other direction, and lemma `ForgetFiltration_iso_comp`
implies that these isomorphisms are inverses of each other.
-/
def ForgetFiltration_functor : L.functor ⋙ ForgetFiltration L ≅ 𝟭 A := by
  have := L.ff.full
  have := L.ff.faithful
  set e := (ForgetFiltration_leftAdjoint L).counit
  have : IsIso e := inferInstance
  exact isoWhiskerRight (ObjectProperty.liftCompιIso (fun X ↦ IsLE X 0) L.functor
    (fun X ↦ (isFilteredTriangulated_over_image L X).1)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ asIso e

/-
The composition in the other direction is isomorphic to `truncGELE 0 0`.
-/

def Functor_forgetFiltration : ForgetFiltration L ⋙ L.functor ≅ truncGELE 0 0 := sorry


-- So `ForgetFiltration` gives a quasi-inverse of the equivalence
-- `(isFilteredTriangulated_over_equiv L)`.
-- (Is this useful?)

def ForgetFiltration_vs_equiv :
    (ObjectProperty.ι (fun X ↦ IsLE X 0 ∧ IsGE X 0)) ⋙ ForgetFiltration L ≅
    (isFilteredTriangulated_over_equiv L).inv := by
  refine ?_ ≪≫ Functor.rightUnitor _
  refine (Iso.inverseCompIso (G := (isFilteredTriangulated_over_equiv L).asEquivalence) ?_).symm
  refine ?_ ≪≫ Functor.associator _ _ _
  refine (ForgetFiltration_functor L).symm ≪≫ isoWhiskerRight (ObjectProperty.liftCompιIso
    (fun X ↦ IsLE X 0 ∧ IsGE X 0) _ (isFilteredTriangulated_over_image L)).symm _

end Forget

section Graded
-- Definition A.1.4.
variable (L : isFilteredTriangulated_over C A) (n : ℤ)

def Gr_aux : C ⥤ C := truncGELE n n ⋙ shiftFunctor₂ C (-n)

-- `Gr_aux` is triangulated.

instance (n : ℤ) : (Gr_aux (C := C) n).CommShift ℤ := by
  dsimp [Gr_aux]; infer_instance

instance (n : ℤ) : (Gr_aux (C := C) n).IsTriangulated := by
  dsimp [Gr_aux]; infer_instance

/- The essential image of `Gr_aux` is contained in the full subcategory of objects that
are both `≤ 0` and `≥ 0`.
-/
lemma Gr_aux_image (X : C) : IsLE ((Gr_aux n).obj X) 0 ∧ IsGE ((Gr_aux n).obj X) 0 := by
  dsimp [Gr_aux]
  constructor
  · have : IsLE ((shiftFunctor₂ C (-n)).obj ((truncLEGE n n).obj X)) 0 := by
      dsimp [truncLEGE]
      exact isLE_shift _ n (-n) 0 (neg_add_cancel _)
    refine isLE_of_iso ((shiftFunctor₂ C (-n)).mapIso ((asIso (truncLEGEToGELE n n)).app X)) 0
  · dsimp [truncGELE]
    exact isGE_shift _ n (-n) 0 (neg_add_cancel _)

def Gr_aux_trunc : Gr_aux (C := C) n ⋙ truncGELE 0 0 ≅ Gr_aux n := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun {X Y} f ↦ ?_)
  · have := (Gr_aux_image n X).1
    have := (Gr_aux_image n X).2
    have : IsGE ((truncLE 0).obj ((Gr_aux n).obj X)) 0 := inferInstance
    exact asIso ((truncGEι 0).app ((truncLE 0).obj ((Gr_aux n).obj X))) ≪≫
      (asIso ((truncLEπ 0).app ((Gr_aux n).obj X))).symm
  · dsimp
    slice_lhs 1 2 => rw [(truncGEι 0).naturality, Functor.id_map]
    have := (Gr_aux_image n Y).1
    rw [← cancel_mono ((truncLEπ 0).app ((Gr_aux n).obj Y))]
    simp only [Functor.id_obj, assoc, IsIso.inv_hom_id, comp_id]
    have := (truncLEπ 0).naturality ((Gr_aux n).map f)
    simp only [Functor.id_obj, Functor.id_map] at this
    rw [this]
    simp only [IsIso.inv_hom_id_assoc]

def Gr : C ⥤ A :=
  Gr_aux n ⋙ ForgetFiltration L

def Gr_Gr_aux : Gr L n ⋙ L.functor ≅ Gr_aux n :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor_forgetFiltration L) ≪≫ Gr_aux_trunc n

-- `Gr` is triangulated.

instance (n : ℤ) : (Gr L n).CommShift ℤ := by
  dsimp [Gr]; infer_instance

instance (n : ℤ) : (Gr L n).IsTriangulated := by
  dsimp [Gr]; infer_instance

-- Proposition A.1.5(i).

-- Again, the isomorphisms are explicit.
def Gr_commShift : leftCommShift (fun n ↦ Gr (C := C) L n) (E := FilteredShift C) := sorry

-- Proposition A.1.5(ii).

lemma Gr_aux_pure_zero_of_ne_zero {n : ℤ} (h : n ≠ 0) (X : A) :
    Limits.IsZero ((Gr_aux n).obj (L.functor.obj X)) := sorry

lemma Gr_pure_zero_of_ne_zero {n : ℤ} (h : n ≠ 0) (X : A) :
    Limits.IsZero ((Gr L n).obj (L.functor.obj X)) := sorry

def Gr_aux_pure_of_zero (n : ℤ) (h : n = 0) : L.functor ⋙ Gr_aux n ≅ L.functor := by
  refine isoWhiskerLeft L.functor (eqToIso (by rw [h])) ≪≫ ?_
  refine (Functor.associator _ _ _).symm ≪≫ isoWhiskerLeft (L.functor ⋙ truncGELE 0 0)
    (shiftFunctorZero' _ (-0) neg_zero) ≪≫ Functor.rightUnitor _ ≪≫ ?_
  refine NatIso.ofComponents (fun X ↦ ?_) (fun {X Y} f ↦ ?_)
  · have := (isFilteredTriangulated_over_image L X).1
    have := (isFilteredTriangulated_over_image L X).2
    have : IsGE ((truncLE 0).obj (L.functor.obj X)) 0 := inferInstance
    exact asIso ((truncGEι 0).app ((truncLE 0).obj (L.functor.obj X))) ≪≫
      (asIso ((truncLEπ 0).app (L.functor.obj X))).symm
  · dsimp
    slice_lhs 1 2 => rw [(truncGEι 0).naturality, Functor.id_map]
    have := (isFilteredTriangulated_over_image L Y).1
    rw [← cancel_mono ((truncLEπ 0).app (L.functor.obj Y))]
    simp only [Functor.id_obj, assoc, IsIso.inv_hom_id, comp_id]
    have := (truncLEπ 0).naturality (L.functor.map f)
    simp only [Functor.id_obj, Functor.id_map] at this
    rw [this]
    simp only [IsIso.inv_hom_id_assoc]

def Gr_pure_of_zero (n : ℤ) (h : n = 0) : L.functor ⋙ Gr L n ≅ 𝟭 A :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Gr_aux_pure_of_zero L n h) _ ≪≫
  ForgetFiltration_functor L

-- Proposition A.1.5(iii).
-- Here the math statement doesn't say everything we want it to, because the
-- isomorphisms are not arbitrary ones, they're given by `truncLEπ` and `truncGEι`.

lemma Gr_truncLE_zero (r n : ℤ) (h : n < r) (X : C) :
    Limits.IsZero ((truncLE n ⋙ Gr L r).obj X) := sorry

lemma isIso_Gr_truncLEπ (r n : ℤ) (h : r ≤ n) :
    IsIso (whiskerRight (truncLEπ n) (Gr L r)) := sorry

lemma Gr_truncGE_zero (r n : ℤ) (h : r < n) (X : C) :
    Limits.IsZero ((truncGE n ⋙ Gr L r).obj X) := sorry

lemma isIso_Gr_truncGEι (r n : ℤ) (h : n ≤ r) :
    IsIso (whiskerRight (truncGEι n) (Gr L r)) := sorry

end Graded

section FunctorLiftCompat

variable (L₁ : isFilteredTriangulated_over C A) (L₂ : isFilteredTriangulated_over D B)
  {T : A ⥤ B} [T.CommShift ℤ] [T.IsTriangulated] (FT : T.filteredLifting L₁ L₂)

def filteredLifting_compat_Gr (n : ℤ) :
    Gr L₁ n ⋙ T ⋙ L₂.functor ≅ Gr_aux n ⋙ FT.functor :=
  isoWhiskerLeft _ FT.compat ≪≫ (Functor.associator _ _ _).symm ≪≫
  isoWhiskerRight (Gr_Gr_aux L₁ n) _

-- Proposition A.1.8 is a mess.
-- Again this is not precise, the natural isomorphisms are not arbitrary!
-- Also, the square with `truncGE` is missing, and we need more squares
-- with `truncGELE`, as well as compatibilities with the connecting
-- morphisms in the triangles of `truncGELE`.

/- Let's do `truncLE`. The "commutative" square says two things:
(1) `FT` sends objects that are `LE n` to objects that are `LE n`.
This gives an isomorphism from `FT.obj ((truncLE n).obj X)` to
`(truncLEπ n).obj (FT.obj ((truncLE n).obj X))` for every `X : C`,
and we want that:
(2) The composition of `(FT ⋙ truncLE n).map ((truncLEπ n).app X)` (going from
`(FT ⋙ truncLE n).obj X` to `(truncLEπ n).obj (FT.obj ((truncLE n).obj X))` with
the inverse of this isomorphism is an isomorphism. Of course, we don't need
to compose with an isomorphism to state that property.

This will give the natural isomorphism that makes the diagram commute.
-/
instance truncLE_lifting_iso_of_le (X : C) (n : ℤ) [IsLE X n] :
    IsIso ((truncLEπ n).app (FT.functor.obj X)) := sorry

instance truncLEπ_lifting_truncLE_iso (n : ℤ) :
    IsIso (whiskerRight (truncLEπ n) (FT.functor ⋙ truncLE n)) := sorry

instance truncLE_lifting_truncLEπ_iso (n : ℤ) :
    IsIso (whiskerLeft (truncLE n ⋙ FT.functor) (truncLEπ n)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  simp only [Functor.comp_obj, Functor.id_obj, whiskerLeft_app]
  infer_instance

def lifting_truncLE_comm (n : ℤ) :
    FT.functor ⋙ truncLE n ≅ truncLE n ⋙ FT.functor :=
  (Functor.leftUnitor _).symm ≪≫
  asIso (whiskerRight (truncLEπ n) (FT.functor ⋙ truncLE n))
  ≪≫ (asIso (whiskerLeft (truncLE n ⋙ FT.functor) (truncLEπ n))).symm
  ≪≫ Functor.rightUnitor _

-- Same idea for `truncGE`.

instance truncGE_lifting_iso_of_le (X : C) (n : ℤ) [IsGE X n] :
    IsIso ((truncGEι n).app (FT.functor.obj X)) := sorry

instance truncGEι_lifting_truncLE_iso (n : ℤ) :
    IsIso (whiskerRight (truncGEι n) (FT.functor ⋙ truncGE n)) := sorry

instance truncGE_lifting_truncGEι_iso (n : ℤ) :
    IsIso (whiskerLeft (truncGE n ⋙ FT.functor) (truncGEι n)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  simp only [Functor.comp_obj, Functor.id_obj, whiskerLeft_app]
  infer_instance

def lifting_truncGE_comm (n : ℤ) :
    FT.functor ⋙ truncGE n ≅ truncGE n ⋙ FT.functor :=
  (Functor.leftUnitor _).symm ≪≫
  (asIso (whiskerRight (truncGEι n) (FT.functor ⋙ truncGE n))).symm ≪≫
  asIso (whiskerLeft (truncGE n ⋙ FT.functor) (truncGEι n)) ≪≫
  Functor.rightUnitor _

-- Now the square with `Gr` follows from the ones with `truncLE` and `truncGE`,
-- since we already know that `FT` "commutes" with `s`.

def lifting_Gr_aux_comm (n : ℤ) :
    FT.functor ⋙ Gr_aux n ≅ Gr_aux n ⋙ FT.functor :=
  (Functor.associator _ _ _).symm ≪≫
  isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
  isoWhiskerRight (isoWhiskerRight (lifting_truncLE_comm L₁ L₂ FT n) _) _ ≪≫
  isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
  isoWhiskerRight (isoWhiskerLeft _ (lifting_truncGE_comm L₁ L₂ FT n)) _ ≪≫
  isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
  Functor.associator _ _ _ ≪≫
  isoWhiskerLeft _ (FT.commShift.iso ((0, -n) : ℤ × ℤ)).symm ≪≫
  (Functor.associator _ _ _).symm

def liftin_Gr_comm_aux (n : ℤ) :
    FT.functor ⋙ Gr L₂ n ⋙ L₂.functor ≅ Gr L₁ n ⋙ T ⋙ L₂.functor :=
  isoWhiskerLeft _ (Gr_Gr_aux L₂ n) ≪≫ lifting_Gr_aux_comm L₁ L₂ FT n ≪≫
  (filteredLifting_compat_Gr L₁ L₂ FT n).symm

def lifting_Gr_comm (n : ℤ) : FT.functor ⋙ Gr L₂ n ≅  Gr L₁ n ⋙ T := by
  have := L₂.ff.faithful
  have := L₂.ff.full
  exact Functor.fullyFaithfulCancelRight L₂.functor (liftin_Gr_comm_aux L₁ L₂ FT n)

-- Commutativity by `ForgetFiltration`. Here too there must be extra compatibilities,
-- but I'm not sure what they all are. Let's see what happens later.

def lifting_forgetFiltrating_comm :
    FT.functor ⋙ ForgetFiltration L₂ ≅ ForgetFiltration L₁ ⋙ T := sorry

end FunctorLiftCompat

end CategoryTheory
