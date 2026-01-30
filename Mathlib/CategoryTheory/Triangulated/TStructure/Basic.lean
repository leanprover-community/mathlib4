/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# t-structures on triangulated categories

This file introduces the notion of t-structure on (pre)triangulated categories.

The first example of t-structure shall be the canonical t-structure on the
derived category of an abelian category (TODO).

Given a t-structure `t : TStructure C`, we define typeclasses `t.IsLE X n`
and `t.IsGE X n` in order to say that an object `X : C` is `≤ n` or `≥ n` for `t`.

## Implementation notes

We introduce the type of t-structures rather than a type class saying that we
have fixed a t-structure on a certain category. The reason is that certain
triangulated categories have several t-structures which one may want to
use depending on the context.

## TODO


* define functors `t.truncLE n : C ⥤ C`, `t.truncGE n : C ⥤ C` and the
  associated distinguished triangles
* promote these truncations to a (functorial) spectral object
* define the heart of `t` and show it is an abelian category
* define triangulated subcategories `t.plus`, `t.minus`, `t.bounded` and show
  that there are induced t-structures on these full subcategories

## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*][bbd-1982]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Limits

variable (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

open Pretriangulated

/-- `TStructure C` is the type of t-structures on the (pre)triangulated category `C`. -/
structure TStructure where
  /-- the predicate of objects that are `≤ n` for `n : ℤ`. -/
  le (n : ℤ) : ObjectProperty C
  /-- the predicate of objects that are `≥ n` for `n : ℤ`. -/
  ge (n : ℤ) : ObjectProperty C
  le_isClosedUnderIsomorphisms (n : ℤ) : (le n).IsClosedUnderIsomorphisms := by infer_instance
  ge_isClosedUnderIsomorphisms (n : ℤ) : (ge n).IsClosedUnderIsomorphisms := by infer_instance
  le_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : le n X) : le n' (X⟦a⟧)
  ge_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : ge n X) : ge n' (X⟦a⟧)
  zero' ⦃X Y : C⦄ (f : X ⟶ Y) (hX : le 0 X) (hY : ge 1 Y) : f = 0
  le_zero_le : le 0 ≤ le 1
  ge_one_le : ge 1 ≤ ge 0
  exists_triangle_zero_one (A : C) : ∃ (X Y : C) (_ : le 0 X) (_ : ge 1 Y)
    (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C

namespace TStructure

attribute [instance] le_isClosedUnderIsomorphisms ge_isClosedUnderIsomorphisms

variable {C}
variable (t : TStructure C)

lemma exists_triangle (A : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∃ (X Y : C) (_ : t.le n₀ X) (_ : t.ge n₁ Y) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := t.exists_triangle_zero_one (A⟦n₀⟧)
  let T := (Triangle.shiftFunctor C (-n₀)).obj (Triangle.mk f g h)
  let e := (shiftEquiv C n₀).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
    refine isomorphic_distinguished _ (Triangle.shift_distinguished _ mem (-n₀)) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    all_goals simp [T]
  exact ⟨_, _, t.le_shift _ _ _ (neg_add_cancel n₀) _ hX,
    t.ge_shift _ _ _ (by lia) _ hY, _, _, _, hT'⟩

lemma shift_le (a n n' : ℤ) (hn' : a + n = n') :
    (t.le n).shift a = t.le n' := by
  ext X
  constructor
  · intro hX
    exact ((t.le n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.le_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.le_shift _ _ _ hn' X hX

lemma shift_ge (a n n' : ℤ) (hn' : a + n = n') :
    (t.ge n).shift a = t.ge n' := by
  ext X
  constructor
  · intro hX
    exact ((t.ge n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.ge_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.ge_shift _ _ _ hn' X hX

lemma le_monotone : Monotone t.le := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.le n ≤ t.le (n + a)
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_le n 1 (n + (1 : ℕ)) rfl, ObjectProperty.prop_shift_iff]
    rw [← t.shift_le n 0 n (add_zero n), ObjectProperty.prop_shift_iff] at hX
    exact t.le_zero_le _ hX
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (ha n).trans (hb (n + a))
  intro a
  induction a with
  | zero => exact H_zero
  | succ a ha => exact H_add a 1 _ rfl ha H_one

lemma ge_antitone : Antitone t.ge := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.ge (n + a) ≤ t.ge n
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_ge n 1 (n + (1 : ℕ)) (by simp), ObjectProperty.prop_shift_iff] at hX
    rw [← t.shift_ge n 0 n (add_zero n)]
    exact t.ge_one_le _ hX
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction a with
  | zero => exact H_zero
  | succ a ha => exact H_add a 1 _ rfl ha H_one

/-- Given a t-structure `t` on a pretriangulated category `C`, the property `t.IsLE X n`
holds if `X : C` is `≤ n` for the t-structure. -/
class IsLE (X : C) (n : ℤ) : Prop where
  le : t.le n X

/-- Given a t-structure `t` on a pretriangulated category `C`, the property `t.IsGE X n`
holds if `X : C` is `≥ n` for the t-structure. -/
class IsGE (X : C) (n : ℤ) : Prop where
  ge : t.ge n X

lemma le_of_isLE (X : C) (n : ℤ) [t.IsLE X n] : t.le n X := IsLE.le

lemma ge_of_isGE (X : C) (n : ℤ) [t.IsGE X n] : t.ge n X := IsGE.ge

lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsLE X n] : t.IsLE Y n where
  le := (t.le n).prop_of_iso e (t.le_of_isLE X n)

lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsGE X n] : t.IsGE Y n where
  ge := (t.ge n).prop_of_iso e (t.ge_of_isGE X n)

lemma isLE_of_le (X : C) (p q : ℤ) (hpq : p ≤ q := by lia) [t.IsLE X p] : t.IsLE X q where
  le := le_monotone t hpq _ (t.le_of_isLE X p)

lemma isGE_of_ge (X : C) (p q : ℤ) (hpq : p ≤ q := by lia) [t.IsGE X q] : t.IsGE X p where
  ge := ge_antitone t hpq _ (t.ge_of_isGE X q)

@[deprecated (since := "2026-01-30")] alias isLE_of_LE := isLE_of_le
@[deprecated (since := "2026-01-30")] alias isGE_of_GE := isGE_of_ge

lemma isLE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) [t.IsLE X n] :
    t.IsLE (X⟦a⟧) n' :=
  ⟨t.le_shift n a n' hn' X (t.le_of_isLE X n)⟩

lemma isGE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) [t.IsGE X n] :
    t.IsGE (X⟦a⟧) n' :=
  ⟨t.ge_shift n a n' hn' X (t.ge_of_isGE X n)⟩

lemma isLE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) [t.IsLE (X⟦a⟧) n'] :
    t.IsLE X n := by
  have h := t.isLE_shift (X⟦a⟧) n' (-a) n
  exact t.isLE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

lemma isGE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) [t.IsGE (X⟦a⟧) n'] :
    t.IsGE X n := by
  have h := t.isGE_shift (X⟦a⟧) n' (-a) n
  exact t.isGE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

lemma isLE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) :
    t.IsLE (X⟦a⟧) n' ↔ t.IsLE X n := by
  constructor
  · intro
    exact t.isLE_of_shift X n a n' hn'
  · intro
    exact t.isLE_shift X n a n' hn'

lemma isGE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) :
    t.IsGE (X⟦a⟧) n' ↔ t.IsGE X n := by
  constructor
  · intro
    exact t.isGE_of_shift X n a n' hn'
  · intro
    exact t.isGE_shift X n a n' hn'

lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁ := by lia)
    [t.IsLE X n₀] [t.IsGE Y n₁] : f = 0 := by
  have := t.isLE_shift X n₀ n₀ 0 (add_zero n₀)
  have := t.isGE_shift Y n₁ n₀ (n₁ - n₀)
  have := t.isGE_of_ge (Y⟦n₀⟧) 1 (n₁ - n₀)
  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  · apply t.le_of_isLE
  · apply t.ge_of_isGE

lemma zero_of_isLE_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    (_ : t.IsLE X n₀) (_ : t.IsGE Y n₁) : f = 0 :=
  t.zero f n₀ n₁ h

lemma isZero (X : C) (n₀ n₁ : ℤ) (h : n₀ < n₁ := by lia)
    [t.IsLE X n₀] [t.IsGE X n₁] : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact t.zero _ n₀ n₁ h

/-- The full subcategory consisting of `t`-bounded above objects. -/
def minus : ObjectProperty C := fun X ↦ ∃ (n : ℤ), t.IsLE X n

/-- The full subcategory consisting of `t`-bounded below objects. -/
def plus : ObjectProperty C := fun X ↦ ∃ (n : ℤ), t.IsGE X n

/-- The full subcategory consisting of `t`-bounded objects. -/
def bounded : ObjectProperty C := t.plus ⊓ t.minus

instance : t.minus.IsClosedUnderIsomorphisms where
  of_iso e := by rintro ⟨n, _⟩; exact ⟨_, t.isLE_of_iso e n⟩

instance : t.minus.IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isLE_shift _ i _ _ (by omega)⟩ }

instance : t.plus.IsClosedUnderIsomorphisms where
  of_iso e := by rintro ⟨n, _⟩; exact ⟨_, t.isGE_of_iso e n⟩

instance : t.plus.IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isGE_shift _ i _ _ (by omega)⟩ }

instance : t.bounded.IsClosedUnderIsomorphisms := by
  dsimp [bounded]
  infer_instance

instance : t.bounded.IsStableUnderShift ℤ := by
  dsimp [bounded]
  infer_instance

end TStructure

end Triangulated

end CategoryTheory
