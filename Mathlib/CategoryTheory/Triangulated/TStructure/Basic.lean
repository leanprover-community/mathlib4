/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# t-structures on triangulated categories

This files introduces the notion of t-structure on (pre)triangulated categories.

The first example of t-structure shall be the canonical t-structure on the
derived category of an abelian category (TODO).

Given a t-structure `t : TStructure C`, we define type classes `t.IsLE X n`
and `t.IsGE X n` in order to say that an object `X : C` is `≤ n` or `≥ n` for `t`.

## Implementation notes

We introduce the type of t-structures rather than a type class saying that we
have fixed a t-structure on a certain category. The reason is that certain
triangulated categories have several t-structures which one may want to
use depending on the context.

## TODO

* define functors `t.truncLE n : C ⥤ C`,`t.truncGE n : C ⥤ C` and the
  associated distinguished triangles
* promote these truncations to a (functorial) spectral object
* define the heart of `t` and show it is an abelian category
* define triangulated subcategories `t.plus`, `t.minus`, `t.bounded` and show
  that there are induced t-structures on these full subcategories

## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*][bbd-1982]

-/

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Limits

namespace Triangulated

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

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
    t.ge_shift _ _ _ (by omega) _ hY, _, _, _, hT'⟩

lemma shift_le (a n n' : ℤ) (hn' : a + n = n') :
    (t.le n).shift a = t.le n' := by
  ext X
  constructor
  · intro hX
    exact ((t.le n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.le_shift n (-a) n' (by omega) _ hX)
  · intro hX
    exact t.le_shift _ _ _ hn' X hX

lemma shift_ge (a n n' : ℤ) (hn' : a + n = n') :
    (t.ge n).shift a = t.ge n' := by
  ext X
  constructor
  · intro hX
    exact ((t.ge n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.ge_shift n (-a) n' (by omega) _ hX)
  · intro hX
    exact t.ge_shift _ _ _ hn' X hX

lemma le_monotone : Monotone t.le := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.le n ≤ t.le (n + a)
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
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
    exact (ha n).trans (hb (n+a))
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

lemma ge_antitone : Antitone t.ge := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.ge (n + a) ≤ t.ge n
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
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
    rw [← h, Nat.cast_add, ← add_assoc ]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

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

@[deprecated (since := "2025-02-25")] alias LE := le
@[deprecated (since := "2025-02-25")] alias GE := ge
@[deprecated (since := "2025-02-25")] alias LE_shift := le_shift
@[deprecated (since := "2025-02-25")] alias GE_shift := ge_shift
@[deprecated (since := "2025-02-25")] alias LE_zero_le := le_zero_le
@[deprecated (since := "2025-02-25")] alias GE_one_le := ge_one_le
@[deprecated (since := "2025-02-25")] alias predicateShift_LE := shift_le
@[deprecated (since := "2025-02-25")] alias predicateShift_GE := shift_ge
@[deprecated (since := "2025-02-25")] alias LE_monotone := le_monotone
@[deprecated (since := "2025-02-25")] alias GE_antitone := ge_antitone
@[deprecated (since := "2025-02-25")] alias mem_of_isLE := le_of_isLE
@[deprecated (since := "2025-02-25")] alias mem_of_isGE := ge_of_isGE

end TStructure

end Triangulated

end CategoryTheory
