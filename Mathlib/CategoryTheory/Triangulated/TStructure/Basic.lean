/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Predicate
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

namespace CategoryTheory

open Limits

namespace Triangulated

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

open Pretriangulated

/-- `TStructure C` is the type of t-structures on the (pre)triangulated category `C`. -/
structure TStructure where
  /-- the predicate of objects that are `≤ n` for `n : ℤ`. -/
  LE (n : ℤ) : C → Prop
  /-- the predicate of objects that are `≥ n` for `n : ℤ`. -/
  GE (n : ℤ) : C → Prop
  LE_closedUnderIsomorphisms (n : ℤ) : ClosedUnderIsomorphisms (LE n) := by infer_instance
  GE_closedUnderIsomorphisms (n : ℤ) : ClosedUnderIsomorphisms (GE n) := by infer_instance
  LE_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : LE n X) : LE n' (X⟦a⟧)
  GE_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : GE n X) : GE n' (X⟦a⟧)
  zero' ⦃X Y : C⦄ (f : X ⟶ Y) (hX : LE 0 X) (hY : GE 1 Y) : f = 0
  LE_zero_le : LE 0 ≤ LE 1
  GE_one_le : GE 1 ≤ GE 0
  exists_triangle_zero_one (A : C) : ∃ (X Y : C) (_ : LE 0 X) (_ : GE 1 Y)
    (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C

namespace TStructure

attribute [instance] LE_closedUnderIsomorphisms GE_closedUnderIsomorphisms

variable {C}
variable (t : TStructure C)

lemma exists_triangle (A : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∃ (X Y : C) (_ : t.LE n₀ X) (_ : t.GE n₁ Y) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := t.exists_triangle_zero_one (A⟦n₀⟧)
  let T := (Triangle.shiftFunctor C (-n₀)).obj (Triangle.mk f g h)
  let e := (shiftEquiv C n₀).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
    refine isomorphic_distinguished _ (Triangle.shift_distinguished _ mem (-n₀)) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    all_goals dsimp; simp [T]
  exact ⟨_, _, t.LE_shift _ _ _ (neg_add_self n₀) _ hX,
    t.GE_shift _ _ _ (by omega) _ hY, _, _, _, hT'⟩

lemma predicateShift_LE (a n n' : ℤ) (hn' : a + n = n') :
    (PredicateShift (t.LE n) a) = t.LE n' := by
  ext X
  constructor
  · intro hX
    exact (mem_iff_of_iso (LE t n') ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.LE_shift n (-a) n' (by omega) _ hX)
  · intro hX
    exact t.LE_shift _ _ _ hn' X hX

lemma predicateShift_GE (a n n' : ℤ) (hn' : a + n = n') :
    (PredicateShift (t.GE n) a) = t.GE n' := by
  ext X
  constructor
  · intro hX
    exact (mem_iff_of_iso (GE t n') ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.GE_shift n (-a) n' (by omega) _ hX)
  · intro hX
    exact t.GE_shift _ _ _ hn' X hX

lemma LE_monotone : Monotone t.LE := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.LE n ≤ t.LE (n + a)
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.predicateShift_LE n 1 (n + (1 : ℕ)) rfl, predicateShift_iff]
    rw [← t.predicateShift_LE n 0 n (add_zero n), predicateShift_iff] at hX
    exact t.LE_zero_le _ hX
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (ha n).trans (hb (n+a))
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

lemma GE_antitone : Antitone t.GE := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.GE (n + a) ≤ t.GE n
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.predicateShift_GE n 1 (n + (1 : ℕ)) (by simp), predicateShift_iff] at hX
    rw [← t.predicateShift_GE n 0 n (add_zero n)]
    exact t.GE_one_le _ hX
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
  le : t.LE n X

/-- Given a t-structure `t` on a pretriangulated category `C`, the property `t.IsGE X n`
holds if `X : C` is `≥ n` for the t-structure. -/
class IsGE (X : C) (n : ℤ) : Prop where
  ge : t.GE n X

lemma mem_of_isLE (X : C) (n : ℤ) [t.IsLE X n] : t.LE n X := IsLE.le

lemma mem_of_isGE (X : C) (n : ℤ) [t.IsGE X n] : t.GE n X := IsGE.ge

end TStructure

end Triangulated

end CategoryTheory
