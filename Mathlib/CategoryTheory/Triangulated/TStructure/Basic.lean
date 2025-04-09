/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Linarith

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

/-import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.Tactic.Linarith

open CategoryTheory Category Limits

namespace CategoryTheory

section

variable {C : Type _} [Category C] (S : C → Prop)

variable {A : Type _} [AddMonoid A] [HasShift C A]

def PredicateShift (a : A) : C → Prop := fun X => S (X⟦a⟧)

lemma predicateShift_iff (a : A) (X : C) : PredicateShift S a X ↔ S (X⟦a⟧) := by rfl

instance predicateShift_closedUnderIsomorphisms (a : A) [ClosedUnderIsomorphisms S] :
    ClosedUnderIsomorphisms (PredicateShift S a) where
  mem_of_iso {X Y} e hX := by
    simp only [predicateShift_iff] at hX ⊢
    exact mem_of_iso S ((shiftFunctor C a).mapIso e) hX

variable (A)

@[simp]
lemma predicateShift_zero [ClosedUnderIsomorphisms S] : PredicateShift S (0 : A) = S := by
  ext X
  simp only [predicateShift_iff]
  exact mem_iff_of_iso S ((shiftFunctorZero C A).app X)

variable {A}

lemma predicateShift_predicateShift (a b c : A) (h : a + b = c) [ClosedUnderIsomorphisms S] :
    PredicateShift (PredicateShift S b) a = PredicateShift S c := by
  ext X
  simp only [predicateShift_iff]
  exact mem_iff_of_iso _ ((shiftFunctorAdd' C a b c h).symm.app X)

@[simp]
lemma essImageFullSubcategoryInclusion [ClosedUnderIsomorphisms S] :
    (fullSubcategoryInclusion S).essImage = setOf S := by
  ext X
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    dsimp
    rw [← mem_iff_of_iso S e]
    exact Y.2
  · intro hX
    exact ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩

end-/

namespace CategoryTheory

open Limits

namespace Triangulated

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

open Pretriangulated ObjectProperty

/-- `TStructure C` is the type of t-structures on the (pre)triangulated category `C`. -/
structure TStructure where
  /-- the predicate of objects that are `≤ n` for `n : ℤ`. -/
  LE (n : ℤ) : C → Prop
  /-- the predicate of objects that are `≥ n` for `n : ℤ`. -/
  GE (n : ℤ) : C → Prop
  LE_closedUnderIsomorphisms (n : ℤ) : IsClosedUnderIsomorphisms (LE n) := by infer_instance
  GE_closedUnderIsomorphisms (n : ℤ) : IsClosedUnderIsomorphisms (GE n) := by infer_instance
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
  exact ⟨_, _, t.LE_shift _ _ _ (neg_add_cancel n₀) _ hX,
    t.GE_shift _ _ _ (by omega) _ hY, _, _, _, hT'⟩

lemma predicateShift_LE (a n n' : ℤ) (hn' : a + n = n') :
    (shift (t.LE n) a) = t.LE n' := by
  ext X
  constructor
  · intro hX
    exact (prop_iff_of_iso (LE t n') ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.LE_shift n (-a) n' (by omega) _ hX)
  · intro hX
    exact t.LE_shift _ _ _ hn' X hX

lemma predicateShift_GE (a n n' : ℤ) (hn' : a + n = n') :
    (shift (t.GE n) a) = t.GE n' := by
  ext X
  constructor
  · intro hX
    exact (prop_iff_of_iso (GE t n') ((shiftEquiv C a).unitIso.symm.app X)).1
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
    rw [← t.predicateShift_LE n 1 (n + (1 : ℕ)) rfl, prop_shift_iff]
    rw [← t.predicateShift_LE n 0 n (add_zero n), prop_shift_iff] at hX
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
    rw [← t.predicateShift_GE n 1 (n + (1 : ℕ)) (by simp), prop_shift_iff] at hX
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

lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsLE X n] : t.IsLE Y n where
  le := prop_of_iso (t.LE n) e (t.mem_of_isLE X n)

lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsGE X n] : t.IsGE Y n where
  ge := prop_of_iso (t.GE n) e (t.mem_of_isGE X n)

lemma isLE_of_LE (X : C) (p q : ℤ) (hpq : p ≤ q) [t.IsLE X p] : t.IsLE X q where
  le := LE_monotone t hpq _ (t.mem_of_isLE X p)

lemma isGE_of_GE (X : C) (p q : ℤ) (hpq : p ≤ q) [t.IsGE X q] : t.IsGE X p where
  ge := GE_antitone t hpq _ (t.mem_of_isGE X q)

lemma isLE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsLE X n] :
    t.IsLE (X⟦a⟧) n' :=
  ⟨t.LE_shift n a n' hn' X (t.mem_of_isLE X n)⟩

lemma isGE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsGE X n] :
    t.IsGE (X⟦a⟧) n' :=
  ⟨t.GE_shift n a n' hn' X (t.mem_of_isGE X n)⟩

lemma isLE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsLE (X⟦a⟧) n'] :
    t.IsLE X n := by
  have h := t.isLE_shift (X⟦a⟧) n' (-a) n (by linarith)
  exact t.isLE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

lemma isGE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsGE (X⟦a⟧) n'] :
    t.IsGE X n := by
  have h := t.isGE_shift (X⟦a⟧) n' (-a) n (by linarith)
  exact t.isGE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

lemma isLE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n' = n) :
    t.IsLE (X⟦a⟧) n' ↔ t.IsLE X n := by
  constructor
  · intro
    exact t.isLE_of_shift X n a n' hn'
  · intro
    exact t.isLE_shift X n a n' hn'

lemma isGE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n' = n) :
    t.IsGE (X⟦a⟧) n' ↔ t.IsGE X n := by
  constructor
  · intro
    exact t.isGE_of_shift X n a n' hn'
  · intro
    exact t.isGE_shift X n a n' hn'

lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [t.IsLE X n₀] [t.IsGE Y n₁] : f = 0 := by
  have := t.isLE_shift X n₀ n₀ 0 (add_zero n₀)
  have := t.isGE_shift Y n₁ n₀ (n₁-n₀) (by linarith)
  have := t.isGE_of_GE (Y⟦n₀⟧) 1 (n₁-n₀) (by linarith)
  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  · apply t.mem_of_isLE
  · apply t.mem_of_isGE

lemma zero_of_isLE_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    (_ : t.IsLE X n₀) (_ : t.IsGE Y n₁) : f = 0 :=
  t.zero f n₀ n₁ h

lemma isZero (X : C) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [t.IsLE X n₀] [t.IsGE X n₁] : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact t.zero _ n₀ n₁ h

def heart (X : C) : Prop := t.LE 0 X ∧ t.GE 0 X

lemma mem_heart_iff (X : C) :
    t.heart X ↔ t.IsLE X 0 ∧ t.IsGE X 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨t.mem_of_isLE _ _, t.mem_of_isGE _ _⟩

instance : IsClosedUnderIsomorphisms t.heart where
  of_iso {X Y} e hX := by
    rw [mem_heart_iff] at hX ⊢
    have := hX.1
    have := hX.2
    constructor
    · exact t.isLE_of_iso e 0
    · exact t.isGE_of_iso e 0

class HasHeart where
  H : Type*
  [cat : Category H]
  [preadditive : Preadditive H]
  ι : H ⥤ C
  additive_ι : ι.Additive := by infer_instance
  fullι : ι.Full := by infer_instance
  faithful_ι : ι.Faithful := by infer_instance
  hι : ι.essImage = t.heart := by simp

def hasHeartFullSubcategory : t.HasHeart where
  H := FullSubcategory t.heart
  ι := fullSubcategoryInclusion t.heart
  hι := by
    ext X
    constructor
    · rintro ⟨⟨Y, hY⟩, ⟨e : Y ≅ X⟩⟩
      exact prop_of_iso t.heart e hY
    · intro hX
      exact ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩

variable [ht : t.HasHeart]

def Heart := ht.H

instance : Category t.Heart := ht.cat

def ιHeart : t.Heart ⥤ C := ht.ι

instance : Preadditive t.Heart := ht.preadditive
instance : t.ιHeart.Full := ht.fullι
instance : t.ιHeart.Faithful := ht.faithful_ι
instance : t.ιHeart.Additive := ht.additive_ι

lemma ιHeart_obj_mem (X : t.Heart) : t.heart (t.ιHeart.obj X) := by
  change (t.ιHeart.obj X) ∈ setOf t.heart
  rw [← ht.hι]
  exact t.ιHeart.obj_mem_essImage X

instance (X : t.Heart) : t.IsLE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).1⟩

instance (X : t.Heart) : t.IsGE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).2⟩

lemma mem_essImage_ιHeart_iff (X : C) :
    t.ιHeart.essImage X ↔ t.heart X := by
  dsimp [ιHeart]
  rw [ht.hι]

noncomputable def heartMk (X : C) (hX : t.heart X) : t.Heart :=
  Functor.essImage.witness ((t.mem_essImage_ιHeart_iff X).2 hX)

noncomputable def ιHeartObjHeartMkIso (X : C) (hX : t.heart X) :
    t.ιHeart.obj (t.heartMk X hX) ≅ X :=
  Functor.essImage.getIso ((t.mem_essImage_ιHeart_iff X).2 hX)

@[simps obj]
noncomputable def liftHeart {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), t.heart (F.obj X)) :
    D ⥤ t.Heart where
  obj X := t.heartMk (F.obj X) (hF X)
  map {X Y} f := t.ιHeart.preimage ((t.ιHeartObjHeartMkIso _ (hF X)).hom ≫ F.map f ≫
      (t.ιHeartObjHeartMkIso _ (hF Y)).inv)
  map_id X := t.ιHeart.map_injective (by simp)
  map_comp f g := t.ιHeart.map_injective (by simp)

@[simp, reassoc]
lemma ιHeart_map_liftHeart_map {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), t.heart (F.obj X)) {X Y : D} (f : X ⟶ Y) :
    t.ιHeart.map ((t.liftHeart F hF).map f) =
      (t.ιHeartObjHeartMkIso _ (hF X)).hom ≫ F.map f ≫
        (t.ιHeartObjHeartMkIso _ (hF Y)).inv := by
  simp [liftHeart]

noncomputable def liftHeartιHeart {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), t.heart (F.obj X)) :
    t.liftHeart F hF ⋙ t.ιHeart ≅ F :=
  NatIso.ofComponents (fun X => t.ιHeartObjHeartMkIso _ (hF X)) (by aesop_cat)

end TStructure

namespace Subcategory

variable {C}
variable (S : Subcategory C) (t : TStructure C)

class HasInducedTStructure : Prop where
  exists_triangle_zero_one (A : C) (hA : S.P A) :
    ∃ (X Y : C) (_ : t.LE 0 X) (_ : t.GE 1 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧) (_ : Triangle.mk f g h ∈ distTriang C),
    S.ι.essImage X ∧ S.ι.essImage Y

variable [h : S.HasInducedTStructure t]

def tStructure : TStructure S.category where
  LE n X := t.LE n (S.ι.obj X)
  GE n X := t.GE n (S.ι.obj X)
  LE_closedUnderIsomorphisms n := ⟨fun {X Y} e hX => prop_of_iso (t.LE n) (S.ι.mapIso e) hX⟩
  GE_closedUnderIsomorphisms n := ⟨fun {X Y} e hX => prop_of_iso (t.GE n) (S.ι.mapIso e) hX⟩
  LE_shift n a n' h X hX := prop_of_iso (t.LE n') ((S.ι.commShiftIso a).symm.app X)
    (t.LE_shift n a n' h (S.ι.obj X) hX)
  GE_shift n a n' h X hX := prop_of_iso (t.GE n') ((S.ι.commShiftIso a).symm.app X)
    (t.GE_shift n a n' h (S.ι.obj X) hX)
  zero' {X Y} f hX hY := S.ι.map_injective (by
    rw [Functor.map_zero]
    exact t.zero' (S.ι.map f) hX hY)
  LE_zero_le X hX := t.LE_zero_le _ hX
  GE_one_le X hX := t.GE_one_le _ hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT, ⟨X', ⟨e⟩⟩, ⟨Y', ⟨e'⟩⟩⟩ :=
      h.exists_triangle_zero_one A.1 A.2
    refine ⟨X', Y', prop_of_iso (t.LE 0) e.symm hX, prop_of_iso (t.GE 1) e'.symm hY,
      S.ι.preimage (e.hom ≫ f), S.ι.preimage (g ≫ e'.inv),
      S.ι.preimage (e'.hom ≫ h ≫ e.inv⟦(1 : ℤ)⟧' ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app X'),
      isomorphic_distinguished _ hT _ ?_⟩
    refine Triangle.isoMk _ _ e (Iso.refl _) e' ?_ ?_ ?_
    · dsimp
      simp
    · dsimp
      simp
    · dsimp
      simp

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
