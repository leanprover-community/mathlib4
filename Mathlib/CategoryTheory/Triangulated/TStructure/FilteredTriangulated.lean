import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Shift.Predicate

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

attribute [local instance] endofunctorMonoidalCategory

variable {C D : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

variable (C)

structure FilteredTriangulated where
  s : MonoidalFunctor (Discrete ℤ) (C ⥤ C)
  s_commshift : ∀ (n : ℤ), (s.obj {as := n}).CommShift ℤ
  s_triang : ∀ (n : ℤ), (s.obj {as := n}).IsTriangulated
  α : 𝟭 C ⟶ s.obj {as := 1}
  LE : ℤ → Triangulated.Subcategory C
  GE : ℤ → Triangulated.Subcategory C
  LE_closedUnderIsomorphisms : ∀ (n : ℤ), ClosedUnderIsomorphisms (LE n).P
  GE_closedUnderIsomorphisms : ∀ (n : ℤ), ClosedUnderIsomorphisms (GE n).P
  LE_zero_le : (LE 0).P ≤ (LE 1).P
  GE_one_le : (GE 1).P ≤ (GE 0).P
  LE_shift : ∀ (n a n' : ℤ), a + n = n' → ∀ (X : C), (LE n).P X → (LE n').P
    ((s.obj {as := a}).obj X)
  GE_shift : ∀ (n a n' : ℤ), a + n = n' → ∀ (X : C), (GE n).P X → (GE n').P
    ((s.obj {as := a}).obj X)
  zero' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (GE 1).P X → (LE 0).P Y → f = 0
  adj_left : ∀ ⦃X Y : C⦄, (GE 1).P X → (LE 0).P Y → Function.Bijective
    (fun (f : (s.obj {as := 1}).obj Y ⟶ X) ↦ (α.app Y ≫ f : Y ⟶ X))
  adj_right : ∀ ⦃X Y : C⦄, (GE 1).P X → (LE 0).P Y → Function.Bijective
    (fun (f : Y ⟶ X) ↦ (f ≫ α.app X: Y ⟶ (s.obj {as := 1}).obj X))
  LE_exhaustive : ∀ (X : C), ∃ (n : ℤ), (LE n).P X
  GE_exhaustive : ∀ (X : C), ∃ (n : ℤ), (GE n).P X
  α_s : ∀ (X : C), (s.obj {as := 1}).map (α.app X) = α.app ((s.obj {as := 1}).obj X)
  exists_triangle_one_zero : ∀ (X : C), ∃ (A : C) (B : C) (_ : (GE 1).P A) (_ : (LE 0).P B)
    (f : A ⟶ X) (g : X ⟶ B) (h : B ⟶ A⟦1⟧),
    Triangle.mk f g h ∈ distinguishedTriangles

namespace FilteredTriangulated

attribute [instance] LE_closedUnderIsomorphisms GE_closedUnderIsomorphisms

variable {C}
variable (F : FilteredTriangulated C)

lemma exists_triangle (A : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∃ (X Y : C) (_ : (F.GE n₁).P X) (_ : (F.LE n₀).P Y) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := F.exists_triangle_one_zero ((F.s.obj {as := -n₀}).obj A)
  let T := (@Functor.mapTriangle _ _ _ _ _ _ (F.s.obj {as := n₀}) (F.s_commshift n₀)).obj
    (Triangle.mk f g h)
  let e := (@shiftEquiv' C _ _ _ {shift := F.s} (-n₀) n₀ (by rw [add_left_neg])).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
    refine isomorphic_distinguished _ (@Functor.IsTriangulated.map_distinguished _ _ _ _ _ _
      (F.s.obj {as := n₀}) (F.s_commshift n₀) _ _ _ _ _ _ _ _ (F.s_triang n₀) _ mem) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    all_goals dsimp; simp [T]
  exact ⟨_, _, F.GE_shift _ _ _ (by omega) _ hX,
      F.LE_shift _ _ _ (by omega) _ hY, _, _, _, hT'⟩

lemma predicateShift_LE (n n' a : ℤ) (hn' : n = n') :
    (PredicateShift (F.LE n).P a) = (F.LE n').P := by
  ext X
  simp only [PredicateShift, Triangulated.Subcategory.shift_iff, hn']

lemma predicateShift_GE (a n n' : ℤ) (hn' : n = n') :
    (PredicateShift (F.GE n).P a) = (F.GE n').P := by
  ext X
  simp only [PredicateShift, hn', Triangulated.Subcategory.shift_iff]

lemma LE_monotone : Monotone (fun n ↦ (F.LE n).P) := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), (F.LE n).P ≤ (F.LE (n + a)).P
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX =>
    (F.LE_closedUnderIsomorphisms (n + 1)).of_iso ((@shiftEquiv' C _ _ _ {shift := F.s}
    (-n) n (by rw [add_left_neg])).unitIso.symm.app X) (F.LE_shift 1 n (n + 1) rfl _
    (F.LE_zero_le _ (F.LE_shift n (-n) 0 (by rw [add_left_neg]) X hX)))
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (ha n).trans (hb (n+a))
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

lemma GE_antitone : Antitone (fun n ↦ (F.GE n).P) := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), (F.GE (n + a)).P ≤ (F.GE n).P
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX =>
    (F.GE_closedUnderIsomorphisms n).of_iso ((@shiftEquiv' C _ _ _ {shift := F.s}
    (-n) n (by rw [add_left_neg])).unitIso.symm.app X) (F.GE_shift 0 n n (by rw [add_zero]) _
    (F.GE_one_le _ (F.GE_shift (n + 1) (-n) 1 (by rw [neg_add_cancel_left]) X hX)))
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc ]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

/-- Given a filtration `F` on a pretriangulated category `C`, the property `F.IsLE X n`
holds if `X : C` is `≤ n` for the filtration. -/
class IsLE (X : C) (n : ℤ) : Prop where
  le : (F.LE n).P X

/-- Given a filtration `F` on a pretriangulated category `C`, the property `F.IsGE X n`
holds if `X : C` is `≥ n` for the filtration. -/
class IsGE (X : C) (n : ℤ) : Prop where
  ge : (F.GE n).P X

lemma mem_of_isLE (X : C) (n : ℤ) [F.IsLE X n] : (F.LE n).P X := IsLE.le

lemma mem_of_isGE (X : C) (n : ℤ) [F.IsGE X n] : (F.GE n).P X := IsGE.ge

-- Need to add stuff about these properties defining triangulated subcategories.

end FilteredTriangulated
