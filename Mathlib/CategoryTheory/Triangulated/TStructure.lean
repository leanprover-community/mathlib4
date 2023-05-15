import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.RespectsIso
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch

open CategoryTheory Category Limits

namespace Set

variable {C : Type _} [Category C] (S : Set C)

variable {A : Type _} [AddMonoid A] [HasShift C A]

def shift (a : A) : Set C := fun X => (X⟦a⟧ ∈ S)

lemma mem_shift_iff (a : A) (X : C) : X ∈ S.shift a ↔ X⟦a⟧ ∈ S := by rfl

lemma shift_respectsIso (a : A) [S.RespectsIso] : (S.shift a).RespectsIso where
  condition {X Y} e hX := by
    simp only [mem_shift_iff] at hX ⊢
    exact mem_of_iso S ((shiftFunctor C a).mapIso e) hX

variable (A)

@[simp]
lemma shift_zero [S.RespectsIso] : S.shift (0 : A) = S := by
  ext X
  simp only [mem_shift_iff]
  exact mem_iff_of_iso S ((shiftFunctorZero C A).app X)

variable {A}

lemma shift_shift (a b c : A) (h : a + b = c) [S.RespectsIso] :
    (S.shift b).shift a = S.shift c := by
  ext X
  simp only [mem_shift_iff]
  exact mem_iff_of_iso _ ((shiftFunctorAdd' C a b c h).symm.app X)

end Set

namespace CategoryTheory

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    --[IsTriangulated C]

open Pretriangulated

namespace Triangulated

structure TStructure where
  setLE (n : ℤ) : Set C
  setGE (n : ℤ) : Set C
  setLE_respectsIso (n : ℤ) : (setLE n).RespectsIso
  setGE_respectsIso (n : ℤ) : (setGE n).RespectsIso
  shift_mem_setLE (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : X ∈ setLE n) : X⟦a⟧ ∈ setLE n'
  shift_mem_setGE (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : X ∈ setGE n) : X⟦a⟧ ∈ setGE n'
  zero' ⦃X Y : C⦄ (f : X ⟶ Y) (hX : X ∈ setLE 0) (hY : Y ∈ setGE 1) : f = 0
  setLE_zero_subset : setLE 0 ⊆ setLE 1
  setGE_one_subset : setGE 1 ⊆ setGE 0
  exists_triangle_zero_one (A : C) : ∃ (X Y : C) (_ : X ∈ setLE 0) (_ : Y ∈ setGE 1)
    (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C

namespace TStructure

attribute [instance] setLE_respectsIso setGE_respectsIso

noncomputable def mk' (setLEZero : Set C) (setGEZero : Set C)
    [setLEZero.RespectsIso] [setGEZero.RespectsIso]
    (zero : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), X ∈ setLEZero → Y⟦(1 : ℤ)⟧ ∈ setGEZero → f = 0)
    (setLE_zero_subset' : setLEZero ⊆ setLEZero.shift (1 : ℤ))
    (setGE_zero_subset' : setGEZero.shift (1 : ℤ) ⊆ setGEZero)
    (exists_triangle_zero_one' : ∀ (A : C), ∃ (X Y : C) (_ : X ∈ setLEZero)
      (_ : Y⟦(1 : ℤ)⟧ ∈ setGEZero) (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C) :
    TStructure C where
  setLE n := setLEZero.shift n
  setGE n := setGEZero.shift n
  setLE_respectsIso n := Set.shift_respectsIso _ _
  setGE_respectsIso n := Set.shift_respectsIso _ _
  shift_mem_setLE := by
    rintro n a n' h X hX
    simpa only [← setLEZero.shift_shift _ _ _ h] using hX
  shift_mem_setGE := by
    rintro n a n' h X hX
    simpa only [← setGEZero.shift_shift _ _ _ h] using hX
  zero' := fun X Y f hX hY => zero f (by simpa only [Set.shift_zero] using hX) hY
  setLE_zero_subset := by simpa only [Set.shift_zero] using setLE_zero_subset'
  setGE_one_subset := by simpa only [Set.shift_zero] using setGE_zero_subset'
  exists_triangle_zero_one := by simpa only [Set.shift_zero] using exists_triangle_zero_one'

variable {C}
variable (t : TStructure C)

lemma exists_triangle (A : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∃ (X Y : C) (_ : X ∈ t.setLE n₀) (_ : Y ∈ t.setGE n₁) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := t.exists_triangle_zero_one (A⟦n₀⟧)
  let T := (Triangle.shiftFunctor C (-n₀)).obj (Triangle.mk f g h)
  have e := (shiftEquiv C n₀).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
    refine' isomorphic_distinguished _ (shift_distinguished _ mem (-n₀)) _ _
    refine' Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) _ _ _
    all_goals dsimp ; simp
  exact ⟨_, _, t.shift_mem_setLE _ _ _ (neg_add_self n₀) _ hX,
    t.shift_mem_setGE _ _ _ (by linarith) _ hY, _, _, _, hT'⟩

lemma shift_setLE (a n n' : ℤ) (hn' : a + n = n'): ((t.setLE n).shift a) = t.setLE n' := by
  ext X
  constructor
  . intro hX
    rw [Set.mem_shift_iff] at hX
    apply ((setLE t n').mem_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.shift_mem_setLE n (-a) n' (by linarith) _ hX)
  . intro hX
    exact t.shift_mem_setLE _ _ _ hn' X hX

lemma shift_setGE (a n n' : ℤ) (hn' : a + n = n'): ((t.setGE n).shift a) = t.setGE n' := by
  ext X
  constructor
  . intro hX
    rw [Set.mem_shift_iff] at hX
    apply ((setGE t n').mem_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.shift_mem_setGE n (-a) n' (by linarith) _ hX)
  . intro hX
    exact t.shift_mem_setGE _ _ _ hn' X hX

lemma setLE_antitone (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) : t.setLE n₀ ⊆ t.setLE n₁ := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.setLE n ⊆ t.setLE (n + a)
  suffices ∀ (a : ℕ), H a by
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by linarith
    apply this
  clear n₀ n₁ h
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_setLE n 1 (n+(1 : ℕ)) rfl, Set.mem_shift_iff]
    rw [← t.shift_setLE n 0 n (add_zero n), Set.mem_shift_iff] at hX
    exact t.setLE_zero_subset hX
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (ha n).trans (hb (n+a))
  intro a
  induction' a with a ha
  . exact H_zero
  . exact H_add a 1 _ rfl ha H_one

lemma setGE_antitone (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) : t.setGE n₁ ⊆ t.setGE n₀ := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.setGE (n + a) ⊆ t.setGE n
  suffices ∀ (a : ℕ), H a by
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by linarith
    apply this
  clear n₀ n₁ h
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_setGE n 1 (n + (1 : ℕ)) (by simp), Set.mem_shift_iff] at hX
    rw [← t.shift_setGE n 0 n (add_zero n)]
    exact t.setGE_one_subset hX
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc ]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction' a with a ha
  . exact H_zero
  . exact H_add a 1 _ rfl ha H_one

lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    (hX : X ∈ t.setLE n₀) (hY : Y ∈ t.setGE n₁) : f = 0 := by
  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  . exact t.shift_mem_setLE n₀ n₀ 0 (add_zero n₀) _ hX
  . rw [← Set.mem_shift_iff, t.shift_setGE n₀ 1 (n₀ + 1) rfl]
    exact t.setGE_antitone (n₀ + 1) n₁ (by simpa only [Int.add_one_le_iff] using h) hY

end TStructure

end Triangulated

end CategoryTheory
