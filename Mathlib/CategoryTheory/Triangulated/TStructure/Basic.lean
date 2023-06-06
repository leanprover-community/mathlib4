import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.RespectsIso
import Mathlib.Tactic.Linarith

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

lemma setLE_monotone (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) : t.setLE n₀ ⊆ t.setLE n₁ := by
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

class IsLE (X : C) (n : ℤ) : Prop where
  mem : X ∈ t.setLE n

lemma mem_of_isLE (X : C) (n : ℤ) [t.IsLE X n] : X ∈ t.setLE n := IsLE.mem

class IsGE (X : C) (n : ℤ) : Prop where
  mem : X ∈ t.setGE n

lemma mem_of_isGE (X : C) (n : ℤ) [t.IsGE X n] : X ∈ t.setGE n := IsGE.mem

lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsLE X n] : t.IsLE Y n where
  mem := (t.setLE n).mem_of_iso e (t.mem_of_isLE X n)

lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsGE X n] : t.IsGE Y n where
  mem := (t.setGE n).mem_of_iso e (t.mem_of_isGE X n)

lemma isLE_of_LE (X : C) (p q : ℤ) (hpq : p ≤ q) [t.IsLE X p] : t.IsLE X q where
  mem := setLE_monotone t p q hpq (t.mem_of_isLE X p)

lemma isGE_of_GE (X : C) (p q : ℤ) (hpq : p ≤ q) [t.IsGE X q] : t.IsGE X p where
  mem := setGE_antitone t p q hpq (t.mem_of_isGE X q)

lemma isLE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsLE X n] :
    t.IsLE (X⟦a⟧) n' :=
  ⟨t.shift_mem_setLE n a n' hn' X (t.mem_of_isLE X n)⟩

lemma isGE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsGE X n] :
    t.IsGE (X⟦a⟧) n' :=
  ⟨t.shift_mem_setGE n a n' hn' X (t.mem_of_isGE X n)⟩

lemma isLE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsLE (X⟦a⟧) n'] :
    t.IsLE X n := by
  have h := t.isLE_shift (X⟦a⟧) n' (-a) n (by linarith)
  exact t.isLE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

lemma isGE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsGE (X⟦a⟧) n'] :
    t.IsGE X n := by
  have h := t.isGE_shift (X⟦a⟧) n' (-a) n (by linarith)
  exact t.isGE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [t.IsLE X n₀] [t.IsGE Y n₁] : f = 0 := by
  have := t.isLE_shift X n₀ n₀ 0 (add_zero n₀)
  have := t.isGE_shift Y n₁ n₀ (n₁-n₀) (by linarith)
  have := t.isGE_of_GE (Y⟦n₀⟧) 1 (n₁-n₀) (by linarith)
  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  . apply t.mem_of_isLE
  . apply t.mem_of_isGE

lemma zero_of_isLE_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    (_ : t.IsLE X n₀) (_ : t.IsGE Y n₁) : f = 0 :=
  t.zero f n₀ n₁ h

lemma isZero (X : C) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [t.IsLE X n₀] [t.IsGE X n₁] : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact t.zero _ n₀ n₁ h

def heart : Set C := t.setLE 0 ∩ t.setGE 0

abbrev Heart := FullSubcategory t.heart

abbrev ιHeart : t.Heart ⥤ C := fullSubcategoryInclusion _

lemma mem_heart_iff (X : C) :
    X ∈ t.heart ↔ t.IsLE X 0 ∧ t.IsGE X 0 := by
  constructor
  . rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
  . rintro ⟨h₁, h₂⟩
    exact ⟨t.mem_of_isLE _ _, t.mem_of_isGE _ _⟩

instance (X : t.Heart) : t.IsLE (t.ιHeart.obj X) 0 := ⟨X.2.1⟩
instance (X : t.Heart) : t.IsGE (t.ιHeart.obj X) 0 := ⟨X.2.2⟩

def ιHeartDegree (n : ℤ) : t.Heart ⥤ C :=
  t.ιHeart ⋙ shiftFunctor C (-n)

noncomputable def ιHeartDegreeCompShiftIso (n : ℤ) : t.ιHeartDegree n ⋙ shiftFunctor C n ≅ t.ιHeart :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (shiftFunctorCompIsoId C (-n) n (add_left_neg n)) ≪≫
    Functor.rightUnitor _

end TStructure

end Triangulated

end CategoryTheory
