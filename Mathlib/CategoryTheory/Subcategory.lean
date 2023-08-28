import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.Data.Set.Image

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

lemma Arrow.eq_iff (φ φ' : Arrow C) : φ = φ' ↔ ∃ (h : φ.left = φ'.left)
        (h' : φ.right = φ'.right), φ.hom = eqToHom h ≫ φ'.hom ≫ eqToHom h'.symm := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, by simp⟩
  · cases φ
    cases φ'
    dsimp
    rintro ⟨rfl, rfl, h⟩
    simp only [h, eqToHom_refl, Category.comp_id, Category.id_comp]

lemma Arrow.mk_eq_iff {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    Arrow.mk f = Arrow.mk g ↔ ∃ (h : X = X') (h' : Y = Y'),
      f = eqToHom h ≫ g ≫ eqToHom h'.symm :=
  Arrow.eq_iff _ _

variable (C)

structure ArrowFamily :=
  J : Type w
  s : J → Arrow C

variable {C}

def ArrowFamily.W (F : ArrowFamily C) : MorphismProperty C :=
  fun _ _ f => Arrow.mk f ∈ Set.range F.s

lemma ArrowFamily.mem_W_iff (F : ArrowFamily C) {X Y : C} (f : X ⟶ Y) :
    F.W f ↔ ∃ (i : F.J), F.s i = Arrow.mk f := by
  dsimp [W]
  simp only [Set.mem_range]

lemma ArrowFamily.mem_W (F : ArrowFamily C) (i : F.J) :
    F.W (F.s i).hom := by
  rw [ArrowFamily.mem_W_iff]
  exact ⟨i, rfl⟩

variable (C)

structure Subcategory where
  F : ArrowFamily.{w} C
  id₁ : ∀ (i : F.J), F.W (𝟙 (F.s i).left)
  id₂ : ∀ (i : F.J), F.W (𝟙 (F.s i).right)
  comp' : F.W.StableUnderComposition

namespace Subcategory

variable {C}

variable (S : Subcategory C)

@[pp_dot]
def objSet : Set C :=
  fun X => ∃ (i : S.F.J), X = (S.F.s i).left

@[pp_dot]
def obj : Type u := S.objSet

@[pp_dot]
def homSet (X Y : S.obj) : Set (X.1 ⟶ Y.1) := fun f => ∃ (i : S.F.J), S.F.s i = Arrow.mk f

@[simp]
lemma mem_homSet_iff {X Y : S.obj} (f : X.1 ⟶ Y.1) :
    f ∈ S.homSet X Y ↔ ∃ (i : S.F.J), S.F.s i = Arrow.mk f := by rfl

@[pp_dot]
def hom (X Y : S.obj) : Type v := S.homSet X Y

lemma hom_ext {X Y : S.obj} (f g : S.hom X Y) (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simps, pp_dot]
def id (X : S.obj) : S.hom X X := ⟨𝟙 _, by
  obtain ⟨i, hi⟩ := X.2
  · simp only [mem_homSet_iff]
    obtain ⟨j, hj⟩ := S.id₁ i
    exact ⟨j, by convert hj⟩⟩

@[simps, pp_dot]
def comp {X Y Z : S.obj} (f : S.hom X Y) (g : S.hom Y Z) : S.hom X Z :=
  ⟨f.1 ≫ g.1, S.comp' _ _ f.2 g.2⟩

instance : Category S.obj where
  Hom X Y := S.hom X Y
  id := S.id
  comp := S.comp
  id_comp _ := S.hom_ext _ _ (by aesop_cat)
  comp_id _ := S.hom_ext _ _ (by aesop_cat)
  assoc _ _ _ := S.hom_ext _ _ (by aesop_cat)

def S.ι : S.obj ⥤ C where
  obj X := X.1
  map φ := φ.1

instance : Small.{w} S.obj := by
  let π : S.F.J → S.obj := fun i => ⟨(S.F.s i).left, ⟨i, rfl⟩⟩
  have : Function.Surjective π := fun X => by
    obtain ⟨i, hi⟩ := X.2
    exact ⟨i, Subtype.ext hi.symm⟩
  exact small_of_surjective this

instance : Small.{w} (Skeleton S.obj) := by
  have : Function.Injective (fromSkeleton S.obj).obj := fun _ _ h => by simpa using h
  exact small_of_injective this

instance : LocallySmall.{w} S.obj := ⟨fun X Y => by
  let Z : Set S.F.J := fun i => X.1 = (S.F.s i).left ∧ Y.1 = (S.F.s i).right
  let π : Z → S.hom X Y := fun i => by
    refine' ⟨eqToHom i.2.1 ≫ (S.F.s i).hom ≫ eqToHom i.2.2.symm, ⟨i, _⟩ ⟩
    rw [Arrow.eq_iff]
    exact ⟨i.2.1.symm, i.2.2.symm, by simp⟩
  have : Function.Surjective π := fun f => by
    obtain ⟨i, hi⟩ := f.2
    rw [Arrow.eq_iff] at hi
    obtain ⟨h₁, h₂, hi⟩ := hi
    dsimp at h₁ h₂
    exact ⟨⟨i, ⟨h₁.symm, h₂.symm⟩⟩, Subtype.ext (by simp [hi])⟩
  exact small_of_surjective this⟩

instance : EssentiallySmall.{w} S.obj := by
  rw [essentiallySmall_iff]
  constructor <;> infer_instance

end Subcategory

namespace ArrowFamily

variable {C}
variable (F : ArrowFamily.{w} C)

inductive selfCompJ : Type w
  | id₁ (j : F.J)
  | id₂ (j : F.J)
  | mk (j : F.J)
  | comp (j₁ j₂ : F.J) (h : (F.s j₁).right = (F.s j₂).left)

def selfCompArrows : F.selfCompJ → Arrow C
  | selfCompJ.id₁ j => Arrow.mk (𝟙 (F.s j).left)
  | selfCompJ.id₂ j => Arrow.mk (𝟙 (F.s j).right)
  | selfCompJ.mk j => F.s j
  | selfCompJ.comp j₁ j₂ h => Arrow.mk ((F.s j₁).hom ≫ eqToHom h ≫ (F.s j₂).hom)

def selfComp (F : ArrowFamily C) : ArrowFamily C where
  J := F.selfCompJ
  s := F.selfCompArrows

lemma selfComp_W_le : F.W ≤ F.selfComp.W := fun X Y f hf => by
  rw [ArrowFamily.mem_W_iff] at hf
  obtain ⟨i, hi⟩ := hf
  exact ⟨selfCompJ.mk i, by simp only [← hi]; rfl⟩

def selfCompIter (F : ArrowFamily C) : ℕ → ArrowFamily C
  | 0 => F
  | n+1 => (selfCompIter F n).selfComp

lemma SelfCompIterMonotone (F : ArrowFamily C) (i j : ℕ) (hij : i ≤ j) :
    (F.selfCompIter i).W ≤ (F.selfCompIter j).W := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  revert i
  induction' k with k hk
  · intro i
    simp
  · intro i _
    simp only [Nat.succ_eq_add_one, ← add_assoc]
    exact (hk i (by simp)).trans (selfComp_W_le _)

def compClosure : ArrowFamily.{w} C where
  J := Sigma (fun n => (F.selfCompIter n).J)
  s := fun ⟨_, j⟩ => ArrowFamily.s _ j

lemma mem_compClosureW_iff {X Y : C} (f : X ⟶ Y) :
    F.compClosure.W f ↔ ∃ (n : ℕ), (F.selfCompIter n).W f := by
  simp only [ArrowFamily.mem_W_iff]
  constructor
  · rintro ⟨⟨n, i⟩, hi⟩
    exact ⟨n, i, hi⟩
  · rintro ⟨n, i, hi⟩
    exact ⟨⟨n, i⟩, hi⟩

end ArrowFamily

def Subcategory.compClosure (F : ArrowFamily.{w} C) : Subcategory C where
  F := F.compClosure
  id₁ := fun ⟨n, i⟩ => by
    rw [ArrowFamily.mem_compClosureW_iff]
    refine' ⟨n+1, _⟩
    unfold ArrowFamily.selfCompIter
    simp only [Nat.add_eq, add_zero]
    exact (F.selfCompIter n).selfComp.mem_W (ArrowFamily.selfCompJ.id₁ i)
  id₂ := fun ⟨n, i⟩ => by
    rw [ArrowFamily.mem_compClosureW_iff]
    refine' ⟨n+1, _⟩
    unfold ArrowFamily.selfCompIter
    simp only [Nat.add_eq, add_zero]
    exact (F.selfCompIter n).selfComp.mem_W (ArrowFamily.selfCompJ.id₂ i)
  comp' := fun X Y Z f g hf hg => by
    rw [ArrowFamily.mem_compClosureW_iff]
    obtain ⟨n, hf', hg'⟩ : ∃ (n : ℕ), (F.selfCompIter n).W f ∧ (F.selfCompIter n).W g := by
      rw [ArrowFamily.mem_compClosureW_iff] at hf hg
      obtain ⟨n₁, hf⟩ := hf
      obtain ⟨n₂, hg⟩ := hg
      exact ⟨max n₁ n₂,
        F.SelfCompIterMonotone _ _ (le_max_left _ _) _ _ _ hf,
        F.SelfCompIterMonotone _ _ (le_max_right _ _) _ _ _ hg⟩
    rw [ArrowFamily.mem_W_iff] at hf' hg'
    obtain ⟨i, hi⟩ := hf'
    obtain ⟨j, hj⟩ := hg'
    refine' ⟨n+1, _⟩
    unfold ArrowFamily.selfCompIter
    simp only [Nat.add_eq, add_zero]
    rw [ArrowFamily.mem_W_iff]
    rw [Arrow.eq_iff] at hi hj
    obtain ⟨h₁, h₂, hi⟩ := hi
    obtain ⟨h₃, h₄, hj⟩ := hj
    refine' ⟨ArrowFamily.selfCompJ.comp i j (h₂.trans h₃.symm), _⟩
    dsimp [ArrowFamily.selfCompArrows, ArrowFamily.selfComp]
    rw [Arrow.eq_iff]
    exact ⟨h₁, h₄, by simp [hi, hj]⟩

end CategoryTheory
