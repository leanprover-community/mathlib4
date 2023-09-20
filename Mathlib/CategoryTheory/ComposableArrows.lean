import Mathlib.AlgebraicTopology.SimplexCategory

namespace CategoryTheory

open Category

variable (C : Type*) [Category C]

abbrev ComposableArrows (n : ℕ) := Fin (n + 1) ⥤ C

namespace ComposableArrows

variable {C} {n : ℕ}

variable (F : ComposableArrows C n)

@[simp]
abbrev obj' (i : ℕ) (hi : i ≤ n := by linarith) : C := F.obj ⟨i, by linarith⟩

@[simp]
abbrev map' (i j : ℕ) (hij : i ≤ j := by linarith) (hjn : j ≤ n := by linarith) :
  F.obj ⟨i, by linarith⟩ ⟶ F.obj ⟨j, by linarith⟩ := F.map (homOfLE (by
    simp only [Fin.mk_le_mk]
    linarith))

variable {F}

@[simp]
abbrev app' {G : ComposableArrows C n} (φ : F ⟶ G) (i : ℕ) (hi : i ≤ n := by linarith) :
    F.obj' i ⟶ G.obj' i := φ.app _

variable (F)

variable {X : C} (f : X ⟶ F.obj' 0)

namespace Precomp

variable (X)

def obj : Fin (n + 1 + 1) → C
  | ⟨0, _⟩ => X
  | ⟨i + 1, hi⟩ => F.obj' i

variable {X}

def map : ∀ (i j : Fin (n + 1 + 1)) (_ : i ≤ j), obj F X i ⟶ obj F X j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 X
  | ⟨0, _⟩, ⟨j+1, hj⟩, _ => f ≫ F.map' 0 j
  | ⟨i+1, hi⟩, ⟨j+1, hj⟩, hij => F.map' i j (by simpa using hij)

@[simp]
lemma map_zero_zero : map F f 0 0 (by simp) = 𝟙 X := rfl

@[simp]
lemma map_one_one : map F f 1 1 (by simp) = F.map (𝟙 _) := rfl

@[simp]
lemma map_zero_one : map F f 0 1 (by simp) = f ≫ F.map (𝟙 _) := rfl

@[simp]
lemma map_zero_succ (j : ℕ) (hj : j + 1 < n + 1 + 1) :
    map F f 0 ⟨j+1, hj⟩ (by simp) = f ≫ F.map' 0 j := rfl

@[simp]
lemma map_succ_succ (i j : ℕ) (hi : i + 1 < n + 1 + 1) (hj : j + 1 < n + 1 + 1) (hij : i + 1 ≤ j + 1) :
    map F f ⟨i + 1, hi⟩ ⟨j+1, hj⟩ hij = F.map' i j := rfl

@[simp]
lemma map_one_succ (j : ℕ) (hj : j + 1 < n + 1 + 1) :
    map F f 1 ⟨j + 1, hj⟩ (by simp [Fin.le_def]) = F.map' 0 j := rfl

lemma map_id (i : Fin (n + 1 + 1)) : map F f i i (by simp) = 𝟙 _ := by
  obtain ⟨i, hi⟩ := i
  cases i
  · rfl
  · apply F.map_id

lemma map_comp {i j k : Fin (n + 1 + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    map F f i k (hij.trans hjk) = map F f i j hij ≫ map F f j k hjk := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain ⟨k, hk⟩ := k
  cases i
  · obtain _ | j := j
    · dsimp
      erw [id_comp]
    · obtain _ | k := k
      · simp [Fin.ext_iff] at hjk
      · dsimp
        change f ≫ F.map _ = (f ≫ F.map _) ≫ F.map _
        rw [assoc, ← F.map_comp, homOfLE_comp]
  · obtain _ | j := j
    · simp [Fin.ext_iff] at hij
    · obtain _ | k := k
      · simp [Fin.ext_iff] at hjk
      · change F.map _ = F.map _ ≫ F.map _
        rw [← F.map_comp, homOfLE_comp]

end Precomp

@[simps]
def precomp : ComposableArrows C (n + 1) where
  obj := Precomp.obj F X
  map g := Precomp.map F f _ _ (leOfHom g)
  map_id := Precomp.map_id F f
  map_comp g g' := (Precomp.map_comp F f (leOfHom g) (leOfHom g'))

@[simps!]
def mk₀ (X : C) : ComposableArrows C 0 := (Functor.const (Fin 1)).obj X

@[simps]
def homMk₀ (X Y : ComposableArrows C 0) (φ : X.obj' 0 ⟶ Y.obj' 0) : X ⟶ Y where
  app := fun ⟨0, _⟩  => φ
  naturality := fun ⟨0, _⟩ ⟨0, _⟩ _ => by
    erw [X.map_id, Y.map_id, id_comp, comp_id]

@[simps]
def isoMk₀ (X Y : ComposableArrows C 0) (φ : X.obj' 0 ≅ Y.obj' 0) : X ≅ Y where
  hom := homMk₀ _ _ φ.hom
  inv := homMk₀ _ _ φ.inv

@[ext]
lemma hom_ext₀ {X Y : ComposableArrows C 0} (f g : X ⟶ Y) (h : app' f 0 = app' g 0) : f = g := by
  apply NatTrans.ext
  ext1 x
  match x with
    | 0 => exact h

namespace Mk₁

variable (X₀ X₁ : C) (f : X₀ ⟶ X₁)

@[simp]
def obj : Fin 2 → C
  | ⟨0, _⟩ => X₀
  | ⟨1, _⟩  => X₁

variable {X₀ X₁}

@[simp]
def map : ∀ (i j : Fin 2) (_ : i ≤ j), obj X₀ X₁ i ⟶ obj X₀ X₁ j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩, _ => f
  | ⟨1, _⟩, ⟨1, _⟩, _ => 𝟙 _

lemma map_id (i : Fin 2) : map f i i (by simp) = 𝟙 _ :=
  match i with
    | 0 => rfl
    | 1 => rfl

lemma _root_.Fin.eq_one_of_neq_zero (i : Fin 2) (hi : i ≠ 0) : i = 1 :=
  match i with
    | 0 => by simp at hi
    | 1 => rfl

lemma map_comp {i j k : Fin 2} (hij : i ≤ j) (hjk : j ≤ k) :
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk :=
  match i with
    | 0 =>
        match j with
          | 0 => by rw [map_id, id_comp]
          | 1 => by
              obtain rfl : k = 1 := k.eq_one_of_neq_zero (by rintro rfl; simp at hjk)
              rw [map_id, comp_id]
    | 1 => by
        obtain rfl := j.eq_one_of_neq_zero (by rintro rfl; simp at hij)
        obtain rfl := k.eq_one_of_neq_zero (by rintro rfl; simp at hjk)
        rw [map_id, id_comp]

end Mk₁

@[simps]
def mk₁ {X₀ X₁ : C} (f : X₀ ⟶ X₁) : ComposableArrows C 1 where
  obj := Mk₁.obj X₀ X₁
  map g := Mk₁.map f _ _ (leOfHom g)
  map_id := Mk₁.map_id f
  map_comp g g' := Mk₁.map_comp f (leOfHom g) (leOfHom g')

@[simps]
def homMk₁ (f g : ComposableArrows C 1) (left : f.obj' 0 ⟶ g.obj' 0) (right : f.obj' 1 ⟶ g.obj' 1)
    (w : f.map' 0 1 ≫ right = left ≫ g.map' 0 1) :
    f ⟶ g where
  app i :=
    match i with
      | ⟨0, _⟩ => left
      | ⟨1, _⟩ => right
  naturality {i j} hij := by
    replace hij := leOfHom hij
    match i with
      | ⟨0, _⟩ =>
          match j with
            | ⟨0, _⟩ =>
                dsimp
                erw [f.map_id, g.map_id, id_comp, comp_id]
            | ⟨1, _⟩ => exact w
      | ⟨1, _⟩  =>
          obtain rfl : j = ⟨1, _⟩ := j.eq_one_of_neq_zero (by rintro rfl; simp at hij)
          dsimp
          erw [f.map_id, g.map_id, id_comp, comp_id]

@[ext]
lemma hom_ext₁ {f g : ComposableArrows C 1} (φ φ' : f ⟶ g)
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
    φ = φ' := by
  apply NatTrans.ext
  ext i
  match i with
    | 0 => exact h₀
    | 1 => exact h₁

@[simps]
def isoMk₁ (f g : ComposableArrows C 1) (left : f.obj' 0 ≅ g.obj' 0) (right : f.obj' 1 ≅ g.obj' 1)
    (w : f.map' 0 1 ≫ right.hom = left.hom ≫ g.map' 0 1) :
    f ≅ g where
  hom := homMk₁ _ _ left.hom right.hom w
  inv := homMk₁ _ _ left.inv right.inv (by
    rw [← cancel_mono right.hom, assoc, assoc, w, right.inv_hom_id, left.inv_hom_id_assoc]
    dsimp
    erw [comp_id])

@[simp]
def mk₂ {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) : ComposableArrows C 2 :=
  (mk₁ g).precomp f

@[simp]
def mk₃ {X₀ X₁ X₂ X₃ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) : ComposableArrows C 3 :=
  (mk₂ g h).precomp f

@[simp]
def mk₄ {X₀ X₁ X₂ X₃ X₄ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) : ComposableArrows C 4 :=
  (mk₃ g h i).precomp f

@[simp]
def mk₅ {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) : ComposableArrows C 5 :=
  (mk₄ g h i j).precomp f

@[simp]
def mk₆ {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) (k : X₅ ⟶ X₆) :
    ComposableArrows C 6 :=
  (mk₅ g h i j k ).precomp f

@[simp]
def mk₇ {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) (k : X₅ ⟶ X₆) (l : X₆ ⟶ X₇) :
    ComposableArrows C 7 :=
  (mk₆ g h i j k l).precomp f

example {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) (k : X₅ ⟶ X₆) (l : X₆ ⟶ X₇) :
    (mk₇ f g h i j k l).map' 1 3 = g ≫ h ≫ 𝟙 _ := by dsimp

end ComposableArrows

@[simps]
def composableArrowsZeroEquivalence : ComposableArrows C 0 ≌ C where
  functor :=
    { obj := fun f => f.obj' 0
      map := fun f => ComposableArrows.app' f 0 }
  inverse :=
    { obj := fun X => ComposableArrows.mk₀ X
      map := fun f => ComposableArrows.homMk₀ _ _ f }
  unitIso := NatIso.ofComponents (fun X => ComposableArrows.isoMk₀ _ _ (Iso.refl _))
    (by aesop_cat)
  counitIso := Iso.refl _

set_option maxHeartbeats 600000 in
@[simps]
def composableArrowsOneEquivalence : ComposableArrows C 1 ≌ Arrow C where
  functor :=
    { obj := fun F => Arrow.mk (F.map' 0 1)
      map := fun {F G} f =>
        { left := ComposableArrows.app' f 0
          right := ComposableArrows.app' f 1
          w := (f.naturality _).symm } }
  inverse :=
    { obj := fun f => ComposableArrows.mk₁ f.hom
      map := fun {f g} φ => ComposableArrows.homMk₁ _ _ φ.left φ.right φ.w.symm }
  unitIso := NatIso.ofComponents
    (fun f => ComposableArrows.isoMk₁ _ _ (Iso.refl _) (Iso.refl _) (by aesop_cat))
      (by aesop_cat)
  counitIso := Iso.refl _

end CategoryTheory
