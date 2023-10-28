import Mathlib.AlgebraicTopology.Nerve
import Mathlib.Tactic.FinCases

namespace CategoryTheory

open Category

lemma Functor.ext_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (hobj : ∀ X, F.obj X = G.obj X)
    (happ : ∀ X, e.hom.app X = eqToHom (hobj X)) : F = G :=
  Functor.ext hobj (fun X Y f => by
    rw [← cancel_mono (e.hom.app Y), e.hom.naturality f, happ, happ, assoc, assoc,
      eqToHom_trans, eqToHom_refl, comp_id])

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

lemma map'_self (i : ℕ) (hi : i ≤ n := by linarith) :
    F.map' i i = 𝟙 _ := F.map_id _

lemma map'_comp (i j k : ℕ) (hij : i ≤ j := by linarith)
    (hjk : j ≤ k := by linarith) (hk : k ≤ n := by linarith) :
    F.map' i k = F.map' i j ≫ F.map' j k :=
  F.map_comp _ _

abbrev left := obj' F 0
abbrev right := obj' F n
abbrev hom : F.left ⟶ F.right := map' F 0 n

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

@[simp]
lemma obj_zero : obj F X 0 = X := rfl

@[simp]
lemma obj_one : obj F X 1 = F.obj' 0 := rfl

@[simp]
lemma obj_succ (i : ℕ) (hi : i + 1 < n + 1 + 1) : obj F X ⟨i + 1, hi⟩ = F.obj' i := rfl

variable {X}

def map : ∀ (i j : Fin (n + 1 + 1)) (_ : i ≤ j), obj F X i ⟶ obj F X j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 X
  | ⟨0, _⟩, ⟨1, _⟩, _ => f
  | ⟨0, _⟩, ⟨j+2, hj⟩, _ => f ≫ F.map' 0 (j+1)
  | ⟨i+1, hi⟩, ⟨j+1, hj⟩, hij => F.map' i j (by simpa using hij)

@[simp]
lemma map_zero_zero : map F f 0 0 (by simp) = 𝟙 X := rfl

@[simp]
lemma map_one_one : map F f 1 1 (by simp) = F.map (𝟙 _) := rfl

@[simp]
lemma map_zero_one : map F f 0 1 (by simp) = f := rfl

@[simp]
lemma map_zero_one' : map F f 0 ⟨0 + 1, by simp⟩ (by simp) = f := rfl

@[simp]
lemma map_zero_succ_succ (j : ℕ) (hj : j + 2 < n + 1 + 1) :
    map F f 0 ⟨j+2, hj⟩ (by simp) = f ≫ F.map' 0 (j+1) := rfl

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
  · obtain _ | _ | j := j
    · dsimp
      erw [id_comp]
    · obtain _ | _ | k := k
      · simp at hjk
      · dsimp
        erw [F.map_id, comp_id]
      · rfl
    · obtain _ | _ | k := k
      · simp [Fin.ext_iff] at hjk
      · simp [Fin.le_def, Nat.succ_eq_add_one] at hjk
      · dsimp
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
def homMk₀ {X Y : ComposableArrows C 0} (φ : X.obj' 0 ⟶ Y.obj' 0) : X ⟶ Y where
  app := fun ⟨0, _⟩  => φ
  naturality := fun ⟨0, _⟩ ⟨0, _⟩ _ => by
    erw [X.map_id, Y.map_id, id_comp, comp_id]

@[simps]
def isoMk₀ {X Y : ComposableArrows C 0} (φ : X.obj' 0 ≅ Y.obj' 0) : X ≅ Y where
  hom := homMk₀ φ.hom
  inv := homMk₀ φ.inv

@[ext]
lemma hom_ext₀ {X Y : ComposableArrows C 0} {f g : X ⟶ Y} (h : app' f 0 = app' g 0) : f = g := by
  apply NatTrans.ext
  ext1 x
  match x with
    | 0 => exact h

lemma ext₀ {X Y : ComposableArrows C 0} (h : X.left = Y.left) : X = Y :=
  Functor.ext_of_iso (isoMk₀ (eqToIso h))
    (fun i => by fin_cases i; exact h)
    (fun i => by fin_cases i; rfl)

lemma mk₀_surjective (X : ComposableArrows C 0) : ∃ (X₀ : C), X = mk₀ X₀ :=
  ⟨X.left, ext₀ rfl⟩

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
def homMk₁ {f g : ComposableArrows C 1} (left : f.obj' 0 ⟶ g.obj' 0) (right : f.obj' 1 ⟶ g.obj' 1)
    (w : f.map' 0 1 ≫ right = left ≫ g.map' 0 1 := by aesop_cat) :
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
lemma hom_ext₁ {f g : ComposableArrows C 1} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
    φ = φ' := by
  apply NatTrans.ext
  ext i
  match i with
    | 0 => exact h₀
    | 1 => exact h₁

@[simps]
def isoMk₁ {f g : ComposableArrows C 1} (left : f.obj' 0 ≅ g.obj' 0) (right : f.obj' 1 ≅ g.obj' 1)
    (w : f.map' 0 1 ≫ right.hom = left.hom ≫ g.map' 0 1) :
    f ≅ g where
  hom := homMk₁ left.hom right.hom w
  inv := homMk₁ left.inv right.inv (by
    rw [← cancel_mono right.hom, assoc, assoc, w, right.inv_hom_id, left.inv_hom_id_assoc]
    dsimp
    erw [comp_id])

lemma map'_eq_hom₁ (f : ComposableArrows C 1) : f.map' 0 1 = f.hom := rfl

lemma ext₁ {f g : ComposableArrows C 1}
    (left : f.left = g.left) (right : f.right = g.right)
    (w : f.hom = eqToHom left ≫ g.hom ≫ eqToHom right.symm) : f = g :=
  Functor.ext_of_iso (isoMk₁ (eqToIso left) (eqToIso right) (by simp [map'_eq_hom₁, w]))
    (fun i => by
      fin_cases i
      · exact left
      · exact right)
    (fun i => by
      fin_cases i
      all_goals rfl)

lemma mk₁_surjective (X : ComposableArrows C 1) : ∃ (X₀ X₁ : C) (f : X₀ ⟶ X₁), X = mk₁ f :=
  ⟨_, _, X.map' 0 1, ext₁ rfl rfl (by simp)⟩

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
    (mk₇ f g h i j k l).map' 0 7 = f ≫ g ≫ h ≫ i ≫ j ≫ k ≫ l := by dsimp

@[simps]
def _root_.Fin.succFunctor (n : ℕ) : Fin n ⥤ Fin (n + 1) where
  obj i := i.succ
  map {i j} hij := homOfLE (Fin.succ_le_succ_iff.2 (leOfHom hij))

@[simps!]
def δ₀Functor : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  (whiskeringLeft _ _ _).obj (Fin.succFunctor _)

abbrev δ₀ (F : ComposableArrows C (n + 1)) := δ₀Functor.obj F

@[simp]
lemma precomp_δ₀ : (F.precomp f).δ₀ = F := rfl

section

variable {F G : ComposableArrows C (n + 1)}
  (α : F.obj' 0 ⟶ G.obj' 0)
  (β : F.δ₀ ⟶ G.δ₀)
  (w : F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1)

-- somewhat redundant with `homMk`
def homMk' : F ⟶ G where
  app i := match i with
    | ⟨0, _⟩ => α
    | ⟨i+1, hi⟩ => app' β i
  naturality {i j} hij := by
    have hij' := leOfHom hij
    match i with
      | ⟨0, _⟩ =>
          match j with
            | ⟨0, _⟩ => erw [F.map_id, G.map_id, id_comp, comp_id]
            | ⟨j+1, hj⟩ =>
                have hj' : j ≤ n := by linarith
                have hj'' : j < n + 1 := by linarith
                have h₁ : (0 : Fin (n+1+1)) ≤ 1 := Fin.zero_le 1
                have h₂' : (0 : Fin (n+1)) ≤ ⟨j, hj''⟩ := Fin.zero_le _
                have h₂ : (1 : Fin (n+1+1)) ≤ ⟨j+1, hj⟩ := by simp [Fin.le_def]
                obtain rfl : hij = homOfLE (h₁.trans h₂) := rfl
                nth_rewrite 2 [← homOfLE_comp h₁ h₂]
                rw [G.map_comp]
                change _ ≫ app' β j hj' = α ≫ _
                rw [← reassoc_of% w]
                erw [← β.naturality (homOfLE h₂')]
                erw [← Functor.map_comp_assoc]
                rfl
      | ⟨i+1, hi⟩  =>
          match j with
            | ⟨0, _⟩ => simp [Fin.ext_iff] at hij'
            | ⟨j+1, hj⟩ =>
                have h : (⟨i, by linarith⟩ : Fin (n+1)) ≤ ⟨j, by linarith⟩ := by simpa using hij'
                exact β.naturality (homOfLE h)

@[simp]
lemma homMk'_app_zero : (homMk' α β w).app 0 = α := rfl

@[simp]
lemma homMk'_app_succ (i : ℕ) (hi : i + 1 < n + 1 + 1) :
    (homMk' α β w).app ⟨i + 1, hi⟩ = app' β i := rfl

example {X₀ X₁ X₂ X₃ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) : mk₂ f (g ≫ h) ⟶ mk₂ (f ≫ g) h :=
  homMk' (𝟙 _) (homMk₁ g (𝟙 _) (by aesop_cat)) (by aesop_cat)

end

lemma hom_ext_succ {F G : ComposableArrows C (n + 1)} {f g : F ⟶ G}
    (h₀ : app' f 0 = app' g 0) (h₁ : δ₀Functor.map f = δ₀Functor.map g) : f = g := by
  ext ⟨i, hi⟩
  obtain _ | i := i
  · exact h₀
  · rw [Nat.succ_eq_add_one] at hi
    exact congr_app h₁ ⟨i, by linarith⟩

section

@[simps]
def isoMk' {F G : ComposableArrows C (n + 1)} (α : F.obj' 0 ≅ G.obj' 0)
    (β : F.δ₀ ≅ G.δ₀) (w : F.map' 0 1 ≫ app' β.hom 0 = α.hom ≫ G.map' 0 1) : F ≅ G where
  hom := homMk' α.hom β.hom w
  inv := homMk' α.inv β.inv (by
    rw [← cancel_epi α.hom, ← reassoc_of% w, α.hom_inv_id_assoc, β.hom_inv_id_app]
    dsimp
    rw [comp_id])
  hom_inv_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp
  inv_hom_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp

end

@[simps]
def homMk {F G : ComposableArrows C n} (app : ∀ i, F.obj i ⟶ G.obj i)
    (w : ∀ (i : ℕ) (hi : i < n), F.map' i (i+1) ≫ app _ = app _ ≫ G.map' i (i+1)) :
    F ⟶ G where
  app := app
  naturality := by
    suffices ∀ (k i j : ℕ) (hj : i + k = j) (hj' : j ≤ n),
        F.map' i j ≫ app _ = app _ ≫ G.map' i j by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hij' := leOfHom hij
      simp only [Fin.mk_le_mk] at hij'
      obtain ⟨k, hk⟩ := Nat.le.dest hij'
      exact this k i j hk (by linarith)
    intro k
    induction' k with k hk
    · intro i j hj hj'
      simp only [Nat.zero_eq, add_zero] at hj
      obtain rfl := hj
      rw [F.map'_self i, G.map'_self i, id_comp, comp_id]
    · intro i j hj hj'
      rw [Nat.succ_eq_add_one, ← add_assoc] at hj
      subst hj
      rw [F.map'_comp i (i+k) (i+k+1), G.map'_comp i (i+k) (i+k+1), assoc,
        w (i+k) (by linarith), reassoc_of% (hk i (i + k) rfl (by linarith))]

@[simps]
def isoMk {F G : ComposableArrows C n} (app : ∀ i, F.obj i ≅ G.obj i)
    (w : ∀ (i : ℕ) (hi : i < n), F.map' i (i+1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i+1)) :
    F ≅ G where
  hom := homMk (fun i => (app i).hom) w
  inv := homMk (fun i => (app i).inv) (fun i hi => by
    dsimp only
    rw [← cancel_epi ((app _).hom), ← reassoc_of% (w i hi), Iso.hom_inv_id, comp_id,
      Iso.hom_inv_id_assoc])

lemma ext {F G : ComposableArrows C n} (h : ∀ i, F.obj i = G.obj i)
    (w : ∀ (i : ℕ) (hi : i < n), F.map' i (i+1) = eqToHom (h _) ≫ G.map' i (i+1) ≫
      eqToHom (h _).symm) : F = G :=
  Functor.ext_of_iso
    (isoMk (fun i => eqToIso (h i)) (fun i hi => by simp [w i hi])) h (fun i => rfl)

lemma ext' {F G : ComposableArrows C (n + 1)} (h₀ : F.obj' 0 = G.obj' 0)
    (h : F.δ₀ = G.δ₀) (w : F.map' 0 1 = eqToHom h₀ ≫ G.map' 0 1 ≫
      eqToHom (Functor.congr_obj h.symm 0)): F = G := by
  have : ∀ i, F.obj i = G.obj i := by
    intro ⟨i, hi⟩
    cases' i with i
    · exact h₀
    · rw [Nat.succ_eq_add_one] at hi
      exact Functor.congr_obj h ⟨i, by linarith⟩
  exact Functor.ext_of_iso (isoMk' (eqToIso h₀) (eqToIso h) (by
      rw [w]
      dsimp [app']
      erw [eqToHom_app, assoc, assoc, eqToHom_trans, eqToHom_refl, comp_id])) this (by
    rintro ⟨i, hi⟩
    dsimp
    cases' i with i
    · erw [homMk'_app_zero]
    · erw [homMk'_app_succ]
      dsimp [app']
      erw [eqToHom_app])

lemma precomp_surjective (F : ComposableArrows C (n + 1)) :
    ∃ (F₀ : ComposableArrows C n) (X₀ : C) (f₀ : X₀ ⟶ F₀.left), F = F₀.precomp f₀ :=
  ⟨F.δ₀, _, F.map' 0 1, ext' rfl (by simp) (by simp)⟩

lemma ext₂ {f g : ComposableArrows C 2}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm) : f = g :=
  ext' h₀ (ext₁ h₁ h₂ w₁) w₀

section

variable
  {f g : ComposableArrows C 2}
    (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
    (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2)

def homMk₂ : f ⟶ g := homMk' app₀ (homMk₁ app₁ app₂ w₁) w₀

@[simp]
lemma homMk₂_app_zero : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 0 = app₀ := rfl

@[simp]
lemma homMk₂_app_one : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 1 = app₁ := rfl

@[simp]
lemma homMk₂_app_two : (homMk₂ app₀ app₁ app₂ w₀ w₁).app ⟨2, by linarith⟩ = app₂ := rfl

end

@[ext]
lemma hom_ext₂ {f g : ComposableArrows C 2} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₁ h₁ h₂)

@[simps]
def isoMk₂ {f g : ComposableArrows C 2}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2) : f ≅ g where
  hom := homMk₂ app₀.hom app₁.hom app₂.hom w₀ w₁
  inv := homMk₂ app₀.inv app₁.inv app₂.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])

lemma mk₂_surjective (X : ComposableArrows C 2) :
    ∃ (X₀ X₁ X₂ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂), X = mk₂ f₀ f₁:=
  ⟨_, _, _, X.map' 0 1, X.map' 1 2, ext₂ rfl rfl rfl (by simp) (by simp)⟩

@[ext]
lemma hom_ext₃ {f g : ComposableArrows C 3} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₂ h₁ h₂ h₃)

section

variable
  {f g : ComposableArrows C 3}
    (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
    (app₃ : f.obj' 3 ⟶ g.obj' 3)
    (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3)

def homMk₃ : f ⟶ g := homMk' app₀ (homMk₂ app₁ app₂ app₃ w₁ w₂) w₀

@[simp]
lemma homMk₃_app_zero : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 0 = app₀ := rfl

@[simp]
lemma homMk₃_app_one : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 1 = app₁ := rfl

@[simp]
lemma homMk₃_app_two : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨2, by linarith⟩ = app₂ := rfl

@[simp]
lemma homMk₃_app_three : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨3, by linarith⟩ = app₃ := rfl

end

lemma ext₃ {f g : ComposableArrows C 3}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm) : f = g :=
  ext' h₀ (ext₂ h₁ h₂ h₃ w₁ w₂) w₀

@[simps]
def isoMk₃ {f g : ComposableArrows C 3}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3) : f ≅ g where
  hom := homMk₃ app₀.hom app₁.hom app₂.hom app₃.hom w₀ w₁ w₂
  inv := homMk₃ app₀.inv app₁.inv app₂.inv app₃.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])
    (by rw [← cancel_epi app₂.hom, ← reassoc_of% w₂, app₃.hom_inv_id,
      comp_id, app₂.hom_inv_id_assoc])

lemma mk₃_surjective (X : ComposableArrows C 3) :
    ∃ (X₀ X₁ X₂ X₃ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃), X = mk₃ f₀ f₁ f₂ :=
  ⟨_, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3,
    ext₃ rfl rfl rfl rfl (by simp) (by simp) (by simp)⟩

end ComposableArrows

@[simps]
def composableArrows₀Equivalence : ComposableArrows C 0 ≌ C where
  functor :=
    { obj := fun f => f.obj' 0
      map := fun f => ComposableArrows.app' f 0 }
  inverse :=
    { obj := fun X => ComposableArrows.mk₀ X
      map := fun f => ComposableArrows.homMk₀ f }
  unitIso := NatIso.ofComponents (fun X => ComposableArrows.isoMk₀ (Iso.refl _))
    (by aesop_cat)
  counitIso := Iso.refl _

set_option maxHeartbeats 600000 in
@[simps]
def composableArrows₁Equivalence : ComposableArrows C 1 ≌ Arrow C where
  functor :=
    { obj := fun F => Arrow.mk (F.map' 0 1)
      map := fun {F G} f =>
        { left := ComposableArrows.app' f 0
          right := ComposableArrows.app' f 1
          w := (f.naturality _).symm } }
  inverse :=
    { obj := fun f => ComposableArrows.mk₁ f.hom
      map := fun {f g} φ => ComposableArrows.homMk₁ φ.left φ.right φ.w.symm }
  unitIso := NatIso.ofComponents
    (fun f => ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _) (by aesop_cat))
      (by aesop_cat)
  counitIso := Iso.refl _

end CategoryTheory
