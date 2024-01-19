-- from LTE
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace fin3FunctorMk

variable (F : Fin 3 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2)

def map' : ∀ (i j : Fin 3) (_ : i ≤ j), F i ⟶ F j
| ⟨0,hi⟩, ⟨0,_⟩, _ => 𝟙 _
| ⟨1,hi⟩, ⟨1,_⟩, _ => 𝟙 _
| ⟨2,hi⟩, ⟨2,_⟩, _ => 𝟙 _
| ⟨0,_⟩, ⟨1,_⟩, _ => a
| ⟨1,_⟩, ⟨2,_⟩, _ => b
| ⟨0,hi⟩, ⟨2,hj⟩, _ => a ≫ b
| ⟨i+3,hi⟩, _, _ => by linarith
| _, ⟨j+3,hj⟩, _ => by linarith
| ⟨i+1,hi⟩, ⟨0,hj⟩, (H : i + 1 ≤ 0) => by linarith
| ⟨i+2,hi⟩, ⟨1,hj⟩, (H : i + 2 ≤ 1) => by linarith

lemma map'_id : ∀ (i : Fin 3), map' F a b i i le_rfl = 𝟙 _
| ⟨0,_⟩ => rfl
| ⟨1,_⟩ => rfl
| ⟨2,_⟩ => rfl
| ⟨i+3,hi⟩ => by norm_num at hi

lemma map'_comp : ∀ (i j k : Fin 3) (hij : i ≤ j) (hjk : j ≤ k),
  map' F a b i j hij ≫ map' F a b j k hjk = map' F a b i k (hij.trans hjk)
| ⟨0, _⟩, ⟨0, _⟩, k, _, _ => Category.id_comp _
| ⟨1, _⟩, ⟨1, _⟩, k, _, _ => Category.id_comp _
| i, ⟨1, _⟩, ⟨1, _⟩, _, _ => Category.comp_id _
| i, ⟨2, _⟩, ⟨2, _⟩, _, _ => Category.comp_id _
| ⟨0, _⟩, ⟨1, _⟩, ⟨2, _⟩, _, _ => rfl
| ⟨i+3,hi⟩, _, _, _, _ => by norm_num at hi
| _, ⟨j+3,hj⟩, _, _, _ => by norm_num at hj
| _, _, ⟨k+3,hk⟩, _, _ => by norm_num at hk
| ⟨i+1,hi⟩, ⟨0,hj⟩, _, (H : i + 1 ≤ 0), _ => by norm_num at H
| ⟨i+2,hi⟩, ⟨1,hj⟩, _, (H : i + 2 ≤ 1), _ => by exfalso; linarith
| _, ⟨i+1,hi⟩, ⟨0,hj⟩, _, (H : i + 1 ≤ 0) => by exfalso; linarith
| _, ⟨i+2,hi⟩, ⟨1,hj⟩, _, (H : i + 2 ≤ 1) => by exfalso; linarith

end fin3FunctorMk

def fin3FunctorMk (F : Fin 3 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2) : Fin 3 ⥤ C where
  obj := F
  map hij := fin3FunctorMk.map' F a b _ _ hij.le
  map_id _ := fin3FunctorMk.map'_id F a b _
  map_comp hij hjk := by rw [fin3FunctorMk.map'_comp F a b _ _ _ hij.le hjk.le]

namespace fin4FunctorMk

variable (F : Fin 4 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2) (c : F 2 ⟶ F 3)

def map' : ∀ (i j : Fin 4) (_ : i ≤ j), F i ⟶ F j
| ⟨0,hi⟩, ⟨0,_⟩, _ => 𝟙 _
| ⟨1,hi⟩, ⟨1,_⟩, _ => 𝟙 _
| ⟨2,hi⟩, ⟨2,_⟩, _ => 𝟙 _
| ⟨3,hi⟩, ⟨3,_⟩, _ => 𝟙 _
| ⟨0,_⟩, ⟨1,_⟩, _ => a
| ⟨1,_⟩, ⟨2,_⟩, _ => b
| ⟨2,_⟩, ⟨3,_⟩, _ => c
| ⟨0,hi⟩, ⟨2,hj⟩, _ => a ≫ b
| ⟨1,hi⟩, ⟨3,hj⟩, _ => b ≫ c
| ⟨0,hi⟩, ⟨3,hj⟩, _ => a ≫ b ≫ c
| ⟨i+4,hi⟩, _, _ => by exfalso; linarith
| _, ⟨j+4,hj⟩, _ => by exfalso; linarith
| ⟨i+1,hi⟩, ⟨0,hj⟩, (H : _ ≤ 0) => by exfalso; linarith
| ⟨i+2,hi⟩, ⟨1,hj⟩, (H : _ ≤ 1) => by exfalso; linarith
| ⟨3,hi⟩, ⟨2,hj⟩, (H : 3 ≤ 2) => by exfalso; linarith

lemma map'_id : ∀ (i : Fin 4), map' F a b c i i le_rfl = 𝟙 _
| ⟨0,hi⟩ => rfl
| ⟨1,hi⟩ => rfl
| ⟨2,hi⟩ => rfl
| ⟨3,hi⟩ => rfl
| ⟨i+4,hi⟩ => by exfalso; linarith

lemma map'_comp : ∀ (i j k : Fin 4) (hij : i ≤ j) (hjk : j ≤ k),
  map' F a b c i j hij ≫ map' F a b c j k hjk = map' F a b c i k (hij.trans hjk)
| ⟨0, _⟩, ⟨0, _⟩, k, _, _ => Category.id_comp _
| ⟨1, _⟩, ⟨1, _⟩, k, _, _ => Category.id_comp _
| ⟨2, _⟩, ⟨2, _⟩, k, _, _ => Category.id_comp _
| i, ⟨1, _⟩, ⟨1, _⟩, _, _ => Category.comp_id _
| i, ⟨2, _⟩, ⟨2, _⟩, _, _ => Category.comp_id _
| i, ⟨3, _⟩, ⟨3, _⟩, _, _ => Category.comp_id _
| ⟨0, _⟩, ⟨1, _⟩, ⟨2, _⟩, _, _ => rfl
| ⟨0, _⟩, ⟨1, _⟩, ⟨3, _⟩, _, _ => rfl
| ⟨0, _⟩, ⟨2, _⟩, ⟨3, _⟩, _, _ => Category.assoc a b c
| ⟨1, _⟩, ⟨2, _⟩, ⟨3, _⟩, _, _ => rfl
| ⟨i+4,hi⟩, _, _, _, _ => by exfalso; linarith
| _, ⟨j+4,hj⟩, _, _, _ => by exfalso; linarith
| _, _, ⟨k+4,hk⟩, _, _ => by exfalso; linarith
| ⟨i+1,hi⟩, ⟨0,hj⟩, _, (H : _ ≤ 0), _ => by exfalso; linarith
| ⟨i+2,hi⟩, ⟨1,hj⟩, _, (H : _ ≤ 1), _ => by exfalso; linarith
| ⟨3,hi⟩, ⟨2,hj⟩, _, (H : _ ≤ 2), _ => by exfalso; linarith
| _, ⟨i+1,hi⟩, ⟨0,hj⟩, _, (H : _ ≤ 0) => by exfalso; linarith
| _, ⟨i+2,hi⟩, ⟨1,hj⟩, _, (H : _ ≤ 1) => by exfalso; linarith
| _, ⟨3,hi⟩, ⟨2,hj⟩, _, (H : _ ≤ 2) => by exfalso; linarith


end fin4FunctorMk

def fin4FunctorMk (F : Fin 4 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2) (c : F 2 ⟶ F 3) : Fin 4 ⥤ C where
  obj := F
  map hij := fin4FunctorMk.map' F a b c _ _ hij.le
  map_id _ := fin4FunctorMk.map'_id F a b c _
  map_comp hij hjk := by rw [fin4FunctorMk.map'_comp F a b c _ _ _ hij.le hjk.le]

end CategoryTheory
