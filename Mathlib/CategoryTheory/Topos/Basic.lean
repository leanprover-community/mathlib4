import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Opposites

/-!
## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

noncomputable section

universe u v u₀ v₀

namespace CategoryTheory

open Category Limits Functor

class ElementaryTopos (ℰ : Type u) [Category.{v} ℰ] [HasFiniteLimits ℰ] where
  hc : Classifier ℰ
  P (B : ℰ) : ℰ
  ε_ (B : ℰ) : B ⨯ (P B) ⟶ hc.Ω
  unhat {A B : ℰ} (f : B ⨯ A ⟶ hc.Ω) : (A ⟶ P B)
  comm {A B : ℰ} (f : B ⨯ A ⟶ hc.Ω) :
    f = (prod.map (𝟙 B) (unhat f)) ≫ ε_ B
  uniq {A B : ℰ} (f : B ⨯ A ⟶ hc.Ω) (g : A ⟶ P B)
    (_ : f = (prod.map (𝟙 B) g) ≫ ε_ B) : g = (unhat f)

variable {ℰ : Type u} [Category.{v} ℰ] [HasFiniteLimits ℰ] [ElementaryTopos ℰ]

open ElementaryTopos

def hat {A : ℰ} (B : ℰ) (g : A ⟶ P B) : B ⨯ A ⟶ hc.Ω := prod.map (𝟙 B) g ≫ ε_ B

lemma unhat_hat {A : ℰ} (B : ℰ) (g : A ⟶ P B) : g = unhat (hat B g) :=
  uniq (hat B g) g rfl

lemma hat_unhat {A B : ℰ} (f : B ⨯ A ⟶ hc.Ω) : f = hat B (unhat f) := comm _

def P_morph {B C : ℰ} (h : B ⟶ C) : P C ⟶ P B := unhat ((prod.map h (𝟙 _)) ≫ ε_ C)

open Opposite

def P_functor : ℰᵒᵖ ⥤ ℰ := {
  obj B := P (unop B),
  map h := P_morph (unop h),
  map_id B := Eq.symm (uniq _ _ (by rfl)),
  map_comp := sorry
}

end CategoryTheory
