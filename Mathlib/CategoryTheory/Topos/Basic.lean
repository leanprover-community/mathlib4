import Mathlib.CategoryTheory.Topos.Classifier

/-!
## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

universe u v u₀ v₀

namespace CategoryTheory

noncomputable section

open Category Limits Functor

structure PowerObject (ℰ : Type u) [Category.{v} ℰ] [HasTerminal ℰ] [HasClassifier ℰ] where
  P : ℰ → ℰ
  ε_ {B : ℰ} : prod B B

class ElementaryTopos (C : Type u) [Category.{v} C] [HasPullbacks C] [HasTerminal C] where
  classifier : Classifier C
