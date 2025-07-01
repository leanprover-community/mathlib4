import Mathlib.CategoryTheory.Topos.Classifier

/-!
## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

universe u v u₀ v₀

namespace CategoryTheory

open Category Limits Functor

structure PowerObject (C : Type u) [Category.{v} C] [HasTerminal C] [HasClassifier C] where
  P : C → C
  ε_ {B : C} : prod B (P B)

class ElementaryTopos (C : Type u) [Category.{v} C] [HasPullbacks C] [HasTerminal C] where
  classifier : Classifier C
