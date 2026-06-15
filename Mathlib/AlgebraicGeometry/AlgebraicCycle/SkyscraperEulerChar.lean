import Mathlib.AlgebraicGeometry.AlgebraicCycle.EulerCharAdditive
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Skyscraper

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    (p : X) (M : Type u) [AddCommGroup M]
    [Module (↑(X.ringCatSheaf.presheaf.stalk p)) M]

instance : Module k ↑(X.residueField p) := by
  --let o := Module.compHom (X.residueField p) (AlgebraicGeometry.Scheme.Hom.residueFieldMap (X ↘ (Spec (CommRingCat.of k))) p).hom
  --simp at o
  sorry

/--
The euler characteristic of the skyscraper sheaf
-/
lemma eulerChar_skyscraper : Scheme.Modules.eulerChar k
    (skyscraperSheafOfModules p X.ringCatSheaf (X.residueField p)) =
    Module.finrank k (X.residueField p) := sorry
