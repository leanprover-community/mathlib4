import Mathlib.AlgebraicGeometry.AlgebraicCycle.EulerCharAdditive
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Skyscraper
import Mathlib.Topology.Sheaves.Flasque

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    (p : X) (M : Type u) [AddCommGroup M]
    [Module (↑(X.ringCatSheaf.presheaf.stalk p)) M]

instance : Module k ↑(X.residueField p) := by
  --let o := Module.compHom (X.residueField p) (AlgebraicGeometry.Scheme.Hom.residueFieldMap (X ↘ (Spec (CommRingCat.of k))) p).hom
  --simp at o
  sorry

#check TopCat.Presheaf.IsFlasque
--#check of_shortExact_of_isFlasque₁₂

open TopCat.Sheaf in
lemma isFlasqueOfIso {C : Type*} [Category* C] {X : TopCat} {F G : TopCat.Sheaf C X}
    (h : F ≅ G) [IsFlasque F] : IsFlasque G := sorry

open TopCat.Sheaf in
instance : IsFlasque <|
    (SheafOfModules.toSheaf _).obj
    (skyscraperSheafOfModules p X.ringCatSheaf (X.residueField p)) := sorry

lemma skyscraper_h {n : ℕ} (h : n > 0) :
  (Scheme.Modules.h k (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) n) = 0 := sorry

/--
The euler characteristic of the skyscraper sheaf
-/
lemma eulerChar_skyscraper : Scheme.Modules.eulerChar k
    (skyscraperSheafOfModules p X.ringCatSheaf (X.residueField p)) =
    Module.finrank k (X.residueField p) := by
  simp [Scheme.Modules.eulerChar]
  have :
    ∑ᶠ (n : ℕ), (-1 : ℤ) ^ n * ↑(Scheme.Modules.h k (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) n)
    = (-1 : ℤ) ^ 0 * ↑(Scheme.Modules.h k (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) 0) +
      ∑ᶠ (n ∈ {m : ℕ | m > 0}), (-1 : ℤ) ^ n * ↑(Scheme.Modules.h k (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) n) := sorry
  rw [this]

  sorry
