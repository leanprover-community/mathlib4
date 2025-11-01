structure GhostAdj (R C : Type _) [Category R] [Category C] where
  P        : R ⥤ C
  R'       : C ⥤ R
  adj      : P ⊣ R'
  ghost    : MorphismProperty R
  ghost_def :
    ∀ {X Y : R} (f : X ⟶ Y), ghost f ↔ IsIso (P.map f)

namespace GhostAdj

variable {R C : Type _} [Category R] [Category C]
variable (GA : GhostAdj R C)

open MorphismProperty

lemma ghost_comp  {X Y Z : R} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : GA.ghost f) (hg : GA.ghost g) :
    GA.ghost (f ≫ g) := by
  have hf_iso : IsIso (GA.P.map f) := (GA.ghost_def f).1 hf
  have hg_iso : IsIso (GA.P.map g) := (GA.ghost_def g).1 hg
  have hfg_iso : IsIso (GA.P.map (f ≫ g)) := by
    simpa [Functor.map_comp] using (IsIso.comp hf_iso hg_iso)
  exact (GA.ghost_def (f ≫ g)).2 hfg_iso

end GhostAdj
