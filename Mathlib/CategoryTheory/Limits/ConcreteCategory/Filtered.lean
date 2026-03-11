module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

namespace CategoryTheory.Limits

variable {J C : Type*} [Category* J] [Category* C]
  {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC] [PreservesColimitsOfShape J (forget C)]
  (F : J ⥤ C) [IsFilteredOrEmpty J]

lemma IsColimit.eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : ToType <| F.obj i}
    {xj : ToType <| F.obj j} : t.ι.app i xi = t.ι.app j xj ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k),
    F.map f xi = F.map g xj :=
  Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (forget C) ht)

variable {F} in
lemma IsColimit.eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : ToType <| F.obj i) :
    t.ι.app i x = t.ι.app i y ↔ ∃ (j : _) (f : i ⟶ j), F.map f x = F.map f y :=
  Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget C) ht) x y

lemma colimit_eq_iff [HasColimit F] {i j : J} {xi : ToType <| F.obj i} {xj : ToType <| F.obj j} :
    colimit.ι F i xi = colimit.ι F j xj ↔
      ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
  (colimit.isColimit F).eq_iff _

end CategoryTheory.Limits
