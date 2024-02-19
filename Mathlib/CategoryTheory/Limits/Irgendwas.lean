import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.IsConnected
import Mathlib.Data.Setoid.Basic

universe v u

namespace CategoryTheory.Limits.Types

open CategoryTheory.Limits
open CategoryTheory.Limits.Types

variable (C : Type u) [Category.{v} C]

def unitValuedFunctor : C ⥤ TypeMax.{u, v} := (Functor.const C).obj PUnit.{(max u v) + 1}

instance instSubsingletonColimitPUnit [IsConnected C] :
    Subsingleton (colimit (unitValuedFunctor C)) where
  allEq := by
    intro a b
    let ⟨c, _, p⟩ := jointly_surjective' a
    let ⟨d, _, q⟩ := jointly_surjective' b
    let r: C → C → Prop := Eq on (fun c => colimit.ι (unitValuedFunctor C) c PUnit.unit)
    let r_equivalence : _root_.Equivalence r := eq_equivalence.comap _
    suffices hr: r c d
    · rw [← p, ← q]
      exact hr
    · refine equiv_relation r r_equivalence ?_ c d
      intro _ _ hom
      apply colimit_sound hom
      simp [unitValuedFunctor]

noncomputable instance instInhabitedColimitPUnit [IsConnected C] :
    Inhabited (colimit (unitValuedFunctor C)) where
  default := colimit.ι (unitValuedFunctor C) Classical.ofNonempty PUnit.unit

noncomputable instance instNonemptyColimitPUnit [IsConnected C] :
    Nonempty (colimit (unitValuedFunctor C)) := Nonempty.intro default

noncomputable instance instUniqueColimitPUnit [IsConnected C] :
    Unique (colimit (unitValuedFunctor C)) := Unique.mk' _

noncomputable def colimitConstPUnitIsoPUnit [IsConnected C] :
    colimit (unitValuedFunctor C) ≅ PUnit := (Equiv.equivOfUnique _ _).toIso

theorem zag_of_hom {c d : C} (h : c ⟶ d) : Zag c d := Or.inl (Nonempty.intro h)

theorem zigzag_of_hom {c d : C} (h : c ⟶ d) : Zigzag c d :=
    Relation.ReflTransGen.single (zag_of_hom _ h)

theorem nonempty_of_nonempty_quot {α : Type u} {r : α → α → Prop} :
    Nonempty (_root_.Quot r) → Nonempty α :=
  fun ⟨q⟩ => nonempty_of_exists (Quot.exists_rep q)

theorem nonempty_of_nonempty_colimit {F : C ⥤ TypeMax.{u, v}} :
    Nonempty (colimit F) → Nonempty C :=
  fun ⟨q⟩ => Quot.ind (fun ⟨c, _⟩ => Nonempty.intro c) ((colimitEquivQuot _).toFun q)

theorem zigzag_of_eq_colimit' {F : C ⥤ TypeMax.{u, v}} {c d : C} {fc : F.obj c} {fd : F.obj d}
    (h : (colimitCocone F).ι.app c fc = (colimitCocone F).ι.app d fd) : Zigzag c d := by
  let f : (c' : C) × F.obj c' → Quotient (Zigzag.setoid C) := fun ⟨j, _⟩ => Quot.mk _ j
  let g : Quot F → Quotient (Zigzag.setoid C) :=
    _root_.Quot.lift f (fun _ _ ⟨hom, _⟩ => Quot.sound (zigzag_of_hom C hom))
  let h1 : f ⟨c, fc⟩ = f ⟨d, fd⟩ := congr_arg g h
  exact (Equivalence.eqvGen_iff zigzag_equivalence).mp (Quot.exact _ h1)

theorem zigzag_of_eq_colimit {F : C ⥤ TypeMax.{u, v}} {c d : C} {fc : F.obj c} {fd : F.obj d}
    (h : colimit.ι F c fc = colimit.ι F d fd) : Zigzag c d := by
  let h := congr_arg (colimitEquivQuot _) h
  simp only [colimitEquivQuot_apply] at h
  exact zigzag_of_eq_colimit' C h

theorem connected_iff_colimit_const_punit_iso_punit :
    IsConnected C ↔ Nonempty (colimit (unitValuedFunctor C) ≅ PUnit) := by
  constructor
  · intro connected
    apply Nonempty.intro
    exact colimitConstPUnitIsoPUnit C
  · intro ⟨h⟩
    have _: Nonempty C :=
        nonempty_of_nonempty_colimit _ (Nonempty.map h.symm.toEquiv.toFun inferInstance)
    apply zigzag_isConnected
    intro c d
    let F := unitValuedFunctor C
    have hh : colimit.ι F c PUnit.unit = colimit.ι F d PUnit.unit := h.toEquiv.injective rfl
    exact zigzag_of_eq_colimit C hh

end CategoryTheory.Limits.Types
