import Mathlib.Topology.Category.LightProfinite.Subcategory

open CategoryTheory Limits

namespace LightProfinite

variable (M : ℕᵒᵖ ⥤ surj)

noncomputable
def component_map {X Y : surj} (f : X ⟶ Y) (n : ℕ) : X.obj.diagram.obj ⟨n⟩ ⟶ Y.obj.diagram.obj ⟨n⟩ :=
  let g := locallyConstant_of_hom f n
  have := Profinite.exists_locallyConstant X.obj.cone X.obj.isLimit g
  let m := this.choose.unop
  let g' : LocallyConstant (X.obj.component m) (Y.obj.component n) := this.choose_spec.choose
  -- have h : g = g'.comap (X.obj.proj m) := this.choose_spec.choose_spec
  if hh : m ≤ n then
    X.obj.transitionMapLE hh ≫ g'.1 else
    (section_ (X.obj.transitionMapLE
      (le_of_lt (by simpa using hh)))) ≫ g'.1

noncomputable def functor : ℕᵒᵖ × ℕᵒᵖ ⥤ FintypeCat where
  obj n := (M.obj n.1).obj.diagram.obj n.2
  map f := (M.obj _).obj.diagram.map f.2 ≫ (component_map (M.map f.1) _)
  map_id := sorry
  map_comp := sorry

#exit

def limitCone : Cone M where
  pt := {
    diagram := {
      obj := fun n ↦ (M.obj n).diagram.obj n
      map := @fun n m f ↦ (by
        --fun f n ↦ (M.obj _).diagram.map f
        simp
        refine (M.obj n).diagram.map f ≫ ?_
        let g := M.map f
        sorry
        )
      map_id := sorry
      map_comp := sorry
    }
    cone := sorry
    isLimit := sorry
  }
  π := sorry
