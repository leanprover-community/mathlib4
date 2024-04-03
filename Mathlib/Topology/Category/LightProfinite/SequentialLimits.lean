import Mathlib.Topology.Category.LightProfinite.Subcategory

open CategoryTheory Limits

namespace LightProfinite

variable (M : ℕᵒᵖ ⥤ LightProfinite)

noncomputable
def component_map {X Y : surj} (f : X ⟶ Y) (n : ℕ) : X.obj.component n ⟶ Y.obj.component n := by
  let g := locallyConstant_of_hom f n
  have := Profinite.exists_locallyConstant X.obj.cone X.obj.isLimit g
  let m := this.choose.unop
  let g' : LocallyConstant (X.obj.component m) (Y.obj.component n) := this.choose_spec.choose
  have h : g = g'.comap (X.obj.proj m) := this.choose_spec.choose_spec
  by_cases h : m ≤ n
  · exact X.obj.transitionMapLE' h ≫ ⟨g'.1, g'.2.continuous⟩
  · sorry

def functor : ℕᵒᵖ × ℕᵒᵖ ⥤ FintypeCat where
  obj := fun (n, m) ↦ (M.obj n).diagram.obj m
  map := @fun (n, m) (k, p) ((f : n ⟶ k), (g : m ⟶ p)) ↦ (by
    simp
    sorry
    )
  map_id := sorry
  map_comp := sorry

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
