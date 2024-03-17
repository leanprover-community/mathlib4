import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Sites.Subsheaf

universe u

open CategoryTheory MonoidalCategory

namespace SSet

variable (X Y : SSet.{u})

abbrev Subobject := GrothendieckTopology.Subpresheaf X

namespace Subobject

variable {X Y}

variable (S : X.Subobject) (T : Y.Subobject)

abbrev toSSet : SSet.{u} := S.toPresheaf

abbrev ι : S.toSSet ⟶ X := GrothendieckTopology.Subpresheaf.ι S

@[simp]
lemma ι_app {Δ : SimplexCategoryᵒᵖ} (x : S.toSSet.obj Δ) :
    S.ι.app Δ x = x.val := rfl

instance : Mono S.ι := by
  change Mono (GrothendieckTopology.Subpresheaf.ι S)
  infer_instance

@[simps]
def prod : (X ⊗ Y).Subobject where
  obj Δ := (S.obj Δ).prod (T.obj Δ)
  map i _ hx := ⟨S.map i hx.1, T.map i hx.2⟩

lemma prod_monotone {S₁ S₂ : X.Subobject} (hX : S₁ ≤ S₂) {T₁ T₂ : Y.Subobject} (hY : T₁ ≤ T₂) :
    S₁.prod T₁ ≤ S₂.prod T₂ :=
  fun _ _ hx => ⟨hX _ hx.1, hY _ hx.2⟩

instance : PartialOrder (Subobject X) := inferInstance
instance : SemilatticeSup (Subobject X) := inferInstance

section

variable {S₁ S₂ : X.Subobject} (h : S₁ ≤ S₂)

def homOfLE : S₁.toSSet ⟶ S₂.toSSet := GrothendieckTopology.Subpresheaf.homOfLe h

@[simp]
lemma homOfLE_app_val (Δ : SimplexCategoryᵒᵖ) (x : S₁.toSSet.obj Δ) :
    ((homOfLE h).app Δ x).val = x.val := rfl

@[reassoc (attr := simp)]
lemma homOfLE_ι : homOfLE h ≫ S₂.ι = S₁.ι := rfl

instance : Mono (homOfLE h) := mono_of_mono_fac (homOfLE_ι h)

end

def unionProd : (X ⊗ Y).Subobject := ((⊤ : Subobject X).prod T) ⊔ (S.prod ⊤)

lemma top_prod_le_unionProd : (⊤ : Subobject X).prod T ≤ S.unionProd T := le_sup_left

lemma prod_top_le_unionProd : (S.prod ⊤) ≤ S.unionProd T := le_sup_right

lemma prod_le_top_prod : S.prod T ≤ (⊤ : Subobject X).prod T :=
  prod_monotone le_top (by rfl)

lemma prod_le_prod_top : S.prod T ≤ S.prod ⊤ :=
  prod_monotone (by rfl) le_top

lemma prod_le_unionProd : S.prod T ≤ S.unionProd T :=
  (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)

end Subobject

end SSet
