import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Sites.Subsheaf

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

variable (X Y : SSet.{u})

abbrev Subobject := GrothendieckTopology.Subpresheaf X

namespace Subobject

variable {X Y}

variable (S : X.Subobject) (T : Y.Subobject)

abbrev toSSet : SSet.{u} := S.toPresheaf

variable {S} in
@[ext]
lemma toSSet_ext {Δ : SimplexCategoryᵒᵖ} {x y : S.toSSet.obj Δ} (h : x.val = y.val) : x = y :=
  Subtype.ext h

abbrev ι : S.toSSet ⟶ X := GrothendieckTopology.Subpresheaf.ι S

@[simp]
lemma ι_app {Δ : SimplexCategoryᵒᵖ} (x : S.toSSet.obj Δ) :
    S.ι.app Δ x = x.val := rfl

instance : Mono S.ι := by
  change Mono (GrothendieckTopology.Subpresheaf.ι S)
  infer_instance

@[simps]
noncomputable def prod : (X ⊗ Y).Subobject where
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

noncomputable def unionProd : (X ⊗ Y).Subobject := ((⊤ : Subobject X).prod T) ⊔ (S.prod ⊤)

lemma top_prod_le_unionProd : (⊤ : Subobject X).prod T ≤ S.unionProd T := le_sup_left

lemma prod_top_le_unionProd : (S.prod ⊤) ≤ S.unionProd T := le_sup_right

lemma prod_le_top_prod : S.prod T ≤ (⊤ : Subobject X).prod T :=
  prod_monotone le_top (by rfl)

lemma prod_le_prod_top : S.prod T ≤ S.prod ⊤ :=
  prod_monotone (by rfl) le_top

lemma prod_le_unionProd : S.prod T ≤ S.unionProd T :=
  (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)

end Subobject

def subobjectBoundary (n : ℕ) : (Δ[n] : SSet.{u}).Subobject where
  obj _ s := ¬Function.Surjective (asOrderHom s)
  map φ s hs := ((boundary n).map φ ⟨s, hs⟩).2

lemma subobjectBoundary_toSSet (n : ℕ) : (subobjectBoundary.{u} n).toSSet = ∂Δ[n] := rfl

lemma subobjectBoundary_ι (n : ℕ) :
    (subobjectBoundary.{u} n).ι = boundaryInclusion n := rfl

def subobjectHorn (n : ℕ) (i : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subobject where
  obj _ s := Set.range (asOrderHom s) ∪ {i} ≠ Set.univ
  map φ s hs := ((horn n i).map φ ⟨s, hs⟩).2

lemma subobjectHorn_toSSet (n : ℕ) (i : Fin (n + 1)) :
    (subobjectHorn.{u} n i).toSSet = Λ[n, i] := rfl

lemma subobjectHorn_ι (n : ℕ) (i : Fin (n + 1)) :
    (subobjectHorn.{u} n i).ι = hornInclusion n i := rfl

section

variable {X Y}
variable (f : X ⟶ Y)

attribute [local simp] FunctorToTypes.naturality

@[simps]
def Subobject.image : Y.Subobject where
  obj Δ := Set.range (f.app Δ)
  map := by
    rintro Δ Δ' φ _ ⟨x, rfl⟩
    exact ⟨X.map φ x, by simp⟩

def toImageSubobject : X ⟶ (Subobject.image f).toSSet where
  app Δ x := ⟨f.app Δ x, ⟨x, rfl⟩⟩

@[simp]
lemma toImageSubobject_apply_val {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) :
    ((toImageSubobject f).app Δ x).val = f.app Δ x := rfl

@[reassoc (attr := simp)]
lemma toImageSubobject_ι : toImageSubobject f ≫ (Subobject.image f).ι = f := rfl

end

end SSet
