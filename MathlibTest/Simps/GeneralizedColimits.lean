import Mathlib.Tactic.Simps.Generalized
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Tests for `simps!!` with colimits

The dual of `GeneralizedLimits.lean`. The shape of the registrations is reversed: the
field-like projections (`inl ≫ h`, `π ≫ h`) are *precompositions* (`precomp`), keyed on morphisms
out of the colimit, and named before the last component (`e_inl_hom`); the universal property
(`h ≫ desc a b w`) is a *postcomposition* (`comp`), keyed on morphisms into the colimit
(`e_hom_desc`).
-/

open CategoryTheory Limits

namespace SimpsGenColimitTest

variable {C : Type*} [Category* C]

/-! ## Pushouts -/

section Pushout

variable {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}

/-! The generalized projections used here are registered in Mathlib, as the `to_dual`
translations of those for limits; see `Mathlib.Tactic.Simps.Generalized`. -/

/-! ### Definitions -/

@[simps!!]
def cocone {W : C} (a : Y ⟶ W) (b : Z ⟶ W) (w : f ≫ a = g ≫ b) : PushoutCocone f g :=
  PushoutCocone.mk a b w

@[simps!!]
noncomputable def fromPo [HasPushout f g] {W : C} (a : Y ⟶ W) (b : Z ⟶ W) (w : f ≫ a = g ≫ b) :
    pushout f g ⟶ W :=
  pushout.desc a b w

@[simps!!]
noncomputable def swap [HasPushout f g] [HasPushout g f] : pushout f g ≅ pushout g f :=
  pushoutSymmetry f g

/-- An isomorphism given by its components. -/
@[simps!!]
noncomputable def swap' [HasPushout f g] [HasPushout g f] : pushout f g ≅ pushout g f where
  hom := pushout.desc (pushout.inr g f) (pushout.inl g f) (pushout.condition).symm
  inv := pushout.desc (pushout.inr f g) (pushout.inl f g) (pushout.condition).symm

/-- An isomorphism between a pushout and an object that is not a colimit. -/
@[simps!!]
noncomputable def idPo [HasPushout (𝟙 X) g] : pushout (𝟙 X) g ≅ Z where
  hom := pushout.desc g (𝟙 Z) (by simp)
  inv := pushout.inr _ _
  inv_hom_id := by simp
  hom_inv_id := by
    ext
    · simpa using (pushout.condition (f := 𝟙 X) (g := g)).symm
    · simp

/-! ### The generated lemmas -/

variable {W : C} (a : Y ⟶ W) (b : Z ⟶ W) (w : f ≫ a = g ≫ b)

example : (cocone a b w).pt = W := cocone_pt a b w
example : (cocone a b w).inl = a := cocone_inl a b w
example : (cocone a b w).inr = b := cocone_inr a b w
-- `ι` is hidden in favor of `inl` and `inr`
#guard_msgs (drop error) in #check cocone_ι_app

variable [HasPushout f g] [HasPushout g f]

example : pushout.inl f g ≫ fromPo a b w = a := inl_fromPo a b w
example : pushout.inr f g ≫ fromPo a b w = b := inr_fromPo a b w
example {V : C} (k : W ⟶ V) : pushout.inl f g ≫ fromPo a b w ≫ k = a ≫ k := by simp

example : pushout.inl f g ≫ swap.hom = pushout.inr g f := swap_inl_hom
example : pushout.inr f g ≫ swap.hom = pushout.inl g f := swap_inr_hom
example : pushout.inl g f ≫ swap.inv = pushout.inr f g := swap_inl_inv
example : pushout.inr g f ≫ swap.inv = pushout.inl f g := swap_inr_inv
example (a : Z ⟶ W) (b : Y ⟶ W) (w : g ≫ a = f ≫ b) :
    swap.hom ≫ pushout.desc a b w = pushout.desc b a w.symm := swap_hom_desc a b w
example : swap.inv ≫ pushout.desc a b w = pushout.desc b a w.symm := swap_inv_desc a b w
example {V : C} (k : V ⟶ pushout f g) (a : Z ⟶ W) (b : Y ⟶ W) (w : g ≫ a = f ≫ b) :
    k ≫ swap.hom ≫ pushout.desc a b w = k ≫ pushout.desc b a w.symm := by simp
-- no lemma about `swap.hom` itself: `inl` and `inr` apply to it
#guard_msgs (drop error) in #check swap_hom
-- no lemmas about `inl ≫ swap.hom ≫ desc`: they follow from `swap_inl_hom` and `inl_desc`
#guard_msgs (drop error) in #check swap_inl_hom_desc

example : pushout.inl f g ≫ swap'.hom = pushout.inr g f := swap'_inl_hom
example (a : Z ⟶ W) (b : Y ⟶ W) (w : g ≫ a = f ≫ b) :
    swap'.hom ≫ pushout.desc a b w = pushout.desc b a w.symm := swap'_hom_desc a b w

variable [HasPushout (𝟙 X) g]

example : pushout.inl (𝟙 X) g ≫ idPo.hom = g := idPo_inl_hom
example : pushout.inr (𝟙 X) g ≫ idPo.hom = 𝟙 Z := idPo_inr_hom
example (a : X ⟶ W) (b : Z ⟶ W) (w : 𝟙 X ≫ a = g ≫ b) :
    idPo.inv ≫ pushout.desc a b w = b :=
  idPo_inv_desc a b w

end Pushout

/-! ## Coequalizers -/

section Coequalizer

variable {X Y : C} {f g : X ⟶ Y}

@[simps!!]
def cofork {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : Cofork f g := Cofork.ofπ π w

@[simps!!]
def coforkIsColimit {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) [Epi π]
    (desc : ∀ {W : C} (k : Y ⟶ W), f ≫ k = g ≫ k → (P ⟶ W))
    (fac : ∀ {W : C} (k : Y ⟶ W) (hk : f ≫ k = g ≫ k), π ≫ desc k hk = k) :
    IsColimit (Cofork.ofπ π w) :=
  Cofork.IsColimit.mk _ (fun s => desc s.π s.condition) (fun s => fac _ _)
    (fun s m hm => by rw [← cancel_epi π, fac]; exact hm)

/-- An isomorphism between two coequalizers. -/
@[simps!!]
noncomputable def coeqSwap [HasCoequalizer f g] [HasCoequalizer g f] :
    coequalizer f g ≅ coequalizer g f where
  hom := coequalizer.desc (coequalizer.π g f) (coequalizer.condition g f).symm
  inv := coequalizer.desc (coequalizer.π f g) (coequalizer.condition f g).symm

variable {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π)

example : (cofork π w).pt = P := cofork_pt π w
example : (cofork π w).π = π := cofork_π π w
#guard_msgs (drop error) in #check cofork_ι_app

example [Epi π] (desc : ∀ {W : C} (k : Y ⟶ W), f ≫ k = g ≫ k → (P ⟶ W))
    (fac : ∀ {W : C} (k : Y ⟶ W) (hk : f ≫ k = g ≫ k), π ≫ desc k hk = k)
    {W : C} (k : Y ⟶ W) (hk : f ≫ k = g ≫ k) :
    Cofork.IsColimit.desc (coforkIsColimit π w desc fac) k hk = desc k hk := by
  simp

variable [HasCoequalizer f g] [HasCoequalizer g f] {W : C} (k : Y ⟶ W)

example : coequalizer.π f g ≫ coeqSwap.hom = coequalizer.π g f := coeqSwap_π_hom
example (w : g ≫ k = f ≫ k) : coeqSwap.hom ≫ coequalizer.desc k w = coequalizer.desc k w.symm :=
  coeqSwap_hom_desc k w

end Coequalizer

/-! ## Binary coproducts -/

section Coprod

variable {X Y : C}

/-- A Mathlib isomorphism, which already has `simps` lemmas for `hom` and `inv`; `simps!!` gives
the lemmas about its composites instead. -/
@[simps!!]
noncomputable def braid [HasBinaryCoproduct X Y] [HasBinaryCoproduct Y X] : X ⨿ Y ≅ Y ⨿ X :=
  coprod.braiding X Y

variable [HasBinaryCoproduct X Y] [HasBinaryCoproduct Y X] {W : C}

example : coprod.inl ≫ (braid (X := X) (Y := Y)).hom = coprod.inr := braid_inl_hom
example : coprod.inr ≫ (braid (X := X) (Y := Y)).hom = coprod.inl := braid_inr_hom
example (a : Y ⟶ W) (b : X ⟶ W) : braid.hom ≫ coprod.desc a b = coprod.desc b a :=
  braid_hom_desc a b
example (a : X ⟶ W) (b : Y ⟶ W) : braid.inv ≫ coprod.desc a b = coprod.desc b a :=
  braid_inv_desc a b

end Coprod

end SimpsGenColimitTest
