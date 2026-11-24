import Mathlib.Tactic.Simps.Generalized
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Tests for `simps!!` with limits -/

open CategoryTheory Limits

namespace SimpsGenTest

variable {C : Type*} [Category* C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

/-! The generalized projections used here are registered in Mathlib, next to `PullbackCone.fst`,
`pullback.fst`, `Fork.ι`, …; see `Mathlib.Tactic.Simps.Generalized`. -/

/-! ### Pullback cones -/

@[simps!!]
def cone {W : C} (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ g) : PullbackCone f g :=
  PullbackCone.mk a b w

/-! ### Morphisms into pullbacks -/

@[simps!!]
noncomputable def toPb [HasPullback f g] {W : C} (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ g) :
    W ⟶ pullback f g :=
  pullback.lift a b w

/-! ### Isomorphisms of pullbacks -/

@[simps!!]
noncomputable def swap [HasPullback f g] [HasPullback g f] : pullback f g ≅ pullback g f :=
  pullbackSymmetry f g

/-- An isomorphism given by its components. -/
@[simps!!]
noncomputable def swap' [HasPullback f g] [HasPullback g f] : pullback f g ≅ pullback g f where
  hom := pullback.lift (pullback.snd f g) (pullback.fst f g) (pullback.condition).symm
  inv := pullback.lift (pullback.snd g f) (pullback.fst g f) (pullback.condition).symm

/-- An isomorphism between a pullback and an object that is not a limit. -/
@[simps!!]
noncomputable def idPb [HasPullback (𝟙 Z) g] : pullback (𝟙 Z) g ≅ Y where
  hom := pullback.snd _ _
  inv := pullback.lift g (𝟙 Y) (by simp)
  hom_inv_id := by ext <;> simp [← pullback.condition]

/-! ### Forks and limit forks -/

variable {f' g' : X ⟶ Y}


@[simps!!]
def fork {P : C} (ι : P ⟶ X) (w : ι ≫ f' = ι ≫ g') : Fork f' g' := Fork.ofι ι w


@[simps!!]
def forkIsLimit {P : C} (ι : P ⟶ X) (w : ι ≫ f' = ι ≫ g') [Mono ι]
    (lift : ∀ {W : C} (k : W ⟶ X), k ≫ f' = k ≫ g' → (W ⟶ P))
    (fac : ∀ {W : C} (k : W ⟶ X) (hk : k ≫ f' = k ≫ g'), lift k hk ≫ ι = k) :
    IsLimit (Fork.ofι ι w) :=
  Fork.IsLimit.mk _ (fun s => lift s.ι s.condition) (fun s => fac _ _)
    (fun s m hm => by rw [← cancel_mono ι, fac]; exact hm)

/-! ### The generated lemmas -/

section
variable {W : C} (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ g)

example : (cone a b w).pt = W := cone_pt a b w
example : (cone a b w).fst = a := cone_fst a b w
example : (cone a b w).snd = b := cone_snd a b w
-- `π` is hidden in favor of `fst` and `snd`
#guard_msgs (drop error) in #check cone_π_app

variable [HasPullback f g] [HasPullback g f]

example : toPb a b w ≫ pullback.fst f g = a := toPb_fst a b w
example : toPb a b w ≫ pullback.snd f g = b := toPb_snd a b w
example {V : C} (k : X ⟶ V) : toPb a b w ≫ pullback.fst f g ≫ k = a ≫ k := by simp

example : swap.hom ≫ pullback.fst g f = pullback.snd f g := swap_hom_fst
example : swap.hom ≫ pullback.snd g f = pullback.fst f g := swap_hom_snd
example : swap.inv ≫ pullback.fst f g = pullback.snd g f := swap_inv_fst
example : swap.inv ≫ pullback.snd f g = pullback.fst g f := swap_inv_snd
example : pullback.lift a b w ≫ swap.hom = pullback.lift b a w.symm := swap_lift_hom a b w
example (a : W ⟶ Y) (b : W ⟶ X) (w : a ≫ g = b ≫ f) :
    pullback.lift a b w ≫ swap.inv = pullback.lift b a w.symm := swap_lift_inv a b w
example {V : C} (k : pullback g f ⟶ V) :
    pullback.lift a b w ≫ swap.hom ≫ k = pullback.lift b a w.symm ≫ k := by simp
-- no lemmas about `lift ≫ swap.hom ≫ fst`: they follow from `swap_hom_fst` and `lift_fst`
#guard_msgs (drop error) in #check swap_hom_lift_fst
-- no lemma about `swap.hom` itself: `fst` and `snd` apply to it
#guard_msgs (drop error) in #check swap_hom

example : swap'.hom ≫ pullback.fst g f = pullback.snd f g := swap'_hom_fst

variable [HasPullback (𝟙 Z) g]

example (a : W ⟶ Z) (b : W ⟶ Y) (w : a ≫ 𝟙 Z = b ≫ g) : pullback.lift a b w ≫ idPb.hom = b :=
  idPb_lift_hom a b w
example : idPb.inv ≫ pullback.fst (𝟙 Z) g = g := idPb_inv_fst
example : idPb.inv ≫ pullback.snd (𝟙 Z) g = 𝟙 Y := idPb_inv_snd

end

section
variable {P : C} (ι : P ⟶ X) (w : ι ≫ f' = ι ≫ g')

example : (fork ι w).pt = P := fork_pt ι w
example : (fork ι w).ι = ι := fork_ι ι w

variable [Mono ι] (lift : ∀ {W : C} (k : W ⟶ X), k ≫ f' = k ≫ g' → (W ⟶ P))
    (fac : ∀ {W : C} (k : W ⟶ X) (hk : k ≫ f' = k ≫ g'), lift k hk ≫ ι = k)

example {W : C} (k : W ⟶ X) (hk : k ≫ f' = k ≫ g') :
    Fork.IsLimit.lift (forkIsLimit ι w lift fac) k hk = lift k hk :=
  forkIsLimit_lift ι w lift fac k hk
example {W : C} (k : W ⟶ X) (hk : k ≫ f' = k ≫ g') :
    Fork.IsLimit.lift (forkIsLimit ι w lift fac) k hk = lift k hk := by
  simp

end

/-! ### Arguments that the self argument doesn't determine

In `BinaryFan.IsLimit.lift {W : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X) (g : W ⟶ Y)`,
`W` comes before the self argument `h`, but its type doesn't determine it: `W` is moved after `h`,
with `f` and `g`. -/

section
variable [HasBinaryProduct X Y]

@[simps!!]
noncomputable def fanIsLimit : IsLimit (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) :=
  prodIsProd X Y

example {W : C} (a : W ⟶ X) (b : W ⟶ Y) :
    BinaryFan.IsLimit.lift fanIsLimit a b = prod.lift a b :=
  fanIsLimit_lift a b
#guard_msgs (drop error) in #check fanIsLimit_lift_1
end

end SimpsGenTest
