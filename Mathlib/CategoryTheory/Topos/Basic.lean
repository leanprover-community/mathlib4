import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Opposites

/-!
# Elementary Topos (in Elementary Form)

This ongoing work formalizes the elementary definition of a topos and the direct consequences.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/


universe u v u₀ v₀

namespace CategoryTheory

open Category Limits Functor

/-- A category `ℰ` is an elementary topos if it has finite limits
and satisfies a power object condition relative to a fixed subobject classifier `Ω`.

See MM92, Chapter IV, Section 1. -/

local notation "𝟙⨯ " f => prod.map (𝟙 _) f
local notation f " ⨯𝟙" => prod.map f (𝟙 _)

class ElementaryTopos (ℰ : Type u) [Category.{v} ℰ] [HasFiniteLimits ℰ] where

  /-- A fixed choice of subobject classifier in `ℰ`, supplying mainly
  `Ω`, `true : ⊤_ C ⟶ Ω`, and `χ` to build the characteristic map. -/
  hc : Classifier ℰ
  /-- The power object functor `P : ℰᵒᵖ ⥤ ℰ`, defined objectwise. -/
  P (B : ℰ) : ℰ
  /-- The element relation. -/
  ε_ (B : ℰ) : B ⨯ (P B) ⟶ hc.Ω
  /-- The P-transpose of a morphism `f : B × A ⟶ Ω`. See equation (6) of MM92. -/
  unhat {A B : ℰ} (f : B ⨯ A ⟶ hc.Ω) : (A ⟶ P B)
  /-- Characteristic equation: any `f : B × A ⟶ Ω` is equal to `ε_B ∘ (𝟙 ⨯ g)`
      where `g` is the P-transpose of `f`. -/
  comm {A B : ℰ} (f : B ⨯ A ⟶ hc.Ω) :
    f = (𝟙⨯ (unhat f)) ≫ ε_ B
  /-- Uniqueness: the P-transpose `g : A ⟶ P B` is uniquely determined by `f`. -/
  uniq {A B : ℰ} (f : B ⨯ A ⟶ hc.Ω) (g : A ⟶ P B)
    (_ : f = (𝟙⨯ g) ≫ ε_ B) : g = (unhat f)

variable {ℰ : Type u} [Category.{v} ℰ] [HasFiniteLimits ℰ] [ElementaryTopos ℰ]

open ElementaryTopos

noncomputable section

/-- The morphism `ε_B ∘ (𝟙 × g)` associated to a map `g : A ⟶ P B`.
    This is the inverse direction of the transpose isomorphism. -/
def hat {A : ℰ} (B : ℰ) (g : A ⟶ P B) : B ⨯ A ⟶ hc.Ω := (𝟙⨯ g) ≫ ε_ B

/-- The morphism `P_morph h` is the functorial action on a morphism `h : B ⟶ C`,
    defined as the P-transpose of `∘ ε_C ∘ h ⨯ 𝟙`. -/
def P_morph {B C : ℰ} (h : B ⟶ C) : P C ⟶ P B := unhat ((h ⨯𝟙) ≫ ε_ C)

/-- Naturality (dinaturality) of `ε`. This corresponds to the naturality square of ε
    in MM92 diagram (5). -/
def ε_dinaturality {B C : ℰ} (h : B ⟶ C) :
  (h ⨯𝟙) ≫ ε_ C = (𝟙⨯ (P_morph h)) ≫ ε_ B := comm _

/-- Functoriality of `P`: divide the dinaturality square of `h ∘ h'` into three squares,
    one on the left described by `comm_left`, and two smaller dinaturality squares
    for `h` and `h'` respectively stacked atop of each other on the right. -/
lemma P_compose {B C D : ℰ} (h : B ⟶ C) (h' : C ⟶ D) :
    P_morph (h ≫ h') = P_morph h' ≫ P_morph h :=
  let comm_left : (h ⨯𝟙) ≫ (𝟙⨯ (P_morph h')) = (𝟙⨯ (P_morph h')) ≫ (h ⨯𝟙) := by simp
  let comm_outer : (h ⨯𝟙) ≫ (h' ⨯𝟙) ≫ ε_ D = (𝟙⨯ (P_morph h')) ≫ (𝟙⨯ (P_morph h)) ≫ ε_ B :=
    by rw [ε_dinaturality h', ← assoc, comm_left, assoc, ε_dinaturality h]
  let eq : (𝟙⨯ (P_morph h')) ≫ (𝟙⨯ (P_morph h)) ≫ ε_ B =
      (𝟙⨯ P_morph h' ≫ P_morph h) ≫ ε_ B := by rw [← assoc, prod.map_id_comp]
  by rw [P_morph, prod.map_comp_id, assoc, comm_outer, ← uniq _ _ eq]

open Opposite

/-- The power object functor `P : ℰᵒᵖ ⥤ ℰ` defined by the transpose correspondence.
    This makes the diagram in MM92 (7) commute. -/
def P_functor : ℰᵒᵖ ⥤ ℰ := {
  obj B := P (unop B),
  map h := P_morph h.unop,
  map_id B := Eq.symm (uniq _ _ (by rfl)),
  map_comp {B C D : ℰᵒᵖ} (h : B ⟶ C) (h' : C ⟶ D) := P_compose h'.unop h.unop
}

/--
Given a morphism `g : A ⟶ P C` and a morphism `h : B ⟶ C`, the characteristic map
of the composite `Ph ∘ g : A ⟶ P B` is equal to the pullback of the characteristic
map `g^` along the morphism `h × 𝟙 : B × A ⟶ C × A`.

This expresses the dinaturality of the `hat` construction, or equivalently,
that the transpose of `Ph ∘ g` is the pullback of the transpose of `g`
along `h × 1`, as in diagram (8) of the reference.

This result reflects how subobjects pull back along morphisms in an elementary topos,
via the classifier `Ω` and the classifying morphisms `χ`.

It shows that `(Ph ∘ g)^` is equal to the classifying map
associated to the pullback of the subobject classified by `g`.
-/
theorem pullback_of_char {A B C U : ℰ} (g : A ⟶ P C) (h : B ⟶ C) (m : U ⟶ C ⨯ A) [Mono m]
    (isChar : hat C g = hc.χ m) :
    hat B (g ≫ P_morph h) = hc.χ (pullback.snd m (h ⨯𝟙)) :=
  let pb_right := IsPullback.flip (hc.isPullback m)
  let m' := pullback.snd m (h ⨯𝟙)
  let pb_left := IsPullback.of_hasPullback m (h ⨯𝟙)
  let pb_outer := IsPullback.paste_horiz pb_left pb_right
  let eq₀ : (𝟙⨯ g) ≫ (h ⨯𝟙) = (h ⨯𝟙) ≫ (𝟙⨯ g) := by simp
  let eq₁ : (h ⨯𝟙) ≫ (hat _ g) = hc.χ (pullback.snd m (h ⨯𝟙)) :=
    have :  _ ≫ terminal.from U = terminal.from _ := by simp
    hc.uniq m' _ (this ▸ isChar ▸ IsPullback.flip pb_outer)
  by rw [hat, prod.map_id_comp, assoc, ← ε_dinaturality, ← assoc, eq₀, assoc, ← hat, eq₁]

end
end CategoryTheory
