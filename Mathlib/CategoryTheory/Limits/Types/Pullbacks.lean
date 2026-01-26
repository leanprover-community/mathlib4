/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Pullbacks in the category of types

In `Type*`, the pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the
subtype `{ p : X × Y // f p.1 = g p.2 }` of the product.
We show some additional lemmas for pullbacks in the category of types.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Limits.Types

-- #synth HasPullbacks.{u} (Type u)
instance : HasPullbacks.{u} (Type u) :=
  -- FIXME does not work via `inferInstance` despite `#synth HasPullbacks.{u} (Type u)` succeeding.
  -- https://github.com/leanprover-community/mathlib4/issues/5752
  -- inferInstance
  hasPullbacks_of_hasWidePullbacks.{u} (Type u)

variable {X Y Z : Type u} {X' Y' Z' : Type v}
variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z')

/-- The usual explicit pullback in the category of types, as a subtype of the product.
The full `LimitCone` data is bundled as `pullbackLimitCone f g`.
-/
abbrev PullbackObj : Type u :=
  { p : X × Y // f p.1 = g p.2 }

-- `PullbackObj f g` comes with a coercion to the product type `X × Y`.
example (p : PullbackObj f g) : X × Y :=
  p

/-- The explicit pullback cone on `PullbackObj f g`.
This is bundled with the `IsLimit` data as `pullbackLimitCone f g`.
-/
abbrev pullbackCone : Limits.PullbackCone f g :=
  PullbackCone.mk (fun p : PullbackObj f g => p.1.1) (fun p => p.1.2) (funext fun p => p.2)

/-- The explicit pullback in the category of types, bundled up as a `LimitCone`
for given `f` and `g`.
-/
@[simps]
def pullbackLimitCone (f : X ⟶ Z) (g : Y ⟶ Z) : Limits.LimitCone (cospan f g) where
  cone := pullbackCone f g
  isLimit :=
    PullbackCone.isLimitAux _ (fun s x => ⟨⟨s.fst x, s.snd x⟩, congr_fun s.condition x⟩)
      (by aesop) (by aesop) fun _ _ w =>
      funext fun x =>
        Subtype.ext <|
          Prod.ext (congr_fun (w WalkingCospan.left) x) (congr_fun (w WalkingCospan.right) x)

end Types

namespace PullbackCone

variable {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : PullbackCone f g}

namespace IsLimit

variable (hc : IsLimit c)

/-- A limit pullback cone in the category of types identifies to the explicit pullback. -/
noncomputable def equivPullbackObj : c.pt ≃ Types.PullbackObj f g :=
  (IsLimit.conePointUniqueUpToIso hc (Types.pullbackLimitCone f g).isLimit).toEquiv

@[simp]
lemma equivPullbackObj_apply_fst (x : c.pt) : (equivPullbackObj hc x).1.1 = c.fst x :=
  congr_fun (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .left) x

@[simp]
lemma equivPullbackObj_apply_snd (x : c.pt) : (equivPullbackObj hc x).1.2 = c.snd x :=
  congr_fun (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .right) x

@[simp]
lemma equivPullbackObj_symm_apply_fst (x : Types.PullbackObj f g) :
    c.fst ((equivPullbackObj hc).symm x) = x.1.1 := by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

@[simp]
lemma equivPullbackObj_symm_apply_snd (x : Types.PullbackObj f g) :
    c.snd ((equivPullbackObj hc).symm x) = x.1.2 := by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

include hc in
lemma type_ext {x y : c.pt} (h₁ : c.fst x = c.fst y) (h₂ : c.snd x = c.snd y) : x = y :=
  (equivPullbackObj hc).injective (by ext <;> assumption)

end IsLimit

variable (c)

/-- Given `c : PullbackCone f g` in the category of types, this is
the canonical map `c.pt → Types.PullbackObj f g`. -/
@[simps coe_fst coe_snd]
def toPullbackObj (x : c.pt) : Types.PullbackObj f g :=
  ⟨⟨c.fst x, c.snd x⟩, congr_fun c.condition x⟩

/-- A pullback cone `c` in the category of types is limit iff the
map `c.toPullbackObj : c.pt → Types.PullbackObj f g` is a bijection. -/
noncomputable def isLimitEquivBijective :
    IsLimit c ≃ Function.Bijective c.toPullbackObj where
  toFun h := (IsLimit.equivPullbackObj h).bijective
  invFun h := IsLimit.ofIsoLimit (Types.pullbackLimitCone f g).isLimit
    (Iso.symm (PullbackCone.ext (Equiv.ofBijective _ h).toIso))
  left_inv _ := Subsingleton.elim _ _

end PullbackCone

namespace Types

section Pullback

open CategoryTheory.Limits.WalkingCospan

variable {W X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The pullback given by the instance `HasPullbacks (Type u)` is isomorphic to the
explicit pullback object given by `PullbackObj`.
-/
noncomputable def pullbackIsoPullback : pullback f g ≅ PullbackObj f g :=
  (PullbackCone.IsLimit.equivPullbackObj (pullbackIsPullback f g)).toIso

@[simp]
theorem pullbackIsoPullback_hom_fst (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).fst = (pullback.fst f g) p :=
  PullbackCone.IsLimit.equivPullbackObj_apply_fst (pullbackIsPullback f g) p

@[simp]
theorem pullbackIsoPullback_hom_snd (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).snd = (pullback.snd f g) p :=
  PullbackCone.IsLimit.equivPullbackObj_apply_snd (pullbackIsPullback f g) p

@[simp]
theorem pullbackIsoPullback_inv_fst_apply (x : (Types.pullbackCone f g).pt) :
    (pullback.fst f g) ((pullbackIsoPullback f g).inv x) = (fun p => (p.1 : X × Y).fst) x :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (pullbackIsPullback f g) x

@[simp]
theorem pullbackIsoPullback_inv_snd_apply (x : (Types.pullbackCone f g).pt) :
    (pullback.snd f g) ((pullbackIsoPullback f g).inv x) = (fun p => (p.1 : X × Y).snd) x :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (pullbackIsPullback f g) x

@[simp]
theorem pullbackIsoPullback_inv_fst :
    (pullbackIsoPullback f g).inv ≫ pullback.fst _ _ = fun p => (p.1 : X × Y).fst := by aesop

@[simp]
theorem pullbackIsoPullback_inv_snd :
    (pullbackIsoPullback f g).inv ≫ pullback.snd _ _ = fun p => (p.1 : X × Y).snd := by aesop

end Pullback

end Types

end CategoryTheory.Limits


namespace CategoryTheory.Limits.Types

variable {P X Y Z : Type u} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

lemma range_fst_of_isPullback (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  let e := h.isoPullback ≪≫ Types.pullbackIsoPullback f g
  have : fst = _root_.Prod.fst ∘ Subtype.val ∘ e.hom := by
    ext p
    suffices fst p = pullback.fst f g (h.isoPullback.hom p) by simpa
    rw [← types_comp_apply h.isoPullback.hom (pullback.fst f g), IsPullback.isoPullback_hom_fst]
  rw [this, Set.range_comp, Set.range_comp, Set.range_eq_univ.mpr (surjective_of_epi e.hom)]
  ext
  simp [eq_comm]

lemma range_snd_of_isPullback (h : IsPullback fst snd f g) :
    Set.range snd = g ⁻¹' Set.range f := by
  rw [range_fst_of_isPullback (IsPullback.flip h)]

variable (f g)

@[simp]
lemma range_pullbackFst : Set.range (pullback.fst f g) = f ⁻¹' Set.range g :=
  range_fst_of_isPullback (.of_hasPullback f g)

@[simp]
lemma range_pullbackSnd : Set.range (pullback.snd f g) = g ⁻¹' Set.range f :=
  range_snd_of_isPullback (.of_hasPullback f g)

section

variable {X₁ X₂ X₃ X₄ : Type u} {t : X₁ ⟶ X₂} {r : X₂ ⟶ X₄}
  {l : X₁ ⟶ X₃} {b : X₃ ⟶ X₄}

lemma ext_of_isPullback (h : IsPullback t l r b) {x₁ y₁ : X₁}
    (h₁ : t x₁ = t y₁) (h₂ : l x₁ = l y₁) : x₁ = y₁ :=
  (h.isLimit.conePointUniqueUpToIso (Types.pullbackLimitCone _ _).isLimit).toEquiv.injective
    (by dsimp; ext <;> assumption)

lemma exists_of_isPullback (h : IsPullback t l r b)
    (x₂ : X₂) (x₃ : X₃) (hx : r x₂ = b x₃) :
    ∃ x₁, t x₁ = x₂ ∧ l x₁ = x₃ := by
  obtain ⟨x₁, hx₁⟩ :=
    (PullbackCone.IsLimit.equivPullbackObj h.isLimit).surjective ⟨⟨x₂, x₃⟩, hx⟩
  rw [Subtype.ext_iff] at hx₁
  exact ⟨x₁, congr_arg _root_.Prod.fst hx₁,
    congr_arg _root_.Prod.snd hx₁⟩

variable (t l r b) in
lemma isPullback_iff :
  IsPullback t l r b ↔ t ≫ r = l ≫ b ∧
    (∀ x₁ y₁, t x₁ = t y₁ ∧ l x₁ = l y₁ → x₁ = y₁) ∧
    ∀ x₂ x₃, r x₂ = b x₃ → ∃ x₁, t x₁ = x₂ ∧ l x₁ = x₃ := by
  constructor
  · intro h
    exact ⟨h.w, fun x₁ y₁ ⟨h₁, h₂⟩ ↦ ext_of_isPullback h h₁ h₂, exists_of_isPullback h⟩
  · rintro ⟨w, h₁, h₂⟩
    let φ : X₁ ⟶ PullbackObj r b := fun x₁ ↦ ⟨⟨t x₁, l x₁⟩, congr_fun w x₁⟩
    have hφ : IsIso φ := by
      rw [isIso_iff_bijective]
      grind [Function.Bijective, Function.Injective, Function.Surjective]
    exact ⟨⟨w⟩, ⟨IsLimit.ofIsoLimit ((Types.pullbackLimitCone r b).isLimit)
      (PullbackCone.ext (asIso φ)).symm⟩⟩

end

end CategoryTheory.Limits.Types
