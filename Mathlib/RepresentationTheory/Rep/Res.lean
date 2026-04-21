/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Restriction of representations
Given a group homomorphism `f : H →* G`, we have the restriction functor
`resFunctor f : Rep k G ⥤ Rep k H` which sends a `G`-representation `ρ` to the
`H`-representation `ρ.comp f`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe t w u v v1 v2

variable {k : Type u} [Semiring k] {G : Type v1} {H : Type v2} [Monoid G] [Monoid H]

open CategoryTheory

namespace Rep

/-- The restriction functor `Rep R G ⥤ Rep R H` for a subgroup `H` of `G`. -/
abbrev resFunctor (f : H →* G) : Rep.{t} k G ⥤ Rep k H where
  obj A := of (X := A.V) (A.ρ.comp f)
  map f' := ofHom ⟨f'.hom, fun h ↦ by simpa using f'.hom.2 (f h)⟩

/-- The restriction of `X : Rep k G` associated to a monoid homomorphism `f : H →* G` -/
abbrev res (f : H →* G) (M : Rep k G) := (resFunctor f).obj M

variable (f : H →* G) (M : Rep k G)

@[simp] lemma res_obj_ρ : (res f M).ρ = (M.ρ.comp f) := rfl

lemma coe_res_obj_ρ' (h : H) : (res f M).ρ h = M.ρ (f h) := rfl

lemma res_obj_V : (res f M).V = M.V := rfl

lemma res_map_hom_toLinearMap {M N : Rep k G} (p : M ⟶ N) :
    ((resFunctor f).map p).hom.toLinearMap = p.hom.toLinearMap := rfl

section

instance : (resFunctor (k := k) f).Faithful where
  map_injective h := by
    ext : 2
    rw [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff] at h
    simpa using h

/-- Morphism between `X Y : Rep k G` can be lifted from restrictions associated with `f : H →* G`
  when `f` is surjective. -/
abbrev liftHomOfSurj {X Y : Rep k G} (hf : Function.Surjective f) (f' : res f X ⟶ res f Y) :
    X ⟶ Y := ofHom ⟨f'.hom.toLinearMap, fun g ↦ by obtain ⟨h, rfl⟩ := hf g; simpa using f'.hom.2 h⟩

@[simp]
lemma liftHomOfSurj_toLinearMap {X Y : Rep k G} (hf : Function.Surjective f)
    (f' : res f X ⟶ res f Y) : (liftHomOfSurj f hf f').hom.toLinearMap =
      f'.hom.toLinearMap := rfl

lemma full_res (hf : (⇑f).Surjective) : (resFunctor (k := k) f).Full where
  map_surjective {X Y} f' := ⟨liftHomOfSurj f hf f', by
    ext : 2; rw [res_map_hom_toLinearMap, liftHomOfSurj_toLinearMap]⟩

instance : (resFunctor (k := k) f).Additive where
  map_add {_ _} _ _ := by
    ext : 2;
    simp only [add_hom, Representation.IntertwiningMap.add_toLinearMap]
    rfl

instance {k : Type u} [CommSemiring k] : (resFunctor (k := k) f).Linear k where
  map_smul {X Y} l r := by
    ext : 2;
    rw [smul_hom, Representation.IntertwiningMap.toLinearMap_smul,
      res_map_hom_toLinearMap, smul_hom, Representation.IntertwiningMap.toLinearMap_smul,
      res_map_hom_toLinearMap]

noncomputable section

variable {G : Type v} [Group G] (A : Rep k G) (S : Subgroup G)
  [S.Normal] [Representation.IsTrivial (A.ρ.comp S.subtype)]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
abbrev ofQuotient : Rep k (G ⧸ S) := Rep.of (A.ρ.ofQuotient S)

/-- A `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially induces a
`G ⧸ S`-representation on `A`, and composing this with the quotient map `G → G ⧸ S` gives the
original representation by definition. Useful for typechecking. -/
abbrev resOfQuotientIso [Representation.IsTrivial (A.ρ.comp S.subtype)] :
    (res (QuotientGroup.mk' S) (A.ofQuotient S)) ≅ A := Iso.refl _

end

end

end Rep
