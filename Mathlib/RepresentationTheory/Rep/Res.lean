/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RepresentationTheory.Rep.Iso
/-!
# Restriction of representations
Given a group homomorphism `f : H →* G`, we have the restriction functor
`resFunctor f : Rep k G ⥤ Rep k H` which sends a `G`-representation `ρ` to the
`H`-representation `ρ.comp f`.

-/

public section

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

lemma res_id : res (MonoidHom.id G) M = M := rfl

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

section ShortComplex

open Limits

variable {k : Type u} [Ring k]

instance : PreservesLimits (resFunctor.{w} (k := k) f) :=
  have : PreservesLimitsOfSize.{w, w} (resFunctor f ⋙ forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))

instance : Limits.PreservesColimits (resFunctor.{w} (k := k) f) :=
  have : PreservesColimitsOfSize.{w, w} (resFunctor (k := k) f ⋙
      forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesColimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))

/-- An object of `Rep k G` is zero iff its restriction to `H` is zero. -/
lemma isZero_res_iff (M : Rep k G) :
    IsZero (res f M) ↔ IsZero M := by
  rw [isZero_iff, isZero_iff, Rep.res_obj_V]

/--
The instances above show that the restriction functor `res φ : Rep R G ⥤ Rep R H`
preserves and reflects exactness. -/
lemma res_map_exact {k : Type u} [CommRing k]
    (S : ShortComplex (Rep.{w} k G)) :
    (S.map (resFunctor f)).Exact ↔ S.Exact := by
  rw [ShortComplex.exact_map_iff_of_faithful]

lemma shortExact_res {k : Type u} [CommRing k] (φ : H →* G) {S : ShortComplex (Rep.{w} k G)} :
    (S.map (resFunctor φ)).ShortExact ↔ S.ShortExact := by
  constructor
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    rw [ShortComplex.exact_map_iff_of_faithful] at h₁
    simp only [ShortComplex.map_f, Representation.IntertwiningMap.coe_eq_toLinearMap,
      mono_iff_injective, ShortComplex.map_g, epi_iff_surjective] at h₂ h₃
    exact {exact := h₁, mono_f := mono_iff_injective _|>.2 h₂, epi_g := epi_iff_surjective _|>.2 h₃}
  · rintro ⟨h⟩
    expose_names
    exact {
      exact := by rwa [ShortComplex.exact_map_iff_of_faithful]
      mono_f := by simpa [mono_iff_injective] using! mono_f
      epi_g := by simpa [epi_iff_surjective] using! epi_g
    }

end ShortComplex

noncomputable section

variable {G : Type v} [Group G] (A : Rep k G) (S : Subgroup G)
  [S.Normal] [Representation.IsTrivial (A.ρ.comp S.subtype)]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
abbrev ofQuotient : Rep k (G ⧸ S) := Rep.of (A.ρ.ofQuotient S)

/-- A `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially induces a
`G ⧸ S`-representation on `A`, and composing this with the quotient map `G → G ⧸ S` gives the
original representation by definition. Useful for typechecking. -/
abbrev resOfQuotientIso : (res (QuotientGroup.mk' S) (A.ofQuotient S)) ≅ A := Iso.refl _

end

end

end Rep
