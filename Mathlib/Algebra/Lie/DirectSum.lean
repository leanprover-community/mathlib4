/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Basic

#align_import algebra.lie.direct_sum from "leanprover-community/mathlib"@"c0cc689babd41c0e9d5f02429211ffbe2403472a"

/-!
# Direct sums of Lie algebras and Lie modules

Direct sums of Lie algebras and Lie modules carry natural algebra and module structures.

## Tags

lie algebra, lie module, direct sum
-/


universe u v w w₁

namespace DirectSum

open DFinsupp

open scoped DirectSum

variable {R : Type u} {ι : Type v} [CommRing R]

section Modules

/-! The direct sum of Lie modules over a fixed Lie algebra carries a natural Lie module
structure. -/


variable {L : Type w₁} {M : ι → Type w}

variable [LieRing L] [LieAlgebra R L]

variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

variable [∀ i, LieRingModule L (M i)] [∀ i, LieModule R L (M i)]

instance : LieRingModule L (⨁ i, M i) where
  bracket x m := m.mapRange (fun i m' => ⁅x, m'⁆) fun i => lie_zero x
  add_lie x y m := by
    refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext`
    -- ⊢ ↑⁅x + y, m⁆ x✝ = ↑(⁅x, m⁆ + ⁅y, m⁆) x✝
    simp only [mapRange_apply, add_apply, add_lie]
    -- 🎉 no goals
  lie_add x m n := by
    refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext`
    -- ⊢ ↑⁅x, m + n⁆ x✝ = ↑(⁅x, m⁆ + ⁅x, n⁆) x✝
    simp only [mapRange_apply, add_apply, lie_add]
    -- 🎉 no goals
  leibniz_lie x y m := by
    refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext`
    -- ⊢ ↑⁅x, ⁅y, m⁆⁆ x✝ = ↑(⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆) x✝
    simp only [mapRange_apply, lie_lie, add_apply, sub_add_cancel]
    -- 🎉 no goals

@[simp]
theorem lie_module_bracket_apply (x : L) (m : ⨁ i, M i) (i : ι) : ⁅x, m⁆ i = ⁅x, m i⁆ :=
  mapRange_apply _ _ m i
#align direct_sum.lie_module_bracket_apply DirectSum.lie_module_bracket_apply

instance : LieModule R L (⨁ i, M i) where
  smul_lie t x m := by
    refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext i`
    -- ⊢ ↑⁅t • x, m⁆ x✝ = ↑(t • ⁅x, m⁆) x✝
    simp only [smul_lie, lie_module_bracket_apply, smul_apply]
    -- 🎉 no goals
  lie_smul t x m := by
    refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext i`
    -- ⊢ ↑⁅x, t • m⁆ x✝ = ↑(t • ⁅x, m⁆) x✝
    simp only [lie_smul, lie_module_bracket_apply, smul_apply]
    -- 🎉 no goals

variable (R ι L M)

/-- The inclusion of each component into a direct sum as a morphism of Lie modules. -/
def lieModuleOf [DecidableEq ι] (j : ι) : M j →ₗ⁅R,L⁆ ⨁ i, M i :=
  { lof R ι M j with
    map_lie' := fun {x m} => by
      refine' DFinsupp.ext fun i => _ -- Porting note: Originally `ext i`
      -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : …
      by_cases h : j = i
      -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : …
      · rw [← h]; simp
        -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : …
                  -- 🎉 no goals
      · simp [lof, lsingle, h] }
        -- 🎉 no goals
#align direct_sum.lie_module_of DirectSum.lieModuleOf

/-- The projection map onto one component, as a morphism of Lie modules. -/
def lieModuleComponent (j : ι) : (⨁ i, M i) →ₗ⁅R,L⁆ M j :=
  { component R ι M j with
    map_lie' := fun {x m} => by simp [component, lapply] }
                                -- 🎉 no goals
#align direct_sum.lie_module_component DirectSum.lieModuleComponent

end Modules

section Algebras

/-! The direct sum of Lie algebras carries a natural Lie algebra structure. -/


variable (L : ι → Type w)

variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

instance lieRing : LieRing (⨁ i, L i) :=
  { (inferInstance : AddCommGroup _) with
    bracket := zipWith (fun i => fun x y => ⁅x, y⁆) fun i => lie_zero 0
    add_lie := fun x y z => by
      refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext`
      -- ⊢ ↑⁅x + y, z⁆ x✝ = ↑(⁅x, z⁆ + ⁅y, z⁆) x✝
      simp only [zipWith_apply, add_apply, add_lie]
      -- 🎉 no goals
    lie_add := fun x y z => by
      refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext`
      -- ⊢ ↑⁅x, y + z⁆ x✝ = ↑(⁅x, y⁆ + ⁅x, z⁆) x✝
      simp only [zipWith_apply, add_apply, lie_add]
      -- 🎉 no goals
    lie_self := fun x => by
      refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext`
      -- ⊢ ↑⁅x, x⁆ x✝ = ↑0 x✝
      simp only [zipWith_apply, add_apply, lie_self, zero_apply]
      -- 🎉 no goals
    leibniz_lie := fun x y z => by
      refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext`
      -- ⊢ ↑⁅x, ⁅y, z⁆⁆ x✝ = ↑(⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆) x✝
      simp only [sub_apply, zipWith_apply, add_apply, zero_apply]
      -- ⊢ ⁅↑x x✝, ⁅↑y x✝, ↑z x✝⁆⁆ = ⁅⁅↑x x✝, ↑y x✝⁆, ↑z x✝⁆ + ⁅↑y x✝, ⁅↑x x✝, ↑z x✝⁆⁆
      apply leibniz_lie }
      -- 🎉 no goals
#align direct_sum.lie_ring DirectSum.lieRing

@[simp]
theorem bracket_apply (x y : ⨁ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ :=
  zipWith_apply _ _ x y i
#align direct_sum.bracket_apply DirectSum.bracket_apply

instance lieAlgebra : LieAlgebra R (⨁ i, L i) :=
  { (inferInstance : Module R _) with
    lie_smul := fun c x y => by
      refine' DFinsupp.ext fun _ => _ -- Porting note: Originally `ext`
      -- ⊢ ↑⁅x, c • y⁆ x✝ = ↑(c • ⁅x, y⁆) x✝
      simp only [zipWith_apply, smul_apply, bracket_apply, lie_smul] }
      -- 🎉 no goals
#align direct_sum.lie_algebra DirectSum.lieAlgebra

variable (R ι)

/-- The inclusion of each component into the direct sum as morphism of Lie algebras. -/
@[simps]
def lieAlgebraOf [DecidableEq ι] (j : ι) : L j →ₗ⁅R⁆ ⨁ i, L i :=
  { lof R ι L j with
    toFun := of L j
    map_lie' := fun {x y} => by
      refine' DFinsupp.ext fun i => _ -- Porting note: Originally `ext i`
      -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := ↑(of L j), map_add' := (_ : ∀ (x y : …
      by_cases h : j = i
      -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := ↑(of L j), map_add' := (_ : ∀ (x y : …
      · rw [← h]; simp [of, singleAddHom]
        -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := ↑(of L j), map_add' := (_ : ∀ (x y : …
                  -- 🎉 no goals
      · simp [of, singleAddHom, h] }
        -- 🎉 no goals
#align direct_sum.lie_algebra_of DirectSum.lieAlgebraOf

/-- The projection map onto one component, as a morphism of Lie algebras. -/
@[simps]
def lieAlgebraComponent (j : ι) : (⨁ i, L i) →ₗ⁅R⁆ L j :=
  { component R ι L j with
    toFun := component R ι L j
    map_lie' := fun {x y} => by simp [component, lapply] }
                                -- 🎉 no goals
#align direct_sum.lie_algebra_component DirectSum.lieAlgebraComponent

@[ext]
theorem lieAlgebra_ext {x y : ⨁ i, L i}
    (h : ∀ i, lieAlgebraComponent R ι L i x = lieAlgebraComponent R ι L i y) : x = y :=
  DFinsupp.ext h
#align direct_sum.lie_algebra_ext DirectSum.lieAlgebra_ext

theorem lie_of_of_ne [DecidableEq ι] {i j : ι} (hij : j ≠ i) (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = 0 := by
  apply lieAlgebra_ext R ι L; intro k
  -- ⊢ ∀ (i_1 : ι), ↑(lieAlgebraComponent R ι L i_1) ⁅↑(of L i) x, ↑(of L j) y⁆ = ↑ …
                              -- ⊢ ↑(lieAlgebraComponent R ι L k) ⁅↑(of L i) x, ↑(of L j) y⁆ = ↑(lieAlgebraComp …
  rw [LieHom.map_lie]
  -- ⊢ ⁅↑(lieAlgebraComponent R ι L k) (↑(of L i) x), ↑(lieAlgebraComponent R ι L k …
  simp only [of, singleAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lieAlgebraComponent_apply,
    component, lapply, LinearMap.coe_mk, AddHom.coe_mk, single_apply, LieHom.map_zero]
  by_cases hik : i = k
  -- ⊢ ⁅if h : i = k then (_ : i = k) ▸ x else 0, if h : j = k then (_ : j = k) ▸ y …
  · simp only [dif_neg, not_false_iff, lie_zero, hik.symm, hij]
    -- 🎉 no goals
  · simp only [dif_neg, not_false_iff, zero_lie, hik]
    -- 🎉 no goals
#align direct_sum.lie_of_of_ne DirectSum.lie_of_of_ne

theorem lie_of_of_eq [DecidableEq ι] {i j : ι} (hij : j = i) (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = of L i ⁅x, hij.recOn y⁆ := by
  have : of L j y = of L i (hij.recOn y) := Eq.rec (Eq.refl _) hij
  -- ⊢ ⁅↑(of L i) x, ↑(of L j) y⁆ = ↑(of L i) ⁅x, Eq.recOn hij y⁆
  rw [this, ← lieAlgebraOf_apply R ι L i ⁅x, hij.recOn y⁆, LieHom.map_lie, lieAlgebraOf_apply,
    lieAlgebraOf_apply]
#align direct_sum.lie_of_of_eq DirectSum.lie_of_of_eq

@[simp]
theorem lie_of [DecidableEq ι] {i j : ι} (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = if hij : j = i then lieAlgebraOf R ι L i ⁅x, hij.recOn y⁆ else 0 := by
  by_cases hij : j = i
  -- ⊢ ⁅↑(of L i) x, ↑(of L j) y⁆ = if hij : j = i then ↑(lieAlgebraOf R ι L i) ⁅x, …
  · simp only [lie_of_of_eq R ι L hij x y, hij, dif_pos, not_false_iff, lieAlgebraOf_apply]
    -- 🎉 no goals
  · simp only [lie_of_of_ne R ι L hij x y, hij, dif_neg, not_false_iff]
    -- 🎉 no goals
#align direct_sum.lie_of DirectSum.lie_of

variable {R L ι}

/-- Given a family of Lie algebras `L i`, together with a family of morphisms of Lie algebras
`f i : L i →ₗ⁅R⁆ L'` into a fixed Lie algebra `L'`, we have a natural linear map:
`(⨁ i, L i) →ₗ[R] L'`. If in addition `⁅f i x, f j y⁆ = 0` for any `x ∈ L i` and `y ∈ L j` (`i ≠ j`)
then this map is a morphism of Lie algebras. -/
@[simps]
def toLieAlgebra [DecidableEq ι] (L' : Type w₁) [LieRing L'] [LieAlgebra R L']
    (f : ∀ i, L i →ₗ⁅R⁆ L') (hf : ∀ i j : ι, i ≠ j → ∀ (x : L i) (y : L j), ⁅f i x, f j y⁆ = 0) :
    (⨁ i, L i) →ₗ⁅R⁆ L' :=
  { toModule R ι L' fun i => (f i : L i →ₗ[R] L') with
    toFun := toModule R ι L' fun i => (f i : L i →ₗ[R] L')
    map_lie' := fun {x y} => by
      let f' i := (f i : L i →ₗ[R] L')
      -- ⊢ AddHom.toFun { toAddHom := { toFun := ↑(toModule R ι L' fun i => ↑(f i)), ma …
      /- The goal is linear in `y`. We can use this to reduce to the case that `y` has only one
        non-zero component. -/
      suffices ∀ (i : ι) (y : L i),
          toModule R ι L' f' ⁅x, of L i y⁆ =
            ⁅toModule R ι L' f' x, toModule R ι L' f' (of L i y)⁆ by
        simp only [← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
        congr; clear y; ext i y; exact this i y
      -- Similarly, we can reduce to the case that `x` has only one non-zero component.
      suffices ∀ (i j) (y : L i) (x : L j),
          toModule R ι L' f' ⁅of L j x, of L i y⁆ =
            ⁅toModule R ι L' f' (of L j x), toModule R ι L' f' (of L i y)⁆ by
        intro i y
        rw [← lie_skew x, ← lie_skew (toModule R ι L' f' x)]
        simp only [LinearMap.map_neg, neg_inj, ← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
        congr; clear x; ext j x; exact this j i x y
      -- Tidy up and use `lie_of`.
      intro i j y x
      -- ⊢ ↑(toModule R ι L' f') ⁅↑(of L j) x, ↑(of L i) y⁆ = ⁅↑(toModule R ι L' f') (↑ …
      simp only [lie_of R, lieAlgebraOf_apply, LieHom.coe_toLinearMap, toAddMonoid_of,
        coe_toModule_eq_coe_toAddMonoid, LinearMap.toAddMonoidHom_coe]
      -- And finish with trivial case analysis.
      rcases eq_or_ne i j with (h | h)
      -- ⊢ ↑(toAddMonoid fun i => LinearMap.toAddMonoidHom ↑(f i)) (if h : i = j then ↑ …
      · have h' : f j (h.recOn y) = f i y := Eq.rec (Eq.refl _) h
        -- ⊢ ↑(toAddMonoid fun i => LinearMap.toAddMonoidHom ↑(f i)) (if h : i = j then ↑ …
        simp only [h, h', LieHom.coe_toLinearMap, dif_pos, LieHom.map_lie, toAddMonoid_of,
          LinearMap.toAddMonoidHom_coe]
      · simp only [h, hf j i h.symm x y, dif_neg, not_false_iff, AddMonoidHom.map_zero] }
        -- 🎉 no goals
#align direct_sum.to_lie_algebra DirectSum.toLieAlgebra

end Algebras

section Ideals

variable {L : Type w} [LieRing L] [LieAlgebra R L] (I : ι → LieIdeal R L)

/-- The fact that this instance is necessary seems to be a bug in typeclass inference. See
[this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/
Typeclass.20resolution.20under.20binders/near/245151099). -/
instance lieRingOfIdeals : LieRing (⨁ i, I i) :=
  DirectSum.lieRing fun i => ↥(I i)
#align direct_sum.lie_ring_of_ideals DirectSum.lieRingOfIdeals

/-- See `DirectSum.lieRingOfIdeals` comment. -/
instance lieAlgebraOfIdeals : LieAlgebra R (⨁ i, I i) :=
  DirectSum.lieAlgebra fun i => ↥(I i)
#align direct_sum.lie_algebra_of_ideals DirectSum.lieAlgebraOfIdeals

end Ideals

end DirectSum
