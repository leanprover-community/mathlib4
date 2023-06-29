/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module data.bundle
! leanprover-community/mathlib commit 9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Module.Basic

/-!
# Bundle
Basic data structure to implement fiber bundles, vector bundles (maybe fibrations?), etc. This file
should contain all possible results that do not involve any topology.

We represent a bundle `E` over a base space `B` as a dependent type `E : B → Type _`.

We provide a type synonym of `Σ x, E x` as `Bundle.TotalSpace E`, to be able to endow it with
a topology which is not the disjoint union topology `Sigma.TopologicalSpace`. In general, the
constructions of fiber bundles we will make will be of this form.

## Main Definitions

* `Bundle.TotalSpace` the total space of a bundle.
* `Bundle.TotalSpace.proj` the projection from the total space to the base space.
* `Bundle.totalSpaceMk` the constructor for the total space.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/


namespace Bundle

variable {B : Type _} (E : B → Type _)

/-- `Bundle.TotalSpace E` is the total space of the bundle `Σ x, E x`.
This type synonym is used to avoid conflicts with general sigma types.
-/
def TotalSpace :=
  Σx, E x
#align bundle.total_space Bundle.TotalSpace

instance [Inhabited B] [Inhabited (E default)] : Inhabited (TotalSpace E) :=
  ⟨⟨default, default⟩⟩

variable {E}

/-- `bundle.TotalSpace.proj` is the canonical projection `Bundle.TotalSpace E → B` from the
total space to the base space. -/
@[simp, reducible]
def TotalSpace.proj : TotalSpace E → B :=
  Sigma.fst
#align bundle.total_space.proj Bundle.TotalSpace.proj

/-- The canonical projection defining a bundle. -/
scoped notation:max "π" E':max => Bundle.TotalSpace.proj (E := E')

/-- Constructor for the total space of a bundle. -/
@[simp, reducible]
def totalSpaceMk (b : B) (a : E b) : Bundle.TotalSpace E :=
  ⟨b, a⟩
#align bundle.total_space_mk Bundle.totalSpaceMk

theorem TotalSpace.proj_mk {x : B} {y : E x} : (totalSpaceMk x y).proj = x :=
  rfl
#align bundle.total_space.proj_mk Bundle.TotalSpace.proj_mk

theorem sigma_mk_eq_totalSpaceMk {x : B} {y : E x} : Sigma.mk x y = totalSpaceMk x y :=
  rfl
#align bundle.sigma_mk_eq_total_space_mk Bundle.sigma_mk_eq_totalSpaceMk

theorem TotalSpace.mk_cast {x x' : B} (h : x = x') (b : E x) :
    totalSpaceMk x' (cast (congr_arg E h) b) = totalSpaceMk x b := by
  subst h
  rfl
#align bundle.total_space.mk_cast Bundle.TotalSpace.mk_cast

theorem TotalSpace.eta (z : TotalSpace E) : totalSpaceMk z.proj z.2 = z :=
  Sigma.eta z
#align bundle.total_space.eta Bundle.TotalSpace.eta

instance {x : B} : CoeTC (E x) (TotalSpace E) :=
  ⟨totalSpaceMk x⟩

-- porting note: removed simp attribute, variable as head symbol
theorem coe_fst (x : B) (v : E x) : (v : TotalSpace E).fst = x :=
  rfl
#align bundle.coe_fst Bundle.coe_fst

-- porting note: removed simp attribute, variable as head symbol
theorem coe_snd {x : B} {y : E x} : (y : TotalSpace E).snd = y :=
  rfl
#align bundle.coe_snd Bundle.coe_snd

-- porting note: removed `to_total_space_coe`, syntactic tautology
#noalign bundle.to_total_space_coe

-- mathport name: «expr ×ᵇ »
/-- The direct sum of two bundles. -/
notation:100 -- notation for the direct sum of two bundles over the same base
E₁ " ×ᵇ " E₂ => fun x => E₁ x × E₂ x

/-- `Bundle.Trivial B F` is the trivial bundle over `B` of fiber `F`. -/
def Trivial (B : Type _) (F : Type _) : B → Type _ :=
  Function.const B F
#align bundle.trivial Bundle.Trivial

instance {F : Type _} [Inhabited F] {b : B} : Inhabited (Bundle.Trivial B F b) :=
  ⟨(default : F)⟩

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def Trivial.projSnd (B : Type _) (F : Type _) : TotalSpace (Bundle.Trivial B F) → F :=
  Sigma.snd
#align bundle.trivial.proj_snd Bundle.Trivial.projSnd

section Pullback

variable {B' : Type _}

/-- The pullback of a bundle `E` over a base `B` under a map `f : B' → B`, denoted by `Pullback f E`
or `f *ᵖ E`,  is the bundle over `B'` whose fiber over `b'` is `E (f b')`. -/
-- porting note: `has_nonempty_instance` linter not found
--  @[nolint has_nonempty_instance]
def Pullback (f : B' → B) (E : B → Type _) := fun x => E (f x)
#align bundle.pullback Bundle.Pullback

-- mathport name: «expr *ᵖ »
@[inherit_doc]
notation f " *ᵖ " E => Pullback f E

/-- Natural embedding of the total space of `f *ᵖ E` into `B' × TotalSpace E`. -/
@[simp]
def pullbackTotalSpaceEmbedding (f : B' → B) : TotalSpace (f *ᵖ E) → B' × TotalSpace E := fun z =>
  (z.proj, totalSpaceMk (f z.proj) z.2)
#align bundle.pullback_total_space_embedding Bundle.pullbackTotalSpaceEmbedding

/-- The base map `f : B' → B` lifts to a canonical map on the total spaces. -/
def Pullback.lift (f : B' → B) : TotalSpace (f *ᵖ E) → TotalSpace E := fun z =>
  totalSpaceMk (f z.proj) z.2
#align bundle.pullback.lift Bundle.Pullback.lift

@[simp]
theorem Pullback.proj_lift (f : B' → B) (x : TotalSpace (f *ᵖ E)) :
    (Pullback.lift f x).proj = f x.1 :=
  rfl
#align bundle.pullback.proj_lift Bundle.Pullback.proj_lift

@[simp]
theorem Pullback.lift_mk (f : B' → B) (x : B') (y : E (f x)) :
    Pullback.lift f (totalSpaceMk x y) = totalSpaceMk (f x) y :=
  rfl
#align bundle.pullback.lift_mk Bundle.Pullback.lift_mk

theorem pullbackTotalSpaceEmbedding_snd (f : B' → B) (x : TotalSpace (f *ᵖ E)) :
    (pullbackTotalSpaceEmbedding f x).2 = Pullback.lift f x :=
  rfl
#align bundle.pullback_total_space_embedding_snd Bundle.pullbackTotalSpaceEmbedding_snd

end Pullback

section FiberStructures

variable [∀ x, AddCommMonoid (E x)]

@[simp]
theorem coe_snd_map_apply (x : B) (v w : E x) :
    (↑(v + w) : TotalSpace E).snd = (v : TotalSpace E).snd + (w : TotalSpace E).snd :=
  rfl
#align bundle.coe_snd_map_apply Bundle.coe_snd_map_apply

variable (R : Type _) [Semiring R] [∀ x, Module R (E x)]

@[simp]
theorem coe_snd_map_smul (x : B) (r : R) (v : E x) :
    (↑(r • v) : TotalSpace E).snd = r • (v : TotalSpace E).snd :=
  rfl
#align bundle.coe_snd_map_smul Bundle.coe_snd_map_smul

end FiberStructures

section TrivialInstances

variable {F : Type _} {R : Type _} [Semiring R] (b : B)

instance [AddCommMonoid F] : AddCommMonoid (Bundle.Trivial B F b) :=
  ‹AddCommMonoid F›

instance [AddCommGroup F] : AddCommGroup (Bundle.Trivial B F b) :=
  ‹AddCommGroup F›

instance [AddCommMonoid F] [Module R F] : Module R (Bundle.Trivial B F b) :=
  ‹Module R F›
