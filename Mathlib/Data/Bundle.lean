/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module data.bundle
! leanprover-community/mathlib commit e473c3198bb41f68560cab68a0529c854b618833
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic

/-!
# Bundle

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
Basic data structure to implement fiber bundles, vector bundles (maybe fibrations?), etc. This file
should contain all possible results that do not involve any topology.

We represent a bundle `E` over a base space `B` as a dependent type `E : B → Type*`.

We define `bundle.total_space F E` to be the type of pairs `⟨b, x⟩`, where `b : B` and `x : E x`.
This type is isomorphic to `Σ x, E x` and uses an extra argument `F` for reasons explained below. In
general, the constructions of fiber bundles we will make will be of this form.

## Main Definitions

* `bundle.total_space` the total space of a bundle.
* `bundle.total_space.proj` the projection from the total space to the base space.
* `bundle.total_space.mk` the constructor for the total space.

## Implementation Notes

- We use a custom structure for the total space of a bundle instead of using a type synonym for the
  canonical disjoint union `Σ x, E x` because the total space usually has a different topology and
  Lean 4 `simp` fails to apply lemmas about `Σ x, E x` to elements of the total space.

- The definition of `bundle.total_space` has an unused argument `F`. The reason is that in some
  constructions (e.g., `bundle.continuous_linear_map.vector_bundle`) we need access to the atlas of
  trivializations of original fiber bundles to construct the topology on the total space of the new
  fiber bundle.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/


namespace Bundle

variable {B F : Type _} (E : B → Type _)

/-- `bundle.total_space E` is the total space of the bundle. It consists of pairs
`(proj : B, snd : E proj)`.
-/
@[ext]
structure TotalSpace (F : Type _) (E : B → Type _) where
  proj : B
  snd : E proj
#align bundle.total_space Bundle.TotalSpaceₓ

instance [Inhabited B] [Inhabited (E default)] : Inhabited (TotalSpace F E) :=
  ⟨⟨default, default⟩⟩

variable {E}

/-- `bundle.total_space.proj` is the canonical projection `bundle.total_space E → B` from the
total space to the base space. -/
add_decl_doc total_space.proj

-- this notation won't be used in the pretty-printer
scoped notation "π" => @Bundle.TotalSpace.proj _

-- TODO: try `abbrev` in Lean 4
scoped notation "total_space.mk'" F:arg => @Bundle.TotalSpace.mk _ F _

#print Bundle.TotalSpace.mk_cast /-
theorem TotalSpace.mk_cast {x x' : B} (h : x = x') (b : E x) :
    (total_space.mk' F) x' (cast (congr_arg E h) b) = TotalSpace.mk x b := by subst h; rfl
#align bundle.total_space.mk_cast Bundle.TotalSpace.mk_cast
-/

instance {x : B} : CoeTC (E x) (TotalSpace F E) :=
  ⟨TotalSpace.mk x⟩

@[simp]
theorem TotalSpace.coe_proj (x : B) (v : E x) : (v : TotalSpace F E).proj = x :=
  rfl
#align bundle.total_space.coe_proj Bundle.TotalSpaceₓ.coe_proj

@[simp]
theorem TotalSpace.coe_snd {x : B} {y : E x} : (y : TotalSpace F E).snd = y :=
  rfl
#align bundle.total_space.coe_snd Bundle.TotalSpaceₓ.coe_snd

theorem TotalSpace.coe_eq_mk {x : B} (v : E x) : (v : TotalSpace F E) = TotalSpace.mk x v :=
  rfl
#align bundle.total_space.coe_eq_mk Bundle.TotalSpaceₓ.coe_eq_mk

#print Bundle.TotalSpace.eta /-
theorem TotalSpace.eta (z : TotalSpace F E) : TotalSpace.mk z.proj z.2 = z := by cases z <;> rfl
#align bundle.total_space.eta Bundle.TotalSpace.eta
-/

notation:100 -- notation for the direct sum of two bundles over the same base
E₁ " ×ᵇ " E₂ => fun x => E₁ x × E₂ x

#print Bundle.Trivial /-
/-- `bundle.trivial B F` is the trivial bundle over `B` of fiber `F`. -/
@[reducible, nolint unused_arguments]
def Trivial (B : Type _) (F : Type _) : B → Type _ := fun _ => F
#align bundle.trivial Bundle.Trivial
-/

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def TotalSpace.trivialSnd (B : Type _) (F : Type _) : TotalSpace F (Bundle.Trivial B F) → F :=
  TotalSpace.snd
#align bundle.total_space.trivial_snd Bundle.TotalSpaceₓ.trivialSnd

/-- A trivial bundle is equivalent to the product `B × F`. -/
@[simps (config := { attrs := [`simp, `mfld_simps] })]
def TotalSpace.toProd (B F : Type _) : (TotalSpace F fun _ : B => F) ≃ B × F
    where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
#align bundle.total_space.to_prod Bundle.TotalSpaceₓ.toProd

section Pullback

variable {B' : Type _}

#print Bundle.Pullback /-
/-- The pullback of a bundle `E` over a base `B` under a map `f : B' → B`, denoted by `pullback f E`
or `f *ᵖ E`,  is the bundle over `B'` whose fiber over `b'` is `E (f b')`. -/
def Pullback (f : B' → B) (E : B → Type _) : B' → Type _ := fun x => E (f x)
#align bundle.pullback Bundle.Pullback
-/

notation f " *ᵖ " E:arg => Pullback f E

instance {f : B' → B} {x : B'} [Nonempty (E (f x))] : Nonempty ((f *ᵖ E) x) :=
  ‹Nonempty (E (f x))›

#print Bundle.pullbackTotalSpaceEmbedding /-
/-- Natural embedding of the total space of `f *ᵖ E` into `B' × total_space E`. -/
@[simp]
def pullbackTotalSpaceEmbedding (f : B' → B) : TotalSpace F (f *ᵖ E) → B' × TotalSpace F E :=
  fun z => (z.proj, TotalSpace.mk (f z.proj) z.2)
#align bundle.pullback_total_space_embedding Bundle.pullbackTotalSpaceEmbedding
-/

#print Bundle.Pullback.lift /-
/-- The base map `f : B' → B` lifts to a canonical map on the total spaces. -/
@[simps (config := { attrs := [`simp, `mfld_simps] })]
def Pullback.lift (f : B' → B) : TotalSpace F (f *ᵖ E) → TotalSpace F E := fun z => ⟨f z.proj, z.2⟩
#align bundle.pullback.lift Bundle.Pullback.lift
-/

#print Bundle.Pullback.lift_mk /-
@[simp, mfld_simps]
theorem Pullback.lift_mk (f : B' → B) (x : B') (y : E (f x)) :
    Pullback.lift f ((total_space.mk' F) x y) = ⟨f x, y⟩ :=
  rfl
#align bundle.pullback.lift_mk Bundle.Pullback.lift_mk
-/

end Pullback

section FiberStructures

#print Bundle.coe_snd_map_apply /-
@[simp]
theorem coe_snd_map_apply [∀ x, Add (E x)] (x : B) (v w : E x) :
    (↑(v + w) : TotalSpace F E).snd = (v : TotalSpace F E).snd + (w : TotalSpace F E).snd :=
  rfl
#align bundle.coe_snd_map_apply Bundle.coe_snd_map_apply
-/

#print Bundle.coe_snd_map_smul /-
@[simp]
theorem coe_snd_map_smul {R} [∀ x, SMul R (E x)] (x : B) (r : R) (v : E x) :
    (↑(r • v) : TotalSpace F E).snd = r • (v : TotalSpace F E).snd :=
  rfl
#align bundle.coe_snd_map_smul Bundle.coe_snd_map_smul
-/

end FiberStructures

end Bundle

