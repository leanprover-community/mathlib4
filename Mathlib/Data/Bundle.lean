/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Data.Set.Basic

#align_import data.bundle from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Bundle
Basic data structure to implement fiber bundles, vector bundles (maybe fibrations?), etc. This file
should contain all possible results that do not involve any topology.

We represent a bundle `E` over a base space `B` as a dependent type `E : B → Type*`.

We define `Bundle.TotalSpace F E` to be the type of pairs `⟨b, x⟩`, where `b : B` and `x : E b`.
This type is isomorphic to `Σ x, E x` and uses an extra argument `F` for reasons explained below. In
general, the constructions of fiber bundles we will make will be of this form.

## Main Definitions

* `Bundle.TotalSpace` the total space of a bundle.
* `Bundle.TotalSpace.proj` the projection from the total space to the base space.
* `Bundle.TotalSpace.mk` the constructor for the total space.

## Implementation Notes

- We use a custom structure for the total space of a bundle instead of using a type synonym for the
  canonical disjoint union `Σ x, E x` because the total space usually has a different topology and
  Lean 4 `simp` fails to apply lemmas about `Σ x, E x` to elements of the total space.

- The definition of `Bundle.TotalSpace` has an unused argument `F`. The reason is that in some
  constructions (e.g., `Bundle.ContinuousLinearMap.vectorBundle`) we need access to the atlas of
  trivializations of original fiber bundles to construct the topology on the total space of the new
  fiber bundle.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/

open Function Set

namespace Bundle

variable {B F : Type*} (E : B → Type*)

/-- `Bundle.TotalSpace F E` is the total space of the bundle. It consists of pairs
`(proj : B, snd : E proj)`.
-/
@[ext]
structure TotalSpace (F : Type*) (E : B → Type*) where
  /-- `Bundle.TotalSpace.proj` is the canonical projection `Bundle.TotalSpace F E → B` from the
  total space to the base space. -/
  proj : B
  snd : E proj
#align bundle.total_space Bundle.TotalSpace

instance [Inhabited B] [Inhabited (E default)] : Inhabited (TotalSpace F E) :=
  ⟨⟨default, default⟩⟩

variable {E}

@[inherit_doc]
scoped notation:max "π" F':max E':max => Bundle.TotalSpace.proj (F := F') (E := E')

abbrev TotalSpace.mk' (F : Type*) (x : B) (y : E x) : TotalSpace F E := ⟨x, y⟩

theorem TotalSpace.mk_cast {x x' : B} (h : x = x') (b : E x) :
    .mk' F x' (cast (congr_arg E h) b) = TotalSpace.mk x b := by subst h; rfl
#align bundle.total_space.mk_cast Bundle.TotalSpace.mk_cast

@[simp 1001, mfld_simps 1001]
theorem TotalSpace.mk_inj {b : B} {y y' : E b} : mk' F b y = mk' F b y' ↔ y = y' := by
  simp [TotalSpace.ext_iff]

theorem TotalSpace.mk_injective (b : B) : Injective (mk b : E b → TotalSpace F E) := fun _ _ ↦
  mk_inj.1

instance {x : B} : CoeTC (E x) (TotalSpace F E) :=
  ⟨TotalSpace.mk x⟩

#noalign bundle.total_space.coe_proj
#noalign bundle.total_space.coe_snd
#noalign bundle.total_space.coe_eq_mk

theorem TotalSpace.eta (z : TotalSpace F E) : TotalSpace.mk z.proj z.2 = z := rfl
#align bundle.total_space.eta Bundle.TotalSpace.eta

@[simp]
theorem TotalSpace.exists {p : TotalSpace F E → Prop} : (∃ x, p x) ↔ ∃ b y, p ⟨b, y⟩ :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨x.1, x.2, hx⟩, fun ⟨b, y, h⟩ ↦ ⟨⟨b, y⟩, h⟩⟩

@[simp]
theorem TotalSpace.range_mk (b : B) : range ((↑) : E b → TotalSpace F E) = π F E ⁻¹' {b} := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    rfl
  · rintro ⟨_, x⟩ rfl
    exact ⟨x, rfl⟩

/-- Notation for the direct sum of two bundles over the same base. -/
notation:100 E₁ " ×ᵇ " E₂ => fun x => E₁ x × E₂ x

/-- `Bundle.Trivial B F` is the trivial bundle over `B` of fiber `F`. -/
@[reducible, nolint unusedArguments]
def Trivial (B : Type*) (F : Type*) : B → Type _ := fun _ => F
#align bundle.trivial Bundle.Trivial

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def TotalSpace.trivialSnd (B : Type*) (F : Type*) : TotalSpace F (Bundle.Trivial B F) → F :=
  TotalSpace.snd
#align bundle.total_space.trivial_snd Bundle.TotalSpace.trivialSnd

/-- A trivial bundle is equivalent to the product `B × F`. -/
@[simps (config := { attrs := [`mfld_simps] })]
def TotalSpace.toProd (B F : Type*) : (TotalSpace F fun _ : B => F) ≃ B × F where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
#align bundle.total_space.to_prod Bundle.TotalSpace.toProd

section Pullback

variable {B' : Type*}

/-- The pullback of a bundle `E` over a base `B` under a map `f : B' → B`, denoted by
`Bundle.Pullback f E` or `f *ᵖ E`, is the bundle over `B'` whose fiber over `b'` is `E (f b')`. -/
def Pullback (f : B' → B) (E : B → Type*) : B' → Type _ := fun x => E (f x)
#align bundle.pullback Bundle.Pullback

@[inherit_doc]
notation f " *ᵖ " E:arg => Pullback f E

instance {f : B' → B} {x : B'} [Nonempty (E (f x))] : Nonempty ((f *ᵖ E) x) :=
  ‹Nonempty (E (f x))›

/-- Natural embedding of the total space of `f *ᵖ E` into `B' × TotalSpace F E`. -/
@[simp]
def pullbackTotalSpaceEmbedding (f : B' → B) : TotalSpace F (f *ᵖ E) → B' × TotalSpace F E :=
  fun z => (z.proj, TotalSpace.mk (f z.proj) z.2)
#align bundle.pullback_total_space_embedding Bundle.pullbackTotalSpaceEmbedding

/-- The base map `f : B' → B` lifts to a canonical map on the total spaces. -/
@[simps (config := { attrs := [`mfld_simps] })]
def Pullback.lift (f : B' → B) : TotalSpace F (f *ᵖ E) → TotalSpace F E := fun z => ⟨f z.proj, z.2⟩
#align bundle.pullback.lift Bundle.Pullback.lift

@[simp, mfld_simps]
theorem Pullback.lift_mk (f : B' → B) (x : B') (y : E (f x)) :
    Pullback.lift f (.mk' F x y) = ⟨f x, y⟩ :=
  rfl
#align bundle.pullback.lift_mk Bundle.Pullback.lift_mk

end Pullback

-- Porting note: not needed since Lean unfolds coercion
#noalign bundle.coe_snd_map_apply
#noalign bundle.coe_snd_map_smul

end Bundle
