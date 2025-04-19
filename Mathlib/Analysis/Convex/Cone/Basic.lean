/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Convex cones

In a `𝕜`-module `E`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
`x, y ∈ s` and `a, b > 0`. We prove that convex cones form a `CompleteLattice`, and define their
images (`ConvexCone.map`) and preimages (`ConvexCone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We define `Convex.toCone` to be the minimal cone that includes a given convex set.

## Main statements

In `Mathlib/Analysis/Convex/Cone/Extension.lean` we prove
the M. Riesz extension theorem and a form of the Hahn-Banach theorem.

In `Mathlib/Analysis/Convex/Cone/Dual.lean` we prove
a variant of the hyperplane separation theorem.

## Implementation notes

While `Convex 𝕜` is a predicate on sets, `ConvexCone 𝕜 E` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
* [Stephen P. Boyd and Lieven Vandenberghe, *Convex Optimization*][boydVandenberghe2004]
* [Emo Welzl and Bernd Gärtner, *Cone Programming*][welzl_garter]
-/


assert_not_exists NormedSpace Real Cardinal

open Set LinearMap Pointwise

variable {𝕜 E F G : Type*}

/-! ### Definition of `ConvexCone` and basic properties -/

section Definitions

variable (𝕜 E)
variable [Semiring 𝕜] [PartialOrder 𝕜]

-- TODO: remove `[IsOrderedRing 𝕜]`.
/-- A convex cone is a subset `s` of a `𝕜`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
structure ConvexCone [IsOrderedRing 𝕜] [AddCommMonoid E] [SMul 𝕜 E] where
  /-- The **carrier set** underlying this cone: the set of points contained in it -/
  carrier : Set E
  smul_mem' : ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ carrier → c • x ∈ carrier
  add_mem' : ∀ ⦃x⦄ (_ : x ∈ carrier) ⦃y⦄ (_ : y ∈ carrier), x + y ∈ carrier

end Definitions

namespace ConvexCone

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E]

section SMul

variable [SMul 𝕜 E] (S T : ConvexCone 𝕜 E)

instance : SetLike (ConvexCone 𝕜 E) E where
  coe := carrier
  coe_injective' S T h := by cases S; cases T; congr

@[simp]
theorem coe_mk {s : Set E} {h₁ h₂} : ↑(mk (𝕜 := 𝕜) s h₁ h₂) = s :=
  rfl

@[simp]
theorem mem_mk {s : Set E} {h₁ h₂ x} : x ∈ mk (𝕜 := 𝕜) s h₁ h₂ ↔ x ∈ s :=
  Iff.rfl

/-- Two `ConvexCone`s are equal if they have the same elements. -/
@[ext]
theorem ext {S T : ConvexCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[aesop safe apply (rule_sets := [SetLike])]
theorem smul_mem {c : 𝕜} {x : E} (hc : 0 < c) (hx : x ∈ S) : c • x ∈ S :=
  S.smul_mem' hc hx

theorem add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S :=
  S.add_mem' hx hy

instance : AddMemClass (ConvexCone 𝕜 E) E where add_mem ha hb := add_mem _ ha hb

instance : Min (ConvexCone 𝕜 E) :=
  ⟨fun S T =>
    ⟨S ∩ T, fun _ hc _ hx => ⟨S.smul_mem hc hx.1, T.smul_mem hc hx.2⟩, fun _ hx _ hy =>
      ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩⟩⟩

@[simp]
theorem coe_inf : ((S ⊓ T : ConvexCone 𝕜 E) : Set E) = ↑S ∩ ↑T :=
  rfl

theorem mem_inf {x} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

instance : InfSet (ConvexCone 𝕜 E) :=
  ⟨fun S =>
    ⟨⋂ s ∈ S, ↑s, fun _ hc _ hx => mem_biInter fun s hs => s.smul_mem hc <| mem_iInter₂.1 hx s hs,
      fun _ hx _ hy =>
      mem_biInter fun s hs => s.add_mem (mem_iInter₂.1 hx s hs) (mem_iInter₂.1 hy s hs)⟩⟩

@[simp]
theorem coe_sInf (S : Set (ConvexCone 𝕜 E)) : ↑(sInf S) = ⋂ s ∈ S, (s : Set E) :=
  rfl

theorem mem_sInf {x : E} {S : Set (ConvexCone 𝕜 E)} : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s :=
  mem_iInter₂

@[simp]
theorem coe_iInf {ι : Sort*} (f : ι → ConvexCone 𝕜 E) : ↑(iInf f) = ⋂ i, (f i : Set E) := by
  simp [iInf]

theorem mem_iInf {ι : Sort*} {x : E} {f : ι → ConvexCone 𝕜 E} : x ∈ iInf f ↔ ∀ i, x ∈ f i :=
  mem_iInter₂.trans <| by simp

variable (𝕜)

instance : Bot (ConvexCone 𝕜 E) :=
  ⟨⟨∅, fun _ _ _ => False.elim, fun _ => False.elim⟩⟩

theorem mem_bot (x : E) : (x ∈ (⊥ : ConvexCone 𝕜 E)) = False :=
  rfl

@[simp]
theorem coe_bot : ↑(⊥ : ConvexCone 𝕜 E) = (∅ : Set E) :=
  rfl

instance : Top (ConvexCone 𝕜 E) :=
  ⟨⟨univ, fun _ _ _ _ => mem_univ _, fun _ _ _ _ => mem_univ _⟩⟩

theorem mem_top (x : E) : x ∈ (⊤ : ConvexCone 𝕜 E) :=
  mem_univ x

@[simp]
theorem coe_top : ↑(⊤ : ConvexCone 𝕜 E) = (univ : Set E) :=
  rfl

instance : CompleteLattice (ConvexCone 𝕜 E) :=
  { SetLike.instPartialOrder with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun _ _ => False.elim
    top := ⊤
    le_top := fun _ x _ => mem_top 𝕜 x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    sup := fun a b => sInf { x | a ≤ x ∧ b ≤ x }
    sSup := fun s => sInf { T | ∀ S ∈ s, S ≤ T }
    le_sup_left := fun _ _ => fun _ hx => mem_sInf.2 fun _ hs => hs.1 hx
    le_sup_right := fun _ _ => fun _ hx => mem_sInf.2 fun _ hs => hs.2 hx
    sup_le := fun _ _ c ha hb _ hx => mem_sInf.1 hx c ⟨ha, hb⟩
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_sSup := fun _ p hs _ hx => mem_sInf.2 fun _ ht => ht p hs hx
    sSup_le := fun _ p hs _ hx => mem_sInf.1 hx p hs
    le_sInf := fun _ _ ha _ hx => mem_sInf.2 fun t ht => ha t ht hx
    sInf_le := fun _ _ ha _ hx => mem_sInf.1 hx _ ha }

instance : Inhabited (ConvexCone 𝕜 E) :=
  ⟨⊥⟩

end SMul

section Module

variable [Module 𝕜 E] (S : ConvexCone 𝕜 E)

protected theorem convex : Convex 𝕜 (S : Set E) :=
  convex_iff_forall_pos.2 fun _ hx _ hy _ _ ha hb _ =>
    S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

end Module

section Maps

variable [AddCommMonoid F] [AddCommMonoid G]
variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]

/-- The image of a convex cone under a `𝕜`-linear map is a convex cone. -/
def map (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 E) : ConvexCone 𝕜 F where
  carrier := f '' S
  smul_mem' := fun c hc _ ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (S.smul_mem hc hx)
  add_mem' := fun _ ⟨x₁, hx₁, hy₁⟩ _ ⟨x₂, hx₂, hy₂⟩ =>
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (S.add_mem hx₁ hx₂)

@[simp, norm_cast]
theorem coe_map (S : ConvexCone 𝕜 E) (f : E →ₗ[𝕜] F) : (S.map f : Set F) = f '' S :=
  rfl

@[simp]
theorem mem_map {f : E →ₗ[𝕜] F} {S : ConvexCone 𝕜 E} {y : F} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Set.mem_image f S y

theorem map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 E) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image g f S

@[simp]
theorem map_id (S : ConvexCone 𝕜 E) : S.map LinearMap.id = S :=
  SetLike.coe_injective <| image_id _

/-- The preimage of a convex cone under a `𝕜`-linear map is a convex cone. -/
def comap (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 F) : ConvexCone 𝕜 E where
  carrier := f ⁻¹' S
  smul_mem' c hc x hx := by
    rw [mem_preimage, f.map_smul c]
    exact S.smul_mem hc hx
  add_mem' x hx y hy := by
    rw [mem_preimage, f.map_add]
    exact S.add_mem hx hy

@[simp]
theorem coe_comap (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 F) : (S.comap f : Set E) = f ⁻¹' S :=
  rfl

@[simp]
theorem comap_id (S : ConvexCone 𝕜 E) : S.comap LinearMap.id = S :=
  rfl

theorem comap_comap (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 G) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
theorem mem_comap {f : E →ₗ[𝕜] F} {S : ConvexCone 𝕜 F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

end Maps

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section MulAction

variable [AddCommMonoid E]
variable [MulAction 𝕜 E] (S : ConvexCone 𝕜 E)

theorem smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : E} : c • x ∈ S ↔ x ∈ S :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ S.smul_mem (inv_pos.2 hc) h, S.smul_mem hc⟩

end MulAction

section OrderedAddCommGroup

variable [AddCommGroup E] [PartialOrder E] [Module 𝕜 E]

/-- Constructs an ordered module given an `OrderedAddCommGroup`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
theorem to_orderedSMul (S : ConvexCone 𝕜 E) (h : ∀ x y : E, x ≤ y ↔ y - x ∈ S) : OrderedSMul 𝕜 E :=
  OrderedSMul.mk'
    (by
      intro x y z xy hz
      rw [h (z • x) (z • y), ← smul_sub z y x]
      exact smul_mem S hz ((h x y).mp xy.le))

end OrderedAddCommGroup

end LinearOrderedField

/-! ### Convex cones with extra properties -/


section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [SMul 𝕜 E] (S : ConvexCone 𝕜 E)

/-- A convex cone is pointed if it includes `0`. -/
def Pointed (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∈ S

/-- A convex cone is blunt if it doesn't include `0`. -/
def Blunt (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∉ S

theorem pointed_iff_not_blunt (S : ConvexCone 𝕜 E) : S.Pointed ↔ ¬S.Blunt :=
  ⟨fun h₁ h₂ => h₂ h₁, Classical.not_not.mp⟩

theorem blunt_iff_not_pointed (S : ConvexCone 𝕜 E) : S.Blunt ↔ ¬S.Pointed := by
  rw [pointed_iff_not_blunt, Classical.not_not]

theorem Pointed.mono {S T : ConvexCone 𝕜 E} (h : S ≤ T) : S.Pointed → T.Pointed :=
  @h _

theorem Blunt.anti {S T : ConvexCone 𝕜 E} (h : T ≤ S) : S.Blunt → T.Blunt :=
  (· ∘ @h 0)

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup E] [SMul 𝕜 E] (S : ConvexCone 𝕜 E)

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def Flat : Prop :=
  ∃ x ∈ S, x ≠ (0 : E) ∧ -x ∈ S

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def Salient : Prop :=
  ∀ x ∈ S, x ≠ (0 : E) → -x ∉ S

theorem salient_iff_not_flat (S : ConvexCone 𝕜 E) : S.Salient ↔ ¬S.Flat := by
  simp [Salient, Flat]

theorem Flat.mono {S T : ConvexCone 𝕜 E} (h : S ≤ T) : S.Flat → T.Flat
  | ⟨x, hxS, hx, hnxS⟩ => ⟨x, h hxS, hx, h hnxS⟩

theorem Salient.anti {S T : ConvexCone 𝕜 E} (h : T ≤ S) : S.Salient → T.Salient :=
  fun hS x hxT hx hnT => hS x (h hxT) hx (h hnT)

/-- A flat cone is always pointed (contains `0`). -/
theorem Flat.pointed {S : ConvexCone 𝕜 E} (hS : S.Flat) : S.Pointed := by
  obtain ⟨x, hx, _, hxneg⟩ := hS
  rw [Pointed, ← add_neg_cancel x]
  exact add_mem S hx hxneg

/-- A blunt cone (one not containing `0`) is always salient. -/
theorem Blunt.salient {S : ConvexCone 𝕜 E} : S.Blunt → S.Salient := by
  rw [salient_iff_not_flat, blunt_iff_not_pointed]
  exact mt Flat.pointed

/-- A pointed convex cone defines a preorder. -/
def toPreorder (h₁ : S.Pointed) : Preorder E where
  le x y := y - x ∈ S
  le_refl x := by rw [sub_self x]; exact h₁
  le_trans x y z xy zy := by simpa using add_mem S zy xy

/-- A pointed and salient cone defines a partial order. -/
def toPartialOrder (h₁ : S.Pointed) (h₂ : S.Salient) : PartialOrder E :=
  { toPreorder S h₁ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a ≠ 0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }

/-- A pointed and salient cone defines an `IsOrderedAddMonoid`. -/
lemma toIsOrderedAddMonoid (h₁ : S.Pointed) (h₂ : S.Salient) :
    let _ := toPartialOrder S h₁ h₂
    IsOrderedAddMonoid E :=
  let _ := toPartialOrder S h₁ h₂
  { add_le_add_left := by
      intro a b hab c
      change c + b - (c + a) ∈ S
      rw [add_sub_add_left_eq_sub]
      exact hab }

end AddCommGroup

section Module

variable [AddCommMonoid E] [Module 𝕜 E]

instance : Zero (ConvexCone 𝕜 E) :=
  ⟨⟨0, fun _ _ => by simp, fun _ => by simp⟩⟩

@[simp]
theorem mem_zero (x : E) : x ∈ (0 : ConvexCone 𝕜 E) ↔ x = 0 :=
  Iff.rfl

@[simp]
theorem coe_zero : ((0 : ConvexCone 𝕜 E) : Set E) = 0 :=
  rfl

theorem pointed_zero : (0 : ConvexCone 𝕜 E).Pointed := by rw [Pointed, mem_zero]

instance instAdd : Add (ConvexCone 𝕜 E) :=
  ⟨fun K₁ K₂ =>
    { carrier := { z | ∃ x ∈ K₁, ∃ y ∈ K₂, x + y = z }
      smul_mem' := by
        rintro c hc _ ⟨x, hx, y, hy, rfl⟩
        rw [smul_add]
        use c • x, K₁.smul_mem hc hx, c • y, K₂.smul_mem hc hy
      add_mem' := by
        rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ y ⟨y₁, hy₁, y₂, hy₂, rfl⟩
        use x₁ + y₁, K₁.add_mem hx₁ hy₁, x₂ + y₂, K₂.add_mem hx₂ hy₂
        abel }⟩

@[simp]
theorem mem_add {K₁ K₂ : ConvexCone 𝕜 E} {a : E} :
    a ∈ K₁ + K₂ ↔ ∃ x ∈ K₁, ∃ y ∈ K₂, x + y = a :=
  Iff.rfl

instance instAddZeroClass : AddZeroClass (ConvexCone 𝕜 E) where
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp

instance instAddCommSemigroup : AddCommSemigroup (ConvexCone 𝕜 E) where
  add := Add.add
  add_assoc _ _ _ := SetLike.coe_injective <| add_assoc _ _ _
  add_comm _ _ := SetLike.coe_injective <| add_comm _ _

end Module

end OrderedSemiring

end ConvexCone

namespace Submodule

/-! ### Submodules are cones -/


section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [Module 𝕜 E]

/-- Every submodule is trivially a convex cone. -/
def toConvexCone (S : Submodule 𝕜 E) : ConvexCone 𝕜 E where
  carrier := S
  smul_mem' c _ _ hx := S.smul_mem c hx
  add_mem' _ hx _ hy := S.add_mem hx hy

@[simp]
theorem coe_toConvexCone (S : Submodule 𝕜 E) : ↑S.toConvexCone = (S : Set E) :=
  rfl

@[simp]
theorem mem_toConvexCone {x : E} {S : Submodule 𝕜 E} : x ∈ S.toConvexCone ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem toConvexCone_le_iff {S T : Submodule 𝕜 E} : S.toConvexCone ≤ T.toConvexCone ↔ S ≤ T :=
  Iff.rfl

@[simp]
theorem toConvexCone_bot : (⊥ : Submodule 𝕜 E).toConvexCone = 0 :=
  rfl

@[simp]
theorem toConvexCone_top : (⊤ : Submodule 𝕜 E).toConvexCone = ⊤ :=
  rfl

@[simp]
theorem toConvexCone_inf (S T : Submodule 𝕜 E) :
    (S ⊓ T).toConvexCone = S.toConvexCone ⊓ T.toConvexCone :=
  rfl

@[simp]
theorem pointed_toConvexCone (S : Submodule 𝕜 E) : S.toConvexCone.Pointed :=
  S.zero_mem

end AddCommMonoid

end OrderedSemiring

end Submodule

namespace ConvexCone

/-! ### Positive cone of an ordered module -/


section PositiveCone

variable (𝕜 E) [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [OrderedSMul 𝕜 E]

/-- The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module.
-/
def positive : ConvexCone 𝕜 E where
  carrier := Set.Ici 0
  smul_mem' _ hc _ (hx : _ ≤ _) := smul_nonneg hc.le hx
  add_mem' _ (hx : _ ≤ _) _ (hy : _ ≤ _) := add_nonneg hx hy

@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl

@[simp]
theorem coe_positive : ↑(positive 𝕜 E) = Set.Ici (0 : E) :=
  rfl

/-- The positive cone of an ordered module is always salient. -/
theorem salient_positive : Salient (positive 𝕜 E) := fun x xs hx hx' =>
  lt_irrefl (0 : E)
    (calc
      0 < x := lt_of_le_of_ne xs hx.symm
      _ ≤ x + -x := le_add_of_nonneg_right hx'
      _ = 0 := add_neg_cancel x
      )

/-- The positive cone of an ordered module is always pointed. -/
theorem pointed_positive : Pointed (positive 𝕜 E) :=
  le_refl 0

/-- The cone of strictly positive elements.

Note that this naming diverges from the mathlib convention of `pos` and `nonneg` due to "positive
cone" (`ConvexCone.positive`) being established terminology for the non-negative elements. -/
def strictlyPositive : ConvexCone 𝕜 E where
  carrier := Set.Ioi 0
  smul_mem' _ hc _ (hx : _ < _) := smul_pos hc hx
  add_mem' _ hx _ hy := add_pos hx hy

@[simp]
theorem mem_strictlyPositive {x : E} : x ∈ strictlyPositive 𝕜 E ↔ 0 < x :=
  Iff.rfl

@[simp]
theorem coe_strictlyPositive : ↑(strictlyPositive 𝕜 E) = Set.Ioi (0 : E) :=
  rfl

theorem positive_le_strictlyPositive : strictlyPositive 𝕜 E ≤ positive 𝕜 E := fun _ => le_of_lt

/-- The strictly positive cone of an ordered module is always salient. -/
theorem salient_strictlyPositive : Salient (strictlyPositive 𝕜 E) :=
  (salient_positive 𝕜 E).anti <| positive_le_strictlyPositive 𝕜 E

/-- The strictly positive cone of an ordered module is always blunt. -/
theorem blunt_strictlyPositive : Blunt (strictlyPositive 𝕜 E) :=
  lt_irrefl 0

end PositiveCone

section ContinuousSMul
variable [TopologicalSpace 𝕜] [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [OrderTopology 𝕜]
  [DenselyOrdered 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {S : ConvexCone 𝕜 E}

lemma Pointed.of_nonempty_of_isClosed (hS : (S : Set E).Nonempty) (hSclos : IsClosed (S : Set E)) :
    S.Pointed := by
  obtain ⟨x, hx⟩ := hS
  let f : 𝕜 → E := (· • x)
  -- The closure of `f (0, ∞)` is a subset of `K`
  have hfS : closure (f '' Set.Ioi 0) ⊆ S :=
    hSclos.closure_subset_iff.2 <| by rintro _ ⟨_, h, rfl⟩; exact S.smul_mem h hx
  -- `f` is continuous at `0` from the right
  have fc : ContinuousWithinAt f (Set.Ioi (0 : 𝕜)) 0 :=
    (continuous_id.smul continuous_const).continuousWithinAt
  -- `0 ∈ closure f (0, ∞) ⊆ K, 0 ∈ K`
  simpa [f, Pointed, ← SetLike.mem_coe] using hfS <| fc.mem_closure_image <| by simp

@[deprecated (since := "2025-04-18")]
alias pointed_of_nonempty_of_isClosed := Pointed.of_nonempty_of_isClosed

end ContinuousSMul

end ConvexCone

/-! ### Cone over a convex set -/


section ConeFromConvex

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace Convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def toCone (s : Set E) (hs : Convex 𝕜 s) : ConvexCone 𝕜 E := by
  apply ConvexCone.mk (⋃ (c : 𝕜) (_ : 0 < c), c • s) <;> simp only [mem_iUnion, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + cy := add_pos cx_pos cy_pos
    refine ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, ?_⟩
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left₀ _ this.ne']

variable {s : Set E} (hs : Convex 𝕜 s) {x : E}

theorem mem_toCone : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ ∃ y ∈ s, c • y = x := by
  simp only [toCone, ConvexCone.mem_mk, mem_iUnion, mem_smul_set, eq_comm, exists_prop]

theorem mem_toCone' : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ c • x ∈ s := by
  refine hs.mem_toCone.trans ⟨?_, ?_⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩

theorem subset_toCone : s ⊆ hs.toCone s := fun x hx =>
  hs.mem_toCone'.2 ⟨1, zero_lt_one, by rwa [one_smul]⟩

/-- `hs.toCone s` is the least cone that includes `s`. -/
theorem toCone_isLeast : IsLeast { t : ConvexCone 𝕜 E | s ⊆ t } (hs.toCone s) := by
  refine ⟨hs.subset_toCone, fun t ht x hx => ?_⟩
  rcases hs.mem_toCone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)

theorem toCone_eq_sInf : hs.toCone s = sInf { t : ConvexCone 𝕜 E | s ⊆ t } :=
  hs.toCone_isLeast.isGLB.sInf_eq.symm

end Convex

theorem convexHull_toCone_isLeast (s : Set E) :
    IsLeast { t : ConvexCone 𝕜 E | s ⊆ t } ((convex_convexHull 𝕜 s).toCone _) := by
  convert (convex_convexHull 𝕜 s).toCone_isLeast using 1
  ext t
  exact ⟨fun h => convexHull_min h t.convex, (subset_convexHull 𝕜 s).trans⟩

theorem convexHull_toCone_eq_sInf (s : Set E) :
    (convex_convexHull 𝕜 s).toCone _ = sInf { t : ConvexCone 𝕜 E | s ⊆ t } :=
  Eq.symm <| IsGLB.sInf_eq <| IsLeast.isGLB <| convexHull_toCone_isLeast s

end ConeFromConvex
