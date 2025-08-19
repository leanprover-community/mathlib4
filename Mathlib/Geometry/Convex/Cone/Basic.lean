/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
import Mathlib.Analysis.Convex.Hull

/-!
# Convex cones

In a `R`-module `M`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
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

While `Convex R` is a predicate on sets, `ConvexCone R M` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
* [Stephen P. Boyd and Lieven Vandenberghe, *Convex Optimization*][boydVandenberghe2004]
* [Emo Welzl and Bernd Gärtner, *Cone Programming*][welzl_garter]
-/

assert_not_exists TopologicalSpace Real Cardinal

open Set LinearMap Pointwise

variable {𝕜 R G M N O : Type*}

/-! ### Definition of `ConvexCone` and basic properties -/

section Definitions

variable [Semiring R] [PartialOrder R]

variable (R M) in
/-- A convex cone is a subset `s` of a `R`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
structure ConvexCone [AddCommMonoid M] [SMul R M] where
  /-- The **carrier set** underlying this cone: the set of points contained in it -/
  carrier : Set M
  smul_mem' : ∀ ⦃c : R⦄, 0 < c → ∀ ⦃x : M⦄, x ∈ carrier → c • x ∈ carrier
  add_mem' : ∀ ⦃x⦄ (_ : x ∈ carrier) ⦃y⦄ (_ : y ∈ carrier), x + y ∈ carrier

end Definitions

namespace ConvexCone

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [AddCommMonoid M]

section SMul

variable [SMul R M] {C C₁ C₂ : ConvexCone R M} {s : Set M} {c : R} {x : M}

instance : SetLike (ConvexCone R M) M where
  coe := carrier
  coe_injective' C₁ C₂ h := by cases C₁; congr!

@[simp, norm_cast] lemma coe_mk (s : Set M) (h₁ h₂) : ↑(mk (R := R) s h₁ h₂) = s := rfl

@[simp] lemma mem_mk {h₁ h₂} : x ∈ mk (R := R) s h₁ h₂ ↔ x ∈ s := .rfl

/-- Two `ConvexCone`s are equal if they have the same elements. -/
@[ext]
theorem ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

variable (C) in
@[aesop 90% (rule_sets := [SetLike])]
protected lemma smul_mem (hc : 0 < c) (hx : x ∈ C) : c • x ∈ C := C.smul_mem' hc hx

variable (C) in
protected lemma add_mem ⦃x⦄ (hx : x ∈ C) ⦃y⦄ (hy : y ∈ C) : x + y ∈ C := C.add_mem' hx hy

instance : AddMemClass (ConvexCone R M) M where add_mem ha hb := add_mem' _ ha hb

instance : Min (ConvexCone R M) :=
  ⟨fun S T ↦
    ⟨S ∩ T, fun _ hc _ hx ↦ ⟨S.smul_mem hc hx.1, T.smul_mem hc hx.2⟩, fun _ hx _ hy ↦
      ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩⟩⟩

variable (C₁ C₂) in
@[simp, norm_cast] lemma coe_inf : (C₁ ⊓ C₂) = (C₁ ∩ C₂ : Set M) := rfl

@[simp] lemma mem_inf : x ∈ C₁ ⊓ C₂ ↔ x ∈ C₁ ∧ x ∈ C₂ := .rfl

instance : InfSet (ConvexCone R M) where
  sInf S :=
    ⟨⋂ C ∈ S, C, fun _r hr _x hx ↦ mem_biInter fun C hC ↦ C.smul_mem hr <| mem_iInter₂.1 hx C hC,
      fun _ hx _ hy ↦
      mem_biInter fun C hC ↦ add_mem (mem_iInter₂.1 hx C hC) (mem_iInter₂.1 hy C hC)⟩

@[simp, norm_cast]
lemma coe_sInf (S : Set (ConvexCone R M)) : ↑(sInf S) = ⋂ C ∈ S, (C : Set M) := rfl

@[simp] lemma mem_sInf {S : Set (ConvexCone R M)} : x ∈ sInf S ↔ ∀ C ∈ S, x ∈ C := mem_iInter₂

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} (f : ι → ConvexCone R M) : ↑(iInf f) = ⋂ i, (f i : Set M) := by
  simp [iInf]

@[simp]
lemma mem_iInf {ι : Sort*} {f : ι → ConvexCone R M} : x ∈ iInf f ↔ ∀ i, x ∈ f i :=
  mem_iInter₂.trans <| by simp

instance : Bot (ConvexCone R M) :=
  ⟨⟨∅, fun _ _ _ ↦ False.elim, fun _ ↦ False.elim⟩⟩

@[simp] lemma notMem_bot : x ∉ (⊥ : ConvexCone R M) := id

@[deprecated notMem_bot (since := "2025-06-11")]
theorem mem_bot (x : M) : (x ∈ (⊥ : ConvexCone R M)) = False :=
  rfl

@[simp, norm_cast] lemma coe_bot : ↑(⊥ : ConvexCone R M) = (∅ : Set M) := rfl

@[simp, norm_cast]
lemma coe_eq_empty : (C : Set M) = ∅ ↔ C = ⊥ := by rw [← coe_bot (R := R)]; norm_cast

instance : Top (ConvexCone R M) :=
  ⟨⟨univ, fun _ _ _ _ ↦ mem_univ _, fun _ _ _ _ ↦ mem_univ _⟩⟩

@[simp] lemma mem_top : x ∈ (⊤ : ConvexCone R M) := mem_univ x

@[simp, norm_cast] lemma coe_top : ↑(⊤ : ConvexCone R M) = (univ : Set M) := rfl

instance : CompleteLattice (ConvexCone R M) :=
  { SetLike.instPartialOrder with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun _ _ ↦ False.elim
    top := ⊤
    le_top _ _ _ := mem_top
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    sup := fun a b ↦ sInf { x | a ≤ x ∧ b ≤ x }
    sSup := fun s ↦ sInf { T | ∀ S ∈ s, S ≤ T }
    le_sup_left := fun _ _ ↦ fun _ hx ↦ mem_sInf.2 fun _ hs ↦ hs.1 hx
    le_sup_right := fun _ _ ↦ fun _ hx ↦ mem_sInf.2 fun _ hs ↦ hs.2 hx
    sup_le := fun _ _ c ha hb _ hx ↦ mem_sInf.1 hx c ⟨ha, hb⟩
    le_inf := fun _ _ _ ha hb _ hx ↦ ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ ↦ And.left
    inf_le_right := fun _ _ _ ↦ And.right
    le_sSup := fun _ p hs _ hx ↦ mem_sInf.2 fun _ ht ↦ ht p hs hx
    sSup_le := fun _ p hs _ hx ↦ mem_sInf.1 hx p hs
    le_sInf := fun _ _ ha _ hx ↦ mem_sInf.2 fun t ht ↦ ha t ht hx
    sInf_le := fun _ _ ha _ hx ↦ mem_sInf.1 hx _ ha }

instance : Inhabited (ConvexCone R M) := ⟨⊥⟩

end SMul

section Module

variable [Module R M] (C : ConvexCone R M)

protected theorem convex : Convex R (C : Set M) :=
  convex_iff_forall_pos.2 fun _ hx _ hy _ _ ha hb _ ↦ add_mem (C.smul_mem ha hx) (C.smul_mem hb hy)

end Module

section Maps

variable [AddCommMonoid N] [AddCommMonoid O]
variable [Module R M] [Module R N] [Module R O]

/-- The image of a convex cone under a `R`-linear map is a convex cone. -/
def map (f : M →ₗ[R] N) (C : ConvexCone R M) : ConvexCone R N where
  carrier := f '' C
  smul_mem' := fun c hc _ ⟨x, hx, hy⟩ ↦ hy ▸ f.map_smul c x ▸ mem_image_of_mem f (C.smul_mem hc hx)
  add_mem' := fun _ ⟨x₁, hx₁, hy₁⟩ _ ⟨x₂, hx₂, hy₂⟩ ↦
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (add_mem hx₁ hx₂)

@[simp, norm_cast]
theorem coe_map (C : ConvexCone R M) (f : M →ₗ[R] N) : (C.map f : Set N) = f '' C :=
  rfl

@[simp]
theorem mem_map {f : M →ₗ[R] N} {C : ConvexCone R M} {y : N} : y ∈ C.map f ↔ ∃ x ∈ C, f x = y :=
  Set.mem_image f C y

theorem map_map (g : N →ₗ[R] O) (f : M →ₗ[R] N) (C : ConvexCone R M) :
    (C.map f).map g = C.map (g.comp f) :=
  SetLike.coe_injective <| image_image g f C

@[simp]
theorem map_id (C : ConvexCone R M) : C.map LinearMap.id = C :=
  SetLike.coe_injective <| image_id _

/-- The preimage of a convex cone under a `R`-linear map is a convex cone. -/
def comap (f : M →ₗ[R] N) (C : ConvexCone R N) : ConvexCone R M where
  carrier := f ⁻¹' C
  smul_mem' c hc x hx := by
    rw [mem_preimage, f.map_smul c]
    exact C.smul_mem hc hx
  add_mem' x hx y hy := by
    rw [mem_preimage, f.map_add]
    exact add_mem hx hy

@[simp]
theorem coe_comap (f : M →ₗ[R] N) (C : ConvexCone R N) : (C.comap f : Set M) = f ⁻¹' C :=
  rfl

@[simp]
theorem comap_id (C : ConvexCone R M) : C.comap LinearMap.id = C :=
  rfl

theorem comap_comap (g : N →ₗ[R] O) (f : M →ₗ[R] N) (C : ConvexCone R O) :
    (C.comap g).comap f = C.comap (g.comp f) :=
  rfl

@[simp]
theorem mem_comap {f : M →ₗ[R] N} {C : ConvexCone R N} {x : M} : x ∈ C.comap f ↔ f x ∈ C :=
  Iff.rfl

end Maps

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section MulAction

variable [AddCommMonoid M]
variable [MulAction 𝕜 M] (C : ConvexCone 𝕜 M)

theorem smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : M} : c • x ∈ C ↔ x ∈ C :=
  ⟨fun h ↦ inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc) h, C.smul_mem hc⟩

end MulAction

section OrderedAddCommGroup

variable [AddCommGroup M] [PartialOrder M] [Module 𝕜 M]

/-- Constructs an ordered module given an `OrderedAddCommGroup`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
theorem to_orderedSMul (C : ConvexCone 𝕜 M) (h : ∀ x y : M, x ≤ y ↔ y - x ∈ C) : OrderedSMul 𝕜 M :=
  .mk' fun x y z xy hz ↦ by
    rw [h (z • x) (z • y), ← smul_sub z y x]; exact C.smul_mem hz ((h x y).mp xy.le)

end OrderedAddCommGroup

end LinearOrderedField

/-! ### Convex cones with extra properties -/


section OrderedSemiring

variable [Semiring R] [PartialOrder R]

section AddCommMonoid

variable [AddCommMonoid M] [SMul R M] {C C₁ C₂ : ConvexCone R M}

/-- A convex cone is pointed if it includes `0`. -/
def Pointed (C : ConvexCone R M) : Prop := (0 : M) ∈ C

/-- A convex cone is blunt if it doesn't include `0`. -/
def Blunt (C : ConvexCone R M) : Prop := (0 : M) ∉ C

lemma blunt_iff_not_pointed : C.Blunt ↔ ¬ C.Pointed := .rfl
lemma pointed_iff_not_blunt : C.Pointed ↔ ¬ C.Blunt := by simp [Blunt, Pointed]

theorem Pointed.mono (h : C₁ ≤ C₂) : C₁.Pointed → C₂.Pointed := @h _
theorem Blunt.anti (h : C₂ ≤ C₁) : C₁.Blunt → C₂.Blunt := (· ∘ @h 0)

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G] [SMul R G] {C C₁ C₂ : ConvexCone R G}

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def Flat (C : ConvexCone R G) : Prop := ∃ x ∈ C, x ≠ (0 : G) ∧ -x ∈ C

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def Salient (C : ConvexCone R G) : Prop := ∀ x ∈ C, x ≠ (0 : G) → -x ∉ C

theorem salient_iff_not_flat : C.Salient ↔ ¬ C.Flat := by simp [Salient, Flat]

theorem Flat.mono (h : C₁ ≤ C₂) : C₁.Flat → C₂.Flat
  | ⟨x, hxS, hx, hnxS⟩ => ⟨x, h hxS, hx, h hnxS⟩

theorem Salient.anti (h : C₂ ≤ C₁) : C₁.Salient → C₂.Salient :=
  fun hS x hxT hx hnT ↦ hS x (h hxT) hx (h hnT)

/-- A flat cone is always pointed (contains `0`). -/
theorem Flat.pointed (hC : C.Flat) : C.Pointed := by
  obtain ⟨x, hx, _, hxneg⟩ := hC
  rw [Pointed, ← add_neg_cancel x]
  exact add_mem hx hxneg

/-- A blunt cone (one not containing `0`) is always salient. -/
theorem Blunt.salient : C.Blunt → C.Salient := by
  rw [salient_iff_not_flat, blunt_iff_not_pointed]
  exact mt Flat.pointed

/-- A pointed convex cone defines a preorder. -/
def toPreorder (C : ConvexCone R G) (h₁ : C.Pointed) : Preorder G where
  le x y := y - x ∈ C
  le_refl x := by rw [sub_self x]; exact h₁
  le_trans x y z xy zy := by simpa using add_mem zy xy

/-- A pointed and salient cone defines a partial order. -/
def toPartialOrder (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient) : PartialOrder G :=
  { toPreorder C h₁ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a ≠ 0 := fun h'' ↦ h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }

/-- A pointed and salient cone defines an `IsOrderedAddMonoid`. -/
lemma to_isOrderedAddMonoid (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient) :
    let _ := toPartialOrder C h₁ h₂
    IsOrderedAddMonoid G :=
  let _ := toPartialOrder C h₁ h₂
  { add_le_add_left := by
      intro a b hab c
      change c + b - (c + a) ∈ C
      rw [add_sub_add_left_eq_sub]
      exact hab }

@[deprecated (since := "2025-06-11")] alias toIsOrderedAddMonoid := to_isOrderedAddMonoid

end AddCommGroup

section Module

variable [AddCommMonoid M] [Module R M] {C₁ C₂ : ConvexCone R M} {x : M}

instance : Zero (ConvexCone R M) :=
  ⟨⟨0, fun _ _ ↦ by simp, fun _ ↦ by simp⟩⟩

@[simp] lemma mem_zero : x ∈ (0 : ConvexCone R M) ↔ x = 0 := .rfl

@[simp, norm_cast] lemma coe_zero : ((0 : ConvexCone R M) : Set M) = 0 := rfl

theorem pointed_zero : (0 : ConvexCone R M).Pointed := by rw [Pointed, mem_zero]

instance instAdd : Add (ConvexCone R M) where
  add C₁ C₂ := {
    carrier := C₁ + C₂
    smul_mem' := by
      rintro c hc _ ⟨x, hx, y, hy, rfl⟩
      rw [smul_add]
      use c • x, C₁.smul_mem hc hx, c • y, C₂.smul_mem hc hy
    add_mem' := by
      rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ y ⟨y₁, hy₁, y₂, hy₂, rfl⟩
      exact ⟨x₁ + y₁, add_mem hx₁ hy₁, x₂ + y₂, add_mem hx₂ hy₂, add_add_add_comm ..⟩
  }

@[simp, norm_cast] lemma coe_add (C₁ C₂ : ConvexCone R M) : ↑(C₁ + C₂) = (C₁ + C₂ : Set M) := rfl
@[simp] lemma mem_add : x ∈ C₁ + C₂ ↔ ∃ y ∈ C₁, ∃ z ∈ C₂, y + z = x := .rfl

instance instAddZeroClass : AddZeroClass (ConvexCone R M) where
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp

instance instAddCommSemigroup : AddCommSemigroup (ConvexCone R M) where
  add := Add.add
  add_assoc _ _ _ := SetLike.coe_injective <| add_assoc _ _ _
  add_comm _ _ := SetLike.coe_injective <| add_comm _ _

end Module

end OrderedSemiring

end ConvexCone

namespace Submodule

/-! ### Submodules are cones -/


section OrderedSemiring

variable [Semiring R] [PartialOrder R]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] {C C₁ C₂ : Submodule R M} {x : M}

/-- Every submodule is trivially a convex cone. -/
def toConvexCone (C : Submodule R M) : ConvexCone R M where
  carrier := C
  smul_mem' c _ _ hx := C.smul_mem c hx
  add_mem' _ hx _ hy := C.add_mem hx hy

@[simp] lemma coe_toConvexCone (C : Submodule R M) : C.toConvexCone = (C : Set M) := rfl

@[simp] lemma mem_toConvexCone : x ∈ C.toConvexCone ↔ x ∈ C := .rfl

@[simp]
lemma toConvexCone_le_toConvexCone : C₁.toConvexCone ≤ C₂.toConvexCone ↔ C₁ ≤ C₂ := .rfl

@[deprecated (since := "2025-06-11")] alias toConvexCone_le_iff := toConvexCone_le_toConvexCone

@[simp] lemma toConvexCone_bot : (⊥ : Submodule R M).toConvexCone = 0 := rfl
@[simp] lemma toConvexCone_top : (⊤ : Submodule R M).toConvexCone = ⊤ := rfl

@[simp]
lemma toConvexCone_inf (C₁ C₂ : Submodule R M) :
    (C₁ ⊓ C₂).toConvexCone = C₁.toConvexCone ⊓ C₂.toConvexCone := rfl

@[simp]
lemma pointed_toConvexCone (C : Submodule R M) : C.toConvexCone.Pointed := C.zero_mem

@[deprecated (since := "2025-06-11")] alias toConvexCone_pointed := pointed_toConvexCone

end AddCommMonoid

end OrderedSemiring

end Submodule

/-! ### Positive cone of an ordered module -/

namespace ConvexCone

section PositiveCone
variable [Semiring R] [PartialOrder R] [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module R M] [PosSMulMono R M] {x : M}

variable (R M) in
/-- The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : ConvexCone R M where
  carrier := Set.Ici 0
  smul_mem' _ hc _ (hx : _ ≤ _) := smul_nonneg hc.le hx
  add_mem' _ (hx : _ ≤ _) _ (hy : _ ≤ _) := add_nonneg hx hy

@[simp] lemma mem_positive : x ∈ positive R M ↔ 0 ≤ x := .rfl

variable (R M) in
@[simp]
theorem coe_positive : ↑(positive R M) = Set.Ici (0 : M) :=
  rfl

/-- The positive cone of an ordered module is always salient. -/
lemma salient_positive {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    [Module R G] [PosSMulMono R G] : Salient (positive R G) :=
  fun x hx_nonneg hx_ne_zero hx_nonpos ↦ lt_irrefl (0 : G) <| by
    simpa using add_pos_of_nonneg_of_pos hx_nonpos <| hx_nonneg.lt_of_ne' hx_ne_zero

/-- The positive cone of an ordered module is always pointed. -/
theorem pointed_positive : Pointed (positive R M) :=
  le_refl 0

end PositiveCone

section StrictlyPositiveCone
variable [Semiring R] [PartialOrder R] [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module R M] [PosSMulStrictMono R M] {x : M}

variable (R M) in
/-- The cone of strictly positive elements.

Note that this naming diverges from the mathlib convention of `pos` and `nonneg` due to "positive
cone" (`ConvexCone.positive`) being established terminology for the non-negative elements. -/
def strictlyPositive : ConvexCone R M where
  carrier := Set.Ioi 0
  smul_mem' _ hc _ (hx : _ < _) := smul_pos hc hx
  add_mem' _ hx _ hy := add_pos hx hy

@[simp]
lemma mem_strictlyPositive : x ∈ strictlyPositive R M ↔ 0 < x := .rfl

variable (R M) in
@[simp]
theorem coe_strictlyPositive : ↑(strictlyPositive R M) = Set.Ioi (0 : M) :=
  rfl

lemma strictlyPositive_le_positive : strictlyPositive R M ≤ positive R M := fun _ ↦ le_of_lt

@[deprecated (since := "2025-05-29")]
alias positive_le_strictlyPositive := strictlyPositive_le_positive

/-- The strictly positive cone of an ordered module is always salient. -/
theorem salient_strictlyPositive : Salient (strictlyPositive R M) :=
  salient_positive.anti strictlyPositive_le_positive

/-- The strictly positive cone of an ordered module is always blunt. -/
theorem blunt_strictlyPositive : Blunt (strictlyPositive R M) :=
  lt_irrefl 0

end StrictlyPositiveCone

end ConvexCone

/-! ### Cone over a convex set -/


section ConeFromConvex

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]

namespace Convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def toCone (s : Set M) (hs : Convex 𝕜 s) : ConvexCone 𝕜 M := by
  apply ConvexCone.mk (⋃ (c : 𝕜) (_ : 0 < c), c • s) <;> simp only [mem_iUnion, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + cy := add_pos cx_pos cy_pos
    refine ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, ?_⟩
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left₀ _ this.ne']

variable {s : Set M} (hs : Convex 𝕜 s) {x : M}

theorem mem_toCone : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ ∃ y ∈ s, c • y = x := by
  simp only [toCone, ConvexCone.mem_mk, mem_iUnion, mem_smul_set, eq_comm, exists_prop]

theorem mem_toCone' : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ c • x ∈ s := by
  refine hs.mem_toCone.trans ⟨?_, ?_⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩

theorem subset_toCone : s ⊆ hs.toCone s := fun x hx ↦
  hs.mem_toCone'.2 ⟨1, zero_lt_one, by rwa [one_smul]⟩

/-- `hs.toCone s` is the least cone that includes `s`. -/
theorem toCone_isLeast : IsLeast { t : ConvexCone 𝕜 M | s ⊆ t } (hs.toCone s) := by
  refine ⟨hs.subset_toCone, fun t ht x hx ↦ ?_⟩
  rcases hs.mem_toCone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)

theorem toCone_eq_sInf : hs.toCone s = sInf { t : ConvexCone 𝕜 M | s ⊆ t } :=
  hs.toCone_isLeast.isGLB.sInf_eq.symm

end Convex

theorem convexHull_toCone_isLeast (s : Set M) :
    IsLeast { t : ConvexCone 𝕜 M | s ⊆ t } ((convex_convexHull 𝕜 s).toCone _) := by
  convert (convex_convexHull 𝕜 s).toCone_isLeast using 1
  ext t
  exact ⟨fun h ↦ convexHull_min h t.convex, (subset_convexHull 𝕜 s).trans⟩

theorem convexHull_toCone_eq_sInf (s : Set M) :
    (convex_convexHull 𝕜 s).toCone _ = sInf { t : ConvexCone 𝕜 M | s ⊆ t } :=
  Eq.symm <| IsGLB.sInf_eq <| IsLeast.isGLB <| convexHull_toCone_isLeast s

end ConeFromConvex
