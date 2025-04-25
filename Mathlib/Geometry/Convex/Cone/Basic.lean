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

variable {𝕜 R M N O : Type*}

/-! ### Definition of `ConvexCone` and basic properties -/

section Definitions

variable [Semiring R] [PartialOrder R]

variable (R M) in
/-- A convex cone is a subset `s` of a `R`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
structure ConvexCone [IsOrderedRing R] [AddCommMonoid M] [SMul R M] where
  /-- The **carrier set** underlying this cone: the set of points contained in it -/
  carrier : Set M
  smul_mem' : ∀ ⦃c : R⦄, 0 < c → ∀ ⦃x : M⦄, x ∈ carrier → c • x ∈ carrier
  add_mem' : ∀ ⦃x⦄ (_ : x ∈ carrier) ⦃y⦄ (_ : y ∈ carrier), x + y ∈ carrier

end Definitions

namespace ConvexCone

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M]

section SMul

variable [SMul R M] {C C₁ C₂ : ConvexCone R M} {s : Set M} {c : R} {x : M}

instance : SetLike (ConvexCone R M) M where
  coe := carrier
  coe_injective' C₁ C₂ h := by cases C₁; congr!

@[simp]
theorem coe_mk (s : Set M) (h₁ h₂) : ↑(mk (R := R) s h₁ h₂) = s :=
  rfl

@[simp]
theorem mem_mk {s : Set M} {h₁ h₂ x} : x ∈ mk (R := R) s h₁ h₂ ↔ x ∈ s :=
  Iff.rfl

/-- Two `ConvexCone`s are equal if they have the same elements. -/
@[ext]
theorem ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ :=
  SetLike.ext h

variable (C) in
@[aesop safe apply (rule_sets := [SetLike])]
protected lemma smul_mem (hc : 0 < c) (hx : x ∈ C) : c • x ∈ C := C.smul_mem' hc hx

variable (C) in
protected lemma add_mem ⦃x⦄ (hx : x ∈ C) ⦃y⦄ (hy : y ∈ C) : x + y ∈ C := C.add_mem' hx hy

instance : AddMemClass (ConvexCone R M) M where add_mem ha hb := add_mem' _ ha hb

/-- Copy of a convex cone with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps] protected def copy (C : ConvexCone R M) (s : Set M) (hs : s = C) : ConvexCone R M where
  carrier := s
  add_mem' := hs.symm ▸ C.add_mem'
  smul_mem' := by simpa [hs] using C.smul_mem'

lemma copy_eq (C : ConvexCone R M) (s : Set M) (hs) : C.copy s hs = C := SetLike.coe_injective hs

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

instance : CompleteSemilatticeInf (ConvexCone R M) where
  sInf_le S C hC := by rw [← SetLike.coe_subset_coe, coe_sInf]; exact biInter_subset_of_mem hC
  le_sInf S C hC := by rw [← SetLike.coe_subset_coe, coe_sInf]; exact subset_iInter₂ hC

variable (R s) in
/-- The cone hull of a set. The smallest convex cone containing that set. -/
def hull : ConvexCone R M := sInf {C : ConvexCone R M | s ⊆ C}

lemma subset_hull : s ⊆ hull R s := by simp [hull]

lemma hull_min (hsC : s ⊆ C) : hull R s ≤ C := sInf_le hsC

lemma hull_le_iff : hull R s ≤ C ↔ s ⊆ C := ⟨subset_hull.trans, hull_min⟩

lemma gc_hull_coe : GaloisConnection (hull R : Set M → ConvexCone R M) (↑) :=
  fun _C _s ↦ hull_le_iff

-- TODO: Fix docstring of `NonUnitalSubalgebra.gi` (it's not `Subtype.val`)
/-- Galois insertion between `ConvexCone` and `SetLike.coe`. -/
protected def gi : GaloisInsertion (hull R : Set M → ConvexCone R M) (↑)  where
  gc := gc_hull_coe
  le_l_u _ := subset_hull
  choice s hs := (hull R s).copy s <| subset_hull.antisymm hs
  choice_eq _ _ := copy_eq _ _ _

instance : Bot (ConvexCone R M) :=
  ⟨⟨∅, fun _ _ _ => False.elim, fun _ => False.elim⟩⟩

@[simp] lemma not_mem_bot : x ∉ (⊥ : ConvexCone R M) := id

@[simp, norm_cast] lemma coe_bot : ↑(⊥ : ConvexCone R M) = (∅ : Set M) := rfl

@[simp, norm_cast]
lemma coe_eq_empty : (C : Set M) = ∅ ↔ C = ⊥ := by rw [← coe_bot (R := R)]; norm_cast

instance : CompleteLattice (ConvexCone R M) where
  bot := ⊥
  bot_le _ := empty_subset _
  __ := ConvexCone.gi.liftCompleteLattice

variable (C₁ C₂) in
@[simp, norm_cast] lemma coe_inf : (C₁ ⊓ C₂) = (C₁ ∩ C₂ : Set M) := rfl

@[simp] lemma mem_inf : x ∈ C₁ ⊓ C₂ ↔ x ∈ C₁ ∧ x ∈ C₂ := .rfl

@[simp] lemma mem_top : x ∈ (⊤ : ConvexCone R M) := mem_univ x

@[simp, norm_cast] lemma coe_top : ↑(⊤ : ConvexCone R M) = (univ : Set M) := rfl

@[simp, norm_cast] lemma disjoint_coe : Disjoint (C₁ : Set M) C₂ ↔ Disjoint C₁ C₂ := by
  simp [disjoint_iff, ← coe_inf]

instance : Inhabited (ConvexCone R M) := ⟨⊥⟩

end SMul

section Module

variable [Module R M] (S : ConvexCone R M)

protected theorem convex : Convex R (S : Set M) :=
  convex_iff_forall_pos.2 fun _ hx _ hy _ _ ha hb _ ↦ add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

end Module

section Maps

variable [AddCommMonoid N] [AddCommMonoid O]
variable [Module R M] [Module R N] [Module R O]

/-- The image of a convex cone under a `R`-linear map is a convex cone. -/
def map (f : M →ₗ[R] N) (S : ConvexCone R M) : ConvexCone R N where
  carrier := f '' S
  smul_mem' := fun c hc _ ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (S.smul_mem hc hx)
  add_mem' := fun _ ⟨x₁, hx₁, hy₁⟩ _ ⟨x₂, hx₂, hy₂⟩ =>
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (add_mem hx₁ hx₂)

@[simp, norm_cast]
theorem coe_map (S : ConvexCone R M) (f : M →ₗ[R] N) : (S.map f : Set N) = f '' S :=
  rfl

@[simp]
theorem mem_map {f : M →ₗ[R] N} {S : ConvexCone R M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Set.mem_image f S y

theorem map_map (g : N →ₗ[R] O) (f : M →ₗ[R] N) (S : ConvexCone R M) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image g f S

@[simp]
theorem map_id (S : ConvexCone R M) : S.map LinearMap.id = S :=
  SetLike.coe_injective <| image_id _

/-- The preimage of a convex cone under a `R`-linear map is a convex cone. -/
def comap (f : M →ₗ[R] N) (S : ConvexCone R N) : ConvexCone R M where
  carrier := f ⁻¹' S
  smul_mem' c hc x hx := by
    rw [mem_preimage, f.map_smul c]
    exact S.smul_mem hc hx
  add_mem' x hx y hy := by
    rw [mem_preimage, f.map_add]
    exact add_mem hx hy

@[simp]
theorem coe_comap (f : M →ₗ[R] N) (S : ConvexCone R N) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl

@[simp]
theorem comap_id (S : ConvexCone R M) : S.comap LinearMap.id = S :=
  rfl

theorem comap_comap (g : N →ₗ[R] O) (f : M →ₗ[R] N) (S : ConvexCone R O) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
theorem mem_comap {f : M →ₗ[R] N} {S : ConvexCone R N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

end Maps

end OrderedSemiring

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

section MulAction

variable [AddCommMonoid M]
variable [MulAction R M] (S : ConvexCone R M)

theorem smul_mem_iff {c : R} (hc : 0 < c) {x : M} : c • x ∈ S ↔ x ∈ S :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ S.smul_mem (inv_pos.2 hc) h, S.smul_mem hc⟩

end MulAction

section OrderedAddCommGroup

variable [AddCommGroup M] [PartialOrder M] [Module R M]

/-- Constructs an ordered module given an `OrderedAddCommGroup`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
theorem to_orderedSMul (C : ConvexCone R M) (h : ∀ x y : M, x ≤ y ↔ y - x ∈ C) : OrderedSMul R M :=
  .mk' fun x y z xy hz ↦ by
    rw [h (z • x) (z • y), ← smul_sub z y x]; exact C.smul_mem hz ((h x y).mp xy.le)

end OrderedAddCommGroup

end LinearOrderedField

/-! ### Convex cones with extra properties -/


section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

section AddCommMonoid

variable [AddCommMonoid M] [SMul R M] (S : ConvexCone R M)

/-- A convex cone is pointed if it includes `0`. -/
def Pointed (S : ConvexCone R M) : Prop :=
  (0 : M) ∈ S

/-- A convex cone is blunt if it doesn't include `0`. -/
def Blunt (S : ConvexCone R M) : Prop :=
  (0 : M) ∉ S

theorem pointed_iff_not_blunt (S : ConvexCone R M) : S.Pointed ↔ ¬S.Blunt :=
  ⟨fun h₁ h₂ => h₂ h₁, Classical.not_not.mp⟩

theorem blunt_iff_not_pointed (S : ConvexCone R M) : S.Blunt ↔ ¬S.Pointed := by
  rw [pointed_iff_not_blunt, Classical.not_not]

theorem Pointed.mono {S C₂ : ConvexCone R M} (h : S ≤ C₂) : S.Pointed → C₂.Pointed :=
  @h _

theorem Blunt.anti {S C₂ : ConvexCone R M} (h : C₂ ≤ S) : S.Blunt → C₂.Blunt :=
  (· ∘ @h 0)

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [SMul R M] (S : ConvexCone R M)

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def Flat : Prop :=
  ∃ x ∈ S, x ≠ (0 : M) ∧ -x ∈ S

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def Salient : Prop :=
  ∀ x ∈ S, x ≠ (0 : M) → -x ∉ S

theorem salient_iff_not_flat (S : ConvexCone R M) : S.Salient ↔ ¬S.Flat := by
  simp [Salient, Flat]

theorem Flat.mono {S C₂ : ConvexCone R M} (h : S ≤ C₂) : S.Flat → C₂.Flat
  | ⟨x, hxS, hx, hnxS⟩ => ⟨x, h hxS, hx, h hnxS⟩

theorem Salient.anti {S C₂ : ConvexCone R M} (h : C₂ ≤ S) : S.Salient → C₂.Salient :=
  fun hS x hxT hx hnT => hS x (h hxT) hx (h hnT)

/-- A flat cone is always pointed (contains `0`). -/
theorem Flat.pointed {S : ConvexCone R M} (hS : S.Flat) : S.Pointed := by
  obtain ⟨x, hx, _, hxneg⟩ := hS
  rw [Pointed, ← add_neg_cancel x]
  exact add_mem hx hxneg

/-- A blunt cone (one not containing `0`) is always salient. -/
theorem Blunt.salient {S : ConvexCone R M} : S.Blunt → S.Salient := by
  rw [salient_iff_not_flat, blunt_iff_not_pointed]
  exact mt Flat.pointed

/-- A pointed convex cone defines a preorder. -/
def toPreorder (h₁ : S.Pointed) : Preorder M where
  le x y := y - x ∈ S
  le_refl x := by rw [sub_self x]; exact h₁
  le_trans x y z xy zy := by simpa using add_mem zy xy

/-- A pointed and salient cone defines a partial order. -/
def toPartialOrder (h₁ : S.Pointed) (h₂ : S.Salient) : PartialOrder M :=
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
    IsOrderedAddMonoid M :=
  let _ := toPartialOrder S h₁ h₂
  { add_le_add_left := by
      intro a b hab c
      change c + b - (c + a) ∈ S
      rw [add_sub_add_left_eq_sub]
      exact hab }

end AddCommGroup

section Module

variable [AddCommMonoid M] [Module R M]

instance : Zero (ConvexCone R M) :=
  ⟨⟨0, fun _ _ => by simp, fun _ => by simp⟩⟩

@[simp]
theorem mem_zero (x : M) : x ∈ (0 : ConvexCone R M) ↔ x = 0 :=
  Iff.rfl

@[simp]
theorem coe_zero : ((0 : ConvexCone R M) : Set M) = 0 :=
  rfl

theorem pointed_zero : (0 : ConvexCone R M).Pointed := by rw [Pointed, mem_zero]

instance instAdd : Add (ConvexCone R M) :=
  ⟨fun K₁ K₂ =>
    { carrier := { z | ∃ x ∈ K₁, ∃ y ∈ K₂, x + y = z }
      smul_mem' := by
        rintro c hc _ ⟨x, hx, y, hy, rfl⟩
        rw [smul_add]
        use c • x, K₁.smul_mem hc hx, c • y, K₂.smul_mem hc hy
      add_mem' := by
        rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ y ⟨y₁, hy₁, y₂, hy₂, rfl⟩
        use x₁ + y₁, add_mem hx₁ hy₁, x₂ + y₂, add_mem hx₂ hy₂
        abel }⟩

@[simp]
theorem mem_add {K₁ K₂ : ConvexCone R M} {a : M} :
    a ∈ K₁ + K₂ ↔ ∃ x ∈ K₁, ∃ y ∈ K₂, x + y = a :=
  Iff.rfl

instance instAddZeroClass : AddZeroClass (ConvexCone R M) where
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp

instance instAddCommSemigroup : AddCommSemigroup (ConvexCone R M) where
  add := Add.add
  add_assoc _ _ _ := SetLike.coe_injective <| add_assoc _ _ _
  add_comm _ _ := SetLike.coe_injective <| add_comm _ _

end Module

end OrderedSemiring

section Field
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]
  {C : ConvexCone 𝕜 M} {s : Set M} {x : M}

/-- The cone hull of a convex set is simply the union of the open halflines through that set. -/
lemma mem_hull_of_convex (hs : Convex 𝕜 s) : x ∈ hull 𝕜 s ↔ ∃ r : 𝕜, 0 < r ∧ x ∈ r • s where
  mp hx := hull_min (C := {
              carrier := {y | ∃ r : 𝕜, 0 < r ∧ y ∈ r • s}
              smul_mem' := by
                intro r₁ hr₁ y ⟨r₂, hr₂, hy⟩
                refine ⟨r₁ * r₂, mul_pos hr₁ hr₂, ?_⟩
                rw [mul_smul]
                exact smul_mem_smul_set hy
              add_mem' := by
                rintro y₁ ⟨r₁, hr₁, hy₁⟩ y₂ ⟨r₂, hr₂, hy₂⟩
                refine ⟨r₁ + r₂, add_pos hr₁ hr₂, ?_⟩
                rw [hs.add_smul hr₁.le hr₂.le]
                exact add_mem_add hy₁ hy₂
            }) (fun y hy ↦ ⟨1, by simpa⟩) hx
  mpr := by rintro ⟨r, hr, y, hy, rfl⟩; exact (hull 𝕜 s).smul_mem hr <| subset_hull hy

lemma disjoint_hull_left_of_convex (hs : Convex 𝕜 s) : Disjoint (hull 𝕜 s) C ↔ Disjoint s C where
  mp := by rw [← disjoint_coe]; exact .mono_left subset_hull
  mpr := by
    simp_rw [← disjoint_coe, disjoint_left, SetLike.mem_coe, mem_hull_of_convex hs]
    rintro hsC _ ⟨r, hr, y, hy, rfl⟩
    exact (C.smul_mem_iff hr).not.mpr (hsC hy)

lemma disjoint_hull_right_of_convex (hs : Convex 𝕜 s) : Disjoint C (hull 𝕜 s) ↔ Disjoint ↑C s := by
  rw [disjoint_comm, disjoint_hull_left_of_convex hs, disjoint_comm]

end Field
end ConvexCone

namespace Submodule

/-! ### Submodules are cones -/


section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]

/-- Every submodule is trivially a convex cone. -/
def toConvexCone (S : Submodule R M) : ConvexCone R M where
  carrier := S
  smul_mem' c _ _ hx := S.smul_mem c hx
  add_mem' _ hx _ hy := add_mem hx hy

@[simp]
theorem coe_toConvexCone (S : Submodule R M) : ↑S.toConvexCone = (S : Set M) :=
  rfl

@[simp]
theorem mem_toConvexCone {x : M} {S : Submodule R M} : x ∈ S.toConvexCone ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem toConvexCone_le_iff {S C₂ : Submodule R M} : S.toConvexCone ≤ C₂.toConvexCone ↔ S ≤ C₂ :=
  Iff.rfl

@[simp]
theorem toConvexCone_bot : (⊥ : Submodule R M).toConvexCone = 0 :=
  rfl

@[simp]
theorem toConvexCone_top : (⊤ : Submodule R M).toConvexCone = ⊤ :=
  rfl

@[simp]
theorem toConvexCone_inf (S C₂ : Submodule R M) :
    (S ⊓ C₂).toConvexCone = S.toConvexCone ⊓ C₂.toConvexCone :=
  rfl

@[simp]
theorem pointed_toConvexCone (S : Submodule R M) : S.toConvexCone.Pointed :=
  S.zero_mem

end AddCommMonoid

end OrderedSemiring

end Submodule

/-! ### Positive cone of an ordered module -/

namespace ConvexCone

section PositiveCone
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M] [PartialOrder M]
  [IsOrderedAddMonoid M] [Module R M] [PosSMulMono R M] {x : M}

variable (R M) in
/-- The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : ConvexCone R M where
  carrier := Set.Ici 0
  smul_mem' _ hc _ (hx : _ ≤ _) := smul_nonneg hc.le hx
  add_mem' _ (hx : _ ≤ _) _ (hy : _ ≤ _) := add_nonneg hx hy

@[simp]
theorem mem_positive : x ∈ positive R M ↔ 0 ≤ x := .rfl

variable (R M) in
@[simp]
theorem coe_positive : ↑(positive R M) = Set.Ici (0 : M) :=
  rfl

/-- The positive cone of an ordered module is always salient. -/
theorem salient_positive {M : Type*} [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Module R M] [PosSMulMono R M] : Salient (positive R M) := fun x xs hx hx' =>
  lt_irrefl (0 : M)
    (calc
      0 < x := lt_of_le_of_ne xs hx.symm
      _ ≤ x + -x := le_add_of_nonneg_right hx'
      _ = 0 := add_neg_cancel x
      )

/-- The positive cone of an ordered module is always pointed. -/
theorem pointed_positive : Pointed (positive R M) :=
  le_refl 0

end PositiveCone

section StrictlyPositiveCone
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [PartialOrder M]
  [IsOrderedAddMonoid M] [Module R M] [PosSMulStrictMono R M] {x : M}

variable (R M) in
/-- The cone of strictly positive elements.

Note that this naming diverges from the mathlib convention of `pos` and `nonneg` due to "positive
cone" (`ConvexCone.positive`) being established terminology for the non-negative elements. -/
def strictlyPositive : ConvexCone R M where
  carrier := Set.Ioi 0
  smul_mem' _ hc _ (hx : _ < _) := smul_pos hc hx
  add_mem' _ hx _ hy := add_pos hx hy

@[simp]
theorem mem_strictlyPositive : x ∈ strictlyPositive R M ↔ 0 < x :=
  Iff.rfl

variable (R M) in
@[simp]
theorem coe_strictlyPositive : ↑(strictlyPositive R M) = Set.Ioi (0 : M) :=
  rfl

theorem strictlyPositive_le_positive : strictlyPositive R M ≤ positive R M := fun _ => le_of_lt

@[deprecated (since := "2025-04-20")]
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

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]

namespace Convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def toCone (s : Set M) (hs : Convex R s) : ConvexCone R M := by
  apply ConvexCone.mk (⋃ (c : R) (_ : 0 < c), c • s) <;> simp only [mem_iUnion, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + cy := add_pos cx_pos cy_pos
    refine ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, ?_⟩
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left₀ _ this.ne']

variable {s : Set M} (hs : Convex R s) {x : M}

theorem mem_toCone : x ∈ hs.toCone s ↔ ∃ c : R, 0 < c ∧ ∃ y ∈ s, c • y = x := by
  simp only [toCone, ConvexCone.mem_mk, mem_iUnion, mem_smul_set, eq_comm, exists_prop]

theorem mem_toCone' : x ∈ hs.toCone s ↔ ∃ c : R, 0 < c ∧ c • x ∈ s := by
  refine hs.mem_toCone.trans ⟨?_, ?_⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩

theorem subset_toCone : s ⊆ hs.toCone s := fun x hx =>
  hs.mem_toCone'.2 ⟨1, zero_lt_one, by rwa [one_smul]⟩

/-- `hs.toCone s` is the least cone that includes `s`. -/
theorem toCone_isLeast : IsLeast { t : ConvexCone R M | s ⊆ t } (hs.toCone s) := by
  refine ⟨hs.subset_toCone, fun t ht x hx => ?_⟩
  rcases hs.mem_toCone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)

theorem toCone_eq_sInf : hs.toCone s = sInf { t : ConvexCone R M | s ⊆ t } :=
  hs.toCone_isLeast.isGLB.sInf_eq.symm

end Convex

theorem convexHull_toCone_isLeast (s : Set M) :
    IsLeast { t : ConvexCone R M | s ⊆ t } ((convex_convexHull R s).toCone _) := by
  convert (convex_convexHull R s).toCone_isLeast using 1
  ext t
  exact ⟨fun h => convexHull_min h t.convex, (subset_convexHull R s).trans⟩

theorem convexHull_toCone_eq_sInf (s : Set M) :
    (convex_convexHull R s).toCone _ = sInf { t : ConvexCone R M | s ⊆ t } :=
  Eq.symm <| IsGLB.sInf_eq <| IsLeast.isGLB <| convexHull_toCone_isLeast s

end ConeFromConvex
