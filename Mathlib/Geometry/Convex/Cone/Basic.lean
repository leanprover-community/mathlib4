/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.Hull

/-!
# Convex cones

In an `R`-module `M`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
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

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

open Set LinearMap Pointwise

variable {𝕜 R G M N O : Type*}

/-! ### Definition of `ConvexCone` and basic properties -/

section Definitions

variable [Semiring R] [PartialOrder R]

variable (R M) in
/-- A convex cone is a subset `s` of an `R`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
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
  sInf_le C C hC := by rw [← SetLike.coe_subset_coe, coe_sInf]; exact biInter_subset_of_mem hC
  le_sInf C C hC := by rw [← SetLike.coe_subset_coe, coe_sInf]; exact subset_iInter₂ hC

variable (R s) in
/-- The cone hull of a set. The smallest convex cone containing that set. -/
def hull : ConvexCone R M := sInf {C : ConvexCone R M | s ⊆ C}

lemma subset_hull : s ⊆ hull R s := by simp [hull]

lemma hull_min (hsC : s ⊆ C) : hull R s ≤ C := sInf_le hsC

lemma hull_le_iff : hull R s ≤ C ↔ s ⊆ C := ⟨subset_hull.trans, hull_min⟩

lemma gc_hull_coe : GaloisConnection (hull R : Set M → ConvexCone R M) (↑) :=
  fun _C _s ↦ hull_le_iff

/-- Galois insertion between `ConvexCone` and `SetLike.coe`. -/
protected def gi : GaloisInsertion (hull R : Set M → ConvexCone R M) (↑) where
  gc := gc_hull_coe
  le_l_u _ := subset_hull
  choice s hs := (hull R s).copy s <| subset_hull.antisymm hs
  choice_eq _ _ := copy_eq _ _ _

instance : Bot (ConvexCone R M) :=
  ⟨⟨∅, fun _ _ _ => False.elim, fun _ => False.elim⟩⟩

@[simp] lemma notMem_bot : x ∉ (⊥ : ConvexCone R M) := id

@[simp, norm_cast] lemma coe_bot : ↑(⊥ : ConvexCone R M) = (∅ : Set M) := rfl

@[simp, norm_cast]
lemma coe_eq_empty : (C : Set M) = ∅ ↔ C = ⊥ := by rw [← coe_bot (R := R)]; norm_cast

instance : CompleteLattice (ConvexCone R M) where
  bot := ⊥
  bot_le _ := empty_subset _
  __ := instCompleteSemilatticeInf
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

variable [Module R M] (C : ConvexCone R M)

protected theorem convex : Convex R (C : Set M) :=
  convex_iff_forall_pos.2 fun _ hx _ hy _ _ ha hb _ ↦ add_mem (C.smul_mem ha hx) (C.smul_mem hb hy)

end Module

section Maps

variable [AddCommMonoid N] [AddCommMonoid O]
variable [Module R M] [Module R N] [Module R O]

/-- The image of a convex cone under an `R`-linear map is a convex cone. -/
def map (f : M →ₗ[R] N) (C : ConvexCone R M) : ConvexCone R N where
  carrier := f '' C
  smul_mem' := fun c hc _ ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (C.smul_mem hc hx)
  add_mem' := fun _ ⟨x₁, hx₁, hy₁⟩ _ ⟨x₂, hx₂, hy₂⟩ =>
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

/-- The preimage of a convex cone under an `R`-linear map is a convex cone. -/
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
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc) h, C.smul_mem hc⟩

end MulAction
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
  fun hS x hxT hx hnT => hS x (h hxT) hx (h hnT)

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
      have h' : b - a ≠ 0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }

/-- A pointed and salient cone defines an `IsOrderedAddMonoid`. -/
lemma to_isOrderedAddMonoid (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient) :
    let _ := toPartialOrder C h₁ h₂
    IsOrderedAddMonoid G where
  __ := toPartialOrder C h₁ h₂
  add_le_add_left a b hab c := show b + c - (a + c) ∈ C by rwa [add_sub_add_right_eq_sub]

end AddCommGroup

section Module

variable [AddCommMonoid M] [Module R M] {C₁ C₂ : ConvexCone R M} {x : M}

instance : Zero (ConvexCone R M) :=
  ⟨⟨0, fun _ _ => by simp, fun _ => by simp⟩⟩

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
  add_assoc _ _ _ := SetLike.coe_injective <| add_assoc _ _ _
  add_comm _ _ := SetLike.coe_injective <| add_comm _ _

section Generating

/-- A convex cone `C` is generating if its linear span is the entire `R`-module `M`.

`IsGenerating` is equivalent to `IsReproducing` modulo some conditions.
See `IsReproducing.isGenerating` and `IsGenerating.isReproducing` for details. -/
@[simp] def IsGenerating (C : ConvexCone R M) : Prop :=
  Submodule.span R (C : Set M) = ⊤

/-- A sufficient criteria for a convex cone `C` to be generating is that top is less than or equal
to the linear span of `C`. -/
theorem IsGenerating.of_top_le_span {C : ConvexCone R M} (h : ⊤ ≤ Submodule.span R (C : Set M)) :
    C.IsGenerating :=
  eq_top_iff.mpr h

/-- The linear span of a generating convex cone equals top. -/
lemma IsGenerating.span_eq_top {C : ConvexCone R M} (hC : C.IsGenerating) :
    Submodule.span R (C : Set M) = ⊤ :=
  hC

/-- Top is less than or equal to the linear span of a generating convex cone. -/
lemma IsGenerating.top_le_span {C : ConvexCone R M} (hC : C.IsGenerating) :
    ⊤ ≤ Submodule.span R (C : Set M) :=
  hC.span_eq_top.ge

/-- The whole `R`-module `M` (viewed as the top convex cone) is generating. -/
theorem isGenerating_top : (⊤ : ConvexCone R M).IsGenerating := by
  simp

/-- The empty convex cone is generating iff the module is a subsingleton. -/
theorem isGenerating_bot_iff : (⊥ : ConvexCone R M).IsGenerating ↔ Subsingleton M := by
  simpa only [IsGenerating, coe_bot, Submodule.span_empty, ← Submodule.subsingleton_iff R] using
    subsingleton_iff_bot_eq_top

/-- In a subsingleton module, the empty convex cone is generating. -/
theorem isGenerating_bot [Subsingleton M] : (⊥ : ConvexCone R M).IsGenerating :=
  isGenerating_bot_iff.mpr inferInstance

/-- A convex cone containing a generating cone is also a generating cone. -/
@[gcongr]
theorem IsGenerating.mono (h : C₁ ≤ C₂) (hgen : C₁.IsGenerating) : C₂.IsGenerating := by
  rw [IsGenerating, ← top_le_iff] at hgen ⊢
  exact hgen.trans (Submodule.span_mono h)

/-- A convex cone is reproducing if its set of element differences equals the entire module,
i.e., every element of `M` can be written as a difference of two elements of `C`.

See also (`IsGenerating`). -/
def IsReproducing [AddCommGroup M] (C : ConvexCone R M) : Prop :=
  (C : Set M) - (C : Set M) = Set.univ

/-- A sufficient criterion for a convex cone `C` to be reproducing is that `Set.univ` is a subset
of `C - C`. -/
theorem IsReproducing.of_univ_subset [AddCommGroup M] {C : ConvexCone R M}
    (h : Set.univ ⊆ (C : Set M) - (C : Set M)) : C.IsReproducing :=
  Set.eq_univ_iff_forall.mpr fun _ ↦ h (Set.mem_univ _)

/-- The set difference of a reproducing cone with itself equals `Set.univ`. -/
lemma IsReproducing.sub_eq_univ [AddCommGroup M] {C : ConvexCone R M} (hC : C.IsReproducing) :
    (C : Set M) - (C : Set M) = Set.univ :=
  hC

/-- A reproducing cone is generating. -/
theorem IsReproducing.isGenerating {R : Type*} {M : Type*} [Ring R] [PartialOrder R]
    [AddCommGroup M] [Module R M] {C : ConvexCone R M} (h : C.IsReproducing) :
    C.IsGenerating := by
  rw [IsGenerating, eq_top_iff]
  rintro x -
  rw [IsReproducing, Set.eq_univ_iff_forall] at h
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_sub.mp (h x)
  exact sub_mem (Submodule.subset_span hy) (Submodule.subset_span hz)

/-- A generating cone is reproducing. -/
theorem IsGenerating.isReproducing {R : Type*} {M : Type*} [Ring R] [LinearOrder R]
    [AddLeftStrictMono R] [AddCommGroup M] [Nontrivial M] [Module R M] {C : ConvexCone R M}
    (h : C.IsGenerating) :
    C.IsReproducing := by
  rw [IsReproducing, Set.eq_univ_iff_forall]
  intro x
  -- A generating cone in a nontrivial module must be nonempty
  have hne : (C : Set M).Nonempty := Set.nonempty_iff_ne_empty.2 fun h' =>
      not_subsingleton M <| isGenerating_bot_iff.1 <| coe_eq_empty.1 h' ▸ h
  -- Build the submodule S = C - C and show span C ⊆ S
  let S : Submodule R M := {
    carrier := (C : Set M) - (C : Set M)
    add_mem' := by
      rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨y₁ + y₂, C.add_mem hy₁ hy₂, z₁ + z₂, C.add_mem hz₁ hz₂, add_sub_add_comm ..⟩
    zero_mem' := by
      obtain ⟨c, hc⟩ := hne
      exact ⟨c, hc, c, hc, sub_self c⟩
    smul_mem' := by
      rintro r _ ⟨y, hy, z, hz, rfl⟩
      simp only [Set.mem_sub, SetLike.mem_coe]
      rcases lt_trichotomy r 0 with hr | rfl | hr
      · -- r < 0: use (-r) • z - (-r) • y = r • (y - z)
        refine ⟨(-r) • z, C.smul_mem (neg_pos.mpr hr) hz,
               (-r) • y, C.smul_mem (neg_pos.mpr hr) hy, ?_⟩
        rw [neg_smul, neg_smul, neg_sub_neg, smul_sub]
      · -- r = 0
        simp only [zero_smul]
        obtain ⟨c, hc⟩ := hne
        exact ⟨c, hc, c, hc, sub_self c⟩
      · -- r > 0: use r • y - r • z
        exact ⟨r • y, C.smul_mem hr hy, r • z, C.smul_mem hr hz, (smul_sub r y z).symm⟩}
  have hCS : (C : Set M) ⊆ S := fun x hx ↦
    let ⟨c, hc⟩ := hne; ⟨x + c, C.add_mem hx hc, c, hc, add_sub_cancel_right x c⟩
  exact (h ▸ Submodule.span_le.mpr hCS) trivial

/-- A convex cone is generating iff every element is a difference of cone elements. -/
theorem isGenerating_iff_isReproducing {R : Type*} {M : Type*} [Ring R] [LinearOrder R]
    [AddLeftStrictMono R] [AddCommGroup M] [Nontrivial M] [Module R M] {C : ConvexCone R M} :
    C.IsGenerating ↔ C.IsReproducing :=
  ⟨IsGenerating.isReproducing, IsReproducing.isGenerating⟩

end Generating

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

/-- The cone hull of a convex set is simply the union of the open halflines through that set. -/
lemma coe_hull_of_convex (hs : Convex 𝕜 s) : hull 𝕜 s = {x | ∃ r : 𝕜, 0 < r ∧ x ∈ r • s} := by
  ext; exact mem_hull_of_convex hs

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

@[simp] lemma toConvexCone_bot : (⊥ : Submodule R M).toConvexCone = 0 := rfl
@[simp] lemma toConvexCone_top : (⊤ : Submodule R M).toConvexCone = ⊤ := rfl

@[simp]
lemma toConvexCone_inf (C₁ C₂ : Submodule R M) :
    (C₁ ⊓ C₂).toConvexCone = C₁.toConvexCone ⊓ C₂.toConvexCone := rfl

@[simp]
lemma pointed_toConvexCone (C : Submodule R M) : C.toConvexCone.Pointed := C.zero_mem

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

lemma strictlyPositive_le_positive : strictlyPositive R M ≤ positive R M := fun _ => le_of_lt

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

theorem subset_toCone : s ⊆ hs.toCone s := fun x hx =>
  hs.mem_toCone'.2 ⟨1, zero_lt_one, by rwa [one_smul]⟩

/-- `hs.toCone s` is the least cone that includes `s`. -/
theorem toCone_isLeast : IsLeast { t : ConvexCone 𝕜 M | s ⊆ t } (hs.toCone s) := by
  refine ⟨hs.subset_toCone, fun t ht x hx => ?_⟩
  rcases hs.mem_toCone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)

theorem toCone_eq_sInf : hs.toCone s = sInf { t : ConvexCone 𝕜 M | s ⊆ t } :=
  hs.toCone_isLeast.isGLB.sInf_eq.symm

end Convex

theorem convexHull_toCone_isLeast (s : Set M) :
    IsLeast { t : ConvexCone 𝕜 M | s ⊆ t } ((convex_convexHull 𝕜 s).toCone _) := by
  convert (convex_convexHull 𝕜 s).toCone_isLeast using 1
  ext t
  exact ⟨fun h => convexHull_min h t.convex, (subset_convexHull 𝕜 s).trans⟩

theorem convexHull_toCone_eq_sInf (s : Set M) :
    (convex_convexHull 𝕜 s).toCone _ = sInf { t : ConvexCone 𝕜 M | s ⊆ t } :=
  Eq.symm <| IsGLB.sInf_eq <| IsLeast.isGLB <| convexHull_toCone_isLeast s

end ConeFromConvex
