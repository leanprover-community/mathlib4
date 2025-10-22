/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Geometry.Convex.Cone.Basic

/-!
# Pointed cones

A *pointed cone* is defined to be a submodule of a module where the scalars are restricted to be
nonnegative. This is equivalent to saying that, as a set, a pointed cone is a convex cone which
contains `0`. This is a bundled version of `ConvexCone.Pointed`. We choose the submodule definition
as it allows us to use the `Module` API to work with convex cones.

-/

assert_not_exists TopologicalSpace Real Cardinal

variable {R E F G : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

/-- A pointed cone is a submodule of a module with scalars restricted to being nonnegative. -/
abbrev PointedCone (R E)
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E] :=
  Submodule {c : R // 0 ≤ c} E

namespace PointedCone

open Function

section Definitions

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
  {C C₁ C₂ : PointedCone R E} {x : E} {r : R}

/-- Every pointed cone is a convex cone. -/
@[coe]
def toConvexCone (C : PointedCone R E) : ConvexCone R E where
  carrier := C
  smul_mem' c hc _ hx := C.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' _ hx _ hy := C.add_mem hx hy

instance : Coe (PointedCone R E) (ConvexCone R E) where
  coe := toConvexCone

theorem toConvexCone_injective : Injective ((↑) : PointedCone R E → ConvexCone R E) :=
  fun _ _ => by simp [toConvexCone]

@[simp]
theorem pointed_toConvexCone (C : PointedCone R E) : (C : ConvexCone R E).Pointed := by
  simp [toConvexCone, ConvexCone.Pointed]

@[simp] lemma mem_toConvexCone : x ∈ C.toConvexCone ↔ x ∈ C := .rfl

@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

lemma convex (C : PointedCone R E) : Convex R (C : Set E) := C.toConvexCone.convex

instance instZero (C : PointedCone R E) : Zero C :=
  ⟨0, C.zero_mem⟩

nonrec lemma smul_mem (C : PointedCone R E) (hr : 0 ≤ r) (hx : x ∈ C) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx

/-- The `PointedCone` constructed from a pointed `ConvexCone`. -/
def _root_.ConvexCone.toPointedCone (C : ConvexCone R E) (hC : C.Pointed) : PointedCone R E where
  carrier := C
  add_mem' hx hy := C.add_mem hx hy
  zero_mem' := hC
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    rcases eq_or_lt_of_le hc with hzero | hpos
    · unfold ConvexCone.Pointed at hC
      convert hC
      simp [← hzero]
    · apply ConvexCone.smul_mem
      · convert hpos
      · exact hx

@[simp]
lemma _root_.ConvexCone.mem_toPointedCone {C : ConvexCone R E} (hC : C.Pointed) (x : E) :
    x ∈ C.toPointedCone hC ↔ x ∈ C :=
  Iff.rfl

@[simp, norm_cast]
lemma _root_.ConvexCone.coe_toPointedCone (C : ConvexCone R E) (hC : C.Pointed) :
    C.toPointedCone hC = C :=
  rfl

@[simp]
lemma _root_.ConvexCone.toPointedCone_top : (⊤ : ConvexCone R E).toPointedCone trivial = ⊤ := rfl

instance canLift : CanLift (ConvexCone R E) (PointedCone R E) (↑) ConvexCone.Pointed where
  prf C hC := ⟨C.toPointedCone hC, rfl⟩

/-- Construct a pointed cone from closure under two-element conical combinations.
I.e., a nonempty set closed under two-element conical combinations is a pointed cone. -/
def ofConeComb (C : Set E) (nonempty : C.Nonempty)
    (coneComb : ∀ x ∈ C, ∀ y ∈ C, ∀ a : R, 0 ≤ a → ∀ b : R, 0 ≤ b → a • x + b • y ∈ C) :
    PointedCone R E :=
  { toAddSubmonoid := {
      carrier := C
      zero_mem' := by
        obtain ⟨x, hx⟩ := nonempty
        simpa [zero_smul, add_zero] using coneComb x hx x hx 0 (le_refl 0) 0 (le_refl 0)
      add_mem' := by
        intro x y hx hy
        simpa [one_smul] using coneComb x hx y hy 1 zero_le_one 1 zero_le_one }
    smul_mem' := by
      intro c x hx
      have := coneComb x hx x hx (c : R) c.property 0 (le_refl 0)
      simp_all }

variable (R) in
/-- The span of a set `s` is the smallest pointed cone that contains `s`.

Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `s` w.r.t. nonnegative scalars. -/
abbrev span (s : Set E) : PointedCone R E := Submodule.span R≥0 s

lemma subset_span {s : Set E} : s ⊆ PointedCone.span R s := Submodule.subset_span

/-- Elements of PointedCone.span R s are expressible as conical combination of elements from s. -/
lemma mem_span_set {s : Set E} : x ∈ span R s ↔
      ∃ c : E →₀ R, ↑c.support ⊆ s ∧ (∀ y, 0 ≤ c y) ∧ c.sum (fun m r => r • m) = x := by
  rw [Submodule.mem_span_set]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.support, Subtype.val ∘ c, by simp [← Subtype.val_inj]⟩, hc, fun y ↦ (c y).2, rfl⟩
  · rintro ⟨c, hc, hc₀, rfl⟩
    exact ⟨⟨c.support, fun y ↦ ⟨c y, hc₀ _⟩, by simp⟩, hc, rfl⟩
end Definitions

section Maps

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [Module R E]
variable [AddCommMonoid F] [Module R F]
variable [AddCommMonoid G] [Module R G]

/-!

## Maps between pointed cones

There is already a definition of maps between submodules, `Submodule.map`. In our case, these maps
are induced from linear maps between the ambient modules that are linear over nonnegative scalars.
Such maps are unlikely to be of any use in practice. So, we construct some API to define maps
between pointed cones induced from linear maps between the ambient modules that are linear over
*all* scalars.

-/

/-- The image of a pointed cone under an `R`-linear map is a pointed cone. -/
def map (f : E →ₗ[R] F) (C : PointedCone R E) : PointedCone R F :=
  Submodule.map (f : E →ₗ[R≥0] F) C

@[simp, norm_cast]
theorem toConvexCone_map (C : PointedCone R E) (f : E →ₗ[R] F) :
    (C.map f : ConvexCone R F) = (C : ConvexCone R E).map f :=
  rfl

@[simp, norm_cast]
theorem coe_map (C : PointedCone R E) (f : E →ₗ[R] F) : (C.map f : Set F) = f '' C :=
  rfl

@[simp]
theorem mem_map {f : E →ₗ[R] F} {C : PointedCone R E} {y : F} : y ∈ C.map f ↔ ∃ x ∈ C, f x = y :=
  Iff.rfl

theorem map_map (g : F →ₗ[R] G) (f : E →ₗ[R] F) (C : PointedCone R E) :
    (C.map f).map g = C.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image g f C

@[simp]
theorem map_id (C : PointedCone R E) : C.map LinearMap.id = C :=
  SetLike.coe_injective <| Set.image_id _

/-- The preimage of a pointed cone under an `R`-linear map is a pointed cone. -/
def comap (f : E →ₗ[R] F) (C : PointedCone R F) : PointedCone R E :=
  Submodule.comap (f : E →ₗ[R≥0] F) C

@[simp, norm_cast]
theorem coe_comap (f : E →ₗ[R] F) (C : PointedCone R F) : (C.comap f : Set E) = f ⁻¹' C :=
  rfl

@[simp]
theorem comap_id (C : PointedCone R E) : C.comap LinearMap.id = C :=
  rfl

theorem comap_comap (g : F →ₗ[R] G) (f : E →ₗ[R] F) (C : PointedCone R G) :
    (C.comap g).comap f = C.comap (g.comp f) :=
  rfl

@[simp]
theorem mem_comap {f : E →ₗ[R] F} {C : PointedCone R F} {x : E} : x ∈ C.comap f ↔ f x ∈ C :=
  Iff.rfl

end Maps

section PositiveCone

variable (R E)
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]

/-- The positive cone is the pointed cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : PointedCone R E :=
  (ConvexCone.positive R E).toPointedCone ConvexCone.pointed_positive

@[simp]
theorem mem_positive {x : E} : x ∈ positive R E ↔ 0 ≤ x :=
  Iff.rfl

@[simp, norm_cast]
theorem toConvexCone_positive : ↑(positive R E) = ConvexCone.positive R E :=
  rfl

end PositiveCone

section OrderedAddCommGroup
variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [PartialOrder E]
  [IsOrderedAddMonoid E] [Module R E]

/-- Constructs an ordered module given an ordered group, a cone, and a proof that
the order relation is the one defined by the cone. -/
lemma to_isOrderedModule (C : PointedCone R E) (h : ∀ x y : E, x ≤ y ↔ y - x ∈ C) :
    IsOrderedModule R E := .of_smul_nonneg <| by simp +contextual [h, C.smul_mem]

end OrderedAddCommGroup
end PointedCone
