/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
module

public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Order.Nonneg.Module
public import Mathlib.Geometry.Convex.Cone.Basic


/-!
# Pointed cones

A *pointed cone* is defined to be a submodule of a module where the scalars are restricted to be
nonnegative. This is equivalent to saying that, as a set, a pointed cone is a convex cone which
contains `0`. This is a bundled version of `ConvexCone.Pointed`. We choose the submodule definition
as it allows us to use the `Module` API to work with convex cones.

-/

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

variable {R E F G : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

/-- A pointed cone is a submodule of a module with scalars restricted to being nonnegative. -/
abbrev PointedCone (R E)
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E] :=
  Submodule {c : R // 0 ≤ c} E

namespace PointedCone

open Function Submodule

section Submodule

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C : PointedCone R E}

set_option backward.isDefEq.respectTransparency false in
/-- A submodule is a pointed cone. -/
@[coe] abbrev ofSubmodule (S : Submodule R E) : PointedCone R E := S.restrictScalars _

instance : Coe (Submodule R E) (PointedCone R E) := ⟨ofSubmodule⟩

@[simp] lemma coe_ofSubmodule (S : Submodule R E) : (ofSubmodule S : Set E) = S := rfl

lemma mem_ofSubmodule_iff {S : Submodule R E} {x : E} : x ∈ (S : PointedCone R E) ↔ x ∈ S := by rfl

set_option backward.isDefEq.respectTransparency false in
lemma ofSubmodule_inj {S T : Submodule R E} : ofSubmodule S = ofSubmodule T ↔ S = T :=
  restrictScalars_inj ..

set_option backward.isDefEq.respectTransparency false in
/-- Coercion from submodules to pointed cones as an order embedding. -/
abbrev ofSubmoduleEmbedding : Submodule R E ↪o PointedCone R E :=
  restrictScalarsEmbedding ..

set_option backward.isDefEq.respectTransparency false in
/-- Coercion from submodules to pointed cones as a lattice homomorphism. -/
abbrev ofSubmoduleLatticeHom : CompleteLatticeHom (Submodule R E) (PointedCone R E) :=
  restrictScalarsLatticeHom ..

set_option backward.isDefEq.respectTransparency false in
lemma ofSubmodule_inf (S T : Submodule R E) : S ⊓ T = (S ⊓ T : PointedCone R E) :=
  restrictScalars_inf _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma ofSubmodule_sup (S T : Submodule R E) : S ⊔ T = (S ⊔ T : PointedCone R E) :=
  restrictScalars_sup _ _ _

lemma ofSubmodule_sInf (s : Set (Submodule R E)) : sInf s = sInf (ofSubmodule '' s) :=
  ofSubmoduleLatticeHom.map_sInf' s

lemma ofSubmodule_iInf (s : Set (Submodule R E)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R E) := by
  rw [← sInf_eq_iInf, ofSubmodule_sInf, sInf_eq_iInf, iInf_image]

lemma ofSubmodule_sSup (s : Set (Submodule R E)) : sSup s = sSup (ofSubmodule '' s) :=
  ofSubmoduleLatticeHom.map_sSup' s

lemma ofSubmodule_iSup (s : Set (Submodule R E)) : ⨆ S ∈ s, S = ⨆ S ∈ s, (S : PointedCone R E) := by
  rw [← sSup_eq_iSup, ofSubmodule_sSup, sSup_eq_iSup, iSup_image]

end Submodule

section ConvexCone

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C C₁ C₂ : PointedCone R E} {x : E} {r : R}

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

@[aesop 90% (rule_sets := [SetLike])]
nonrec lemma smul_mem (C : PointedCone R E) (hr : 0 ≤ r) (hx : x ∈ C) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx

set_option backward.isDefEq.respectTransparency false in
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

instance : CanLift (ConvexCone R E) (PointedCone R E) (↑) ConvexCone.Pointed where
  prf C hC := ⟨C.toPointedCone hC, rfl⟩

end ConvexCone

section Definitions

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C : PointedCone R E} {x : E}

/-- Construct a pointed cone from closure under two-element conical combinations.
I.e., a nonempty set closed under two-element conical combinations is a pointed cone. -/
@[simps!]
def ofConeComb (C : Set E) (nonempty : C.Nonempty)
    (coneComb : ∀ x ∈ C, ∀ y ∈ C, ∀ a : R, 0 ≤ a → ∀ b : R, 0 ≤ b → a • x + b • y ∈ C) :
    PointedCone R E :=
  .ofLinearComb C nonempty fun x hx y hy ⟨a, ha⟩ ⟨b, hb⟩ => coneComb x hx y hy a ha b hb

variable (R) in
/-- The cone hull of a set `s` is the smallest pointed cone that contains `s`.

Pointed cones being defined as submodules over nonnegative scalars, this is implemented as
the submodule span of `s` w.r.t. nonnegative scalars. -/
abbrev hull (s : Set E) : PointedCone R E := span R≥0 s

lemma subset_hull {s : Set E} : s ⊆ PointedCone.hull R s := subset_span

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias subset_span := subset_hull

/-- Elements of the cone hull are expressible as conical combination of elements from s. -/
lemma mem_hull_set {s : Set E} : x ∈ hull R s ↔
      ∃ c : E →₀ R, ↑c.support ⊆ s ∧ (∀ y, 0 ≤ c y) ∧ c.sum (fun m r => r • m) = x := by
  rw [mem_span_set]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.support, Subtype.val ∘ c, by simp [← Subtype.val_inj]⟩, hc, fun y ↦ (c y).2, rfl⟩
  · rintro ⟨c, hc, hc₀, rfl⟩
    exact ⟨⟨c.support, fun y ↦ ⟨c y, hc₀ _⟩, by simp⟩, hc, rfl⟩

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias mem_span_set := mem_hull_set

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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

section Lineal

open Pointwise

variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

/-- The lineality space of a cone `C` is the submodule given by `C ⊓ -C`. -/
@[simps!]
def lineal (C : PointedCone R E) : Submodule R E where
  __ := C.support
  smul_mem' r _ hx := by
    by_cases hr : 0 ≤ r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
    · have hr := le_of_lt <| neg_pos_of_neg <| lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)
@[simp]
lemma ofSubmodule_lineal (C : PointedCone R E) : C.lineal = C ⊓ -C :=
  rfl

@[simp]
lemma mem_lineal {C : PointedCone R E} {x : E} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := by
  rfl

@[simp]
theorem support_eq {C : PointedCone R E} : C.support = C.lineal.toAddSubgroup :=
  rfl

/-- The lineality space of a cone is the largest submodule contained in the cone. -/
theorem gc_ofSubmodule_lineal :
    GaloisConnection (α := Submodule R E) ofSubmodule lineal :=
  fun _ _ ↦ ⟨fun _ _ ↦ by aesop, fun h _ hx ↦ (h hx).1⟩

lemma lineal_le (C : PointedCone R E) : C.lineal ≤ C := gc_ofSubmodule_lineal.l_u_le C

theorem lineal_eq_sSup (C : PointedCone R E) : C.lineal = sSup {S : Submodule R E | S ≤ C} := by
  simp_rw [gc_ofSubmodule_lineal.le_iff_le, Set.Iic_def, csSup_Iic]

end Lineal

section Salient
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

/-- A pointed cone is salient iff the intersection of the cone with its negative
is the set `{0}`. -/
lemma salient_iff_inter_neg_eq_singleton (C : PointedCone R E) :
    (C : ConvexCone R E).Salient ↔ (C ∩ -C : Set E) = {0} := by
  simp [ConvexCone.Salient, Set.eq_singleton_iff_unique_mem, not_imp_not]

end Salient

end PointedCone
