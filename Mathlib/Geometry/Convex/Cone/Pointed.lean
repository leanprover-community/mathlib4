/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
module

public import Mathlib.Algebra.Group.Submonoid.Support
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

variable {R M : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

variable (R M) in
/-- A pointed cone is a submodule of a module with scalars restricted to being nonnegative. -/
abbrev PointedCone
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M] [Module R M] :=
  Submodule {c : R // 0 ≤ c} M

namespace PointedCone

open Submodule Pointwise

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] {C : PointedCone R M}

section ofSubmodule

set_option backward.isDefEq.respectTransparency false in
/-- A submodule is a pointed cone. -/
@[coe] abbrev ofSubmodule (S : Submodule R M) : PointedCone R M := S.restrictScalars _

instance : Coe (Submodule R M) (PointedCone R M) := ⟨ofSubmodule⟩

@[simp] lemma coe_ofSubmodule (S : Submodule R M) : (ofSubmodule S : Set M) = S := rfl

lemma mem_ofSubmodule_iff {S : Submodule R M} {x : M} : x ∈ (S : PointedCone R M) ↔ x ∈ S := by rfl

set_option backward.isDefEq.respectTransparency false in
lemma ofSubmodule_inj {S T : Submodule R M} : ofSubmodule S = ofSubmodule T ↔ S = T :=
  restrictScalars_inj ..

set_option backward.isDefEq.respectTransparency false in
/-- Coercion from submodules to pointed cones as an order embedding. -/
abbrev ofSubmoduleEmbedding : Submodule R M ↪o PointedCone R M :=
  restrictScalarsEmbedding ..

set_option backward.isDefEq.respectTransparency false in
/-- Coercion from submodules to pointed cones as a lattice homomorphism. -/
abbrev ofSubmoduleLatticeHom : CompleteLatticeHom (Submodule R M) (PointedCone R M) :=
  restrictScalarsLatticeHom ..

set_option backward.isDefEq.respectTransparency false in
lemma ofSubmodule_inf (S T : Submodule R M) : S ⊓ T = (S ⊓ T : PointedCone R M) :=
  restrictScalars_inf _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma ofSubmodule_sup (S T : Submodule R M) : S ⊔ T = (S ⊔ T : PointedCone R M) :=
  restrictScalars_sup _ _ _

lemma ofSubmodule_sInf (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
  ofSubmoduleLatticeHom.map_sInf' s

lemma ofSubmodule_iInf (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
  rw [← sInf_eq_iInf, ofSubmodule_sInf, sInf_eq_iInf, iInf_image]

lemma ofSubmodule_sSup (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
  ofSubmoduleLatticeHom.map_sSup' s

lemma ofSubmodule_iSup (s : Set (Submodule R M)) : ⨆ S ∈ s, S = ⨆ S ∈ s, (S : PointedCone R M) := by
  rw [← sSup_eq_iSup, ofSubmodule_sSup, sSup_eq_iSup, iSup_image]

end ofSubmodule

section toConvexCone

variable (C) in
/-- Every pointed cone is a convex cone. -/
@[coe]
def toConvexCone : ConvexCone R M where
  carrier := C
  smul_mem' c hc _ hx := C.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' _ hx _ hy := C.add_mem hx hy

instance : Coe (PointedCone R M) (ConvexCone R M) where
  coe := toConvexCone

theorem toConvexCone_injective : Function.Injective ((↑) : PointedCone R M → ConvexCone R M) :=
  fun _ _ => by simp [toConvexCone]

variable (C) in
@[simp]
theorem pointed_toConvexCone : (C : ConvexCone R M).Pointed := by
  simp [toConvexCone, ConvexCone.Pointed]

@[simp] lemma mem_toConvexCone {x : M} : x ∈ C.toConvexCone ↔ x ∈ C := .rfl

@[ext] lemma ext {C₁ C₂ : PointedCone R M} (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

variable (C) in
lemma convex : Convex R (C : Set M) := C.toConvexCone.convex

@[aesop 90% (rule_sets := [SetLike])]
nonrec lemma smul_mem {r : R} (hr : 0 ≤ r) {x : M} (hx : x ∈ C) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx

end toConvexCone

section toPointedCone

variable {C' : ConvexCone R M} (hC' : C'.Pointed)

set_option backward.isDefEq.respectTransparency false in
/-- The `PointedCone` constructed from a pointed `ConvexCone`. -/
def _root_.ConvexCone.toPointedCone : PointedCone R M where
  carrier := C'
  add_mem' hx hy := C'.add_mem hx hy
  zero_mem' := hC'
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    rcases eq_or_lt_of_le hc with hzero | hpos
    · unfold ConvexCone.Pointed at hC'
      convert hC'
      simp [← hzero]
    · apply ConvexCone.smul_mem
      · convert hpos
      · exact hx

@[simp]
lemma _root_.ConvexCone.mem_toPointedCone {x : M} :
    x ∈ C'.toPointedCone hC' ↔ x ∈ C' :=
  Iff.rfl

@[simp, norm_cast]
lemma _root_.ConvexCone.coe_toPointedCone :
    C'.toPointedCone hC' = C' :=
  rfl

@[simp]
lemma _root_.ConvexCone.toPointedCone_top : (⊤ : ConvexCone R M).toPointedCone trivial = ⊤ := rfl

instance : CanLift (ConvexCone R M) (PointedCone R M) (↑) ConvexCone.Pointed where
  prf C hC := ⟨C.toPointedCone hC, rfl⟩

end toPointedCone

/-- Construct a pointed cone from closure under two-element conical combinations.
I.e., a nonempty set closed under two-element conical combinations is a pointed cone. -/
@[simps!]
def ofConeComb (s : Set M) (nonempty : s.Nonempty)
    (coneComb : ∀ x ∈ s, ∀ y ∈ s, ∀ a : R, 0 ≤ a → ∀ b : R, 0 ≤ b → a • x + b • y ∈ s) :
    PointedCone R M :=
  .ofLinearComb s nonempty fun x hx y hy ⟨a, ha⟩ ⟨b, hb⟩ => coneComb x hx y hy a ha b hb

variable (R) in
/-- The cone hull of a set `s` is the smallest pointed cone that contains `s`.

Pointed cones being defined as submodules over nonnegative scalars, this is implemented as
the submodule span of `s` w.r.t. nonnegative scalars. -/
abbrev hull (s : Set M) : PointedCone R M := span R≥0 s

lemma subset_hull {s : Set M} : s ⊆ PointedCone.hull R s := subset_span

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias subset_span := subset_hull

/-- Elements of the cone hull are expressible as conical combination of elements from s. -/
lemma mem_hull_set {s : Set M} {x : M} : x ∈ hull R s ↔
      ∃ c : M →₀ R, ↑c.support ⊆ s ∧ (∀ y, 0 ≤ c y) ∧ c.sum (fun m r => r • m) = x := by
  rw [mem_span_set]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.support, Subtype.val ∘ c, by simp [← Subtype.val_inj]⟩, hc, fun y ↦ (c y).2, rfl⟩
  · rintro ⟨c, hc, hc₀, rfl⟩
    exact ⟨⟨c.support, fun y ↦ ⟨c y, hc₀ _⟩, by simp⟩, hc, rfl⟩

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias mem_span_set := mem_hull_set

section Maps

variable {F G : Type*} [AddCommMonoid F] [Module R F] [AddCommMonoid G] [Module R G]
         (f : M →ₗ[R] F) (g : F →ₗ[R] G)
         (C : PointedCone R M) (C' : PointedCone R F) (C'' : PointedCone R G)

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
def map : PointedCone R F :=
  Submodule.map (f : M →ₗ[R≥0] F) C

@[simp, norm_cast]
theorem toConvexCone_map :
    (C.map f : ConvexCone R F) = (C : ConvexCone R M).map f :=
  rfl

@[simp, norm_cast]
theorem coe_map : (C.map f : Set F) = f '' C :=
  rfl

variable {f C} in
@[simp]
theorem mem_map {y : F} : y ∈ C.map f ↔ ∃ x ∈ C, f x = y :=
  Iff.rfl

theorem map_map :
    (C.map f).map g = C.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image g f C

@[simp]
theorem map_id : C.map LinearMap.id = C :=
  SetLike.coe_injective <| Set.image_id _

set_option backward.isDefEq.respectTransparency false in
/-- The preimage of a pointed cone under an `R`-linear map is a pointed cone. -/
def comap : PointedCone R M :=
  Submodule.comap (f : M →ₗ[R≥0] F) C'

@[simp, norm_cast]
theorem coe_comap : (C'.comap f : Set M) = f ⁻¹' C' :=
  rfl

@[simp]
theorem comap_id : C.comap LinearMap.id = C :=
  rfl

theorem comap_comap :
    (C''.comap g).comap f = C''.comap (g.comp f) :=
  rfl

variable {f C'} in
@[simp]
theorem mem_comap {x : M} : x ∈ C'.comap f ↔ f x ∈ C' :=
  Iff.rfl

end Maps

section PartialOrder

variable [PartialOrder M] [IsOrderedAddMonoid M] [PosSMulMono R M]

variable (R M) in
/-- The positive cone is the pointed cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : PointedCone R M :=
  (ConvexCone.positive R M).toPointedCone ConvexCone.pointed_positive

@[simp]
theorem mem_positive {x : M} : x ∈ positive R M ↔ 0 ≤ x :=
  Iff.rfl

variable (R M) in
@[simp, norm_cast]
theorem toConvexCone_positive : ↑(positive R M) = ConvexCone.positive R M :=
  rfl

end PartialOrder

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module R M] (C : PointedCone R M)

set_option backward.isDefEq.respectTransparency false in
lemma neg_ofSubmodule (S : Submodule R M) :  -(ofSubmodule S) = ofSubmodule (-S) :=
  neg_restrictScalars S

/-- A pointed cone is salient iff the intersection of the cone with its negative
is the set `{0}`. -/
lemma salient_iff_inter_neg_eq_singleton :
    (C : ConvexCone R M).Salient ↔ (C ∩ -C : Set M) = {0} := by
  simp [ConvexCone.Salient, Set.eq_singleton_iff_unique_mem, not_imp_not]

end AddCommGroup

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]

section PartialOrder

section AddCommGroup

variable [PartialOrder R] [IsOrderedRing R] {C : PointedCone R M}

lemma sup_inf_assoc_of_le_submodule (D : PointedCone R M)
    {S : Submodule R M} (hCS : C ≤ S) : (C ⊔ D) ⊓ S = C ⊔ (D ⊓ S) :=
  sup_inf_assoc_of_le_of_neg_le _ hCS (by simpa [Submodule.neg_le])

lemma inf_sup_assoc_of_le_of_submodule_le (D : PointedCone R M)
    {S : Submodule R M} (hSC : S ≤ C) : (C ⊓ D) ⊔ S = C ⊓ (D ⊔ S) :=
  inf_sup_assoc_of_le_of_neg_le _ hSC (by simpa [Submodule.neg_le])

end AddCommGroup

end PartialOrder

variable [LinearOrder R] [IsOrderedRing R] {C : PointedCone R M}

section Lineal

variable (C)

/-- The lineality space of a cone `C` is the submodule given by `C ⊓ -C`. -/
@[simps!]
def lineal : Submodule R M where
  __ := C.support
  smul_mem' r _ hx := by
    by_cases hr : 0 ≤ r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
    · have hr := le_of_lt <| neg_pos_of_neg <| lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)

@[simp]
lemma ofSubmodule_lineal : C.lineal = C ⊓ -C :=
  rfl

variable {C} in
@[simp]
lemma mem_lineal {x : M} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := by
  rfl

@[simp]
theorem support_eq : C.support = C.lineal.toAddSubgroup :=
  rfl

/-- The lineality space of a cone is the largest submodule contained in the cone. -/
theorem gc_ofSubmodule_lineal :
    GaloisConnection (α := Submodule R M) ofSubmodule lineal :=
  fun _ _ ↦ ⟨fun _ _ ↦ by aesop, fun h _ hx ↦ (h hx).1⟩

lemma lineal_le : C.lineal ≤ C := gc_ofSubmodule_lineal.l_u_le C

theorem lineal_eq_sSup : C.lineal = sSup {S : Submodule R M | S ≤ C} := by
  simp_rw [gc_ofSubmodule_lineal.le_iff_le, Set.Iic_def, csSup_Iic]

end Lineal

section PartialOrder

variable [PartialOrder M] [IsOrderedAddMonoid M]

/-- Constructs an ordered module given an ordered group, a cone, and a proof that
the order relation is the one defined by the cone. -/
lemma to_isOrderedModule (h : ∀ x y : M, x ≤ y ↔ y - x ∈ C) :
    IsOrderedModule R M := .of_smul_nonneg <| by simp +contextual [h, C.smul_mem]

end PartialOrder

end Ring

end PointedCone
