/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade, Yury Kudryashov, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Order.Nonneg.Module
public import Mathlib.Analysis.Convex.Hull


/-!
# Pointed cones

In an `R`-module `M`, a *pointed cone* is a set `s` closed under conical combinations; that is,
such that `a • x + b • y ∈ s` whenever `x, y ∈ s` and `a, b ≥ 0`.

We define a pointed cone as a submodule of a module where the scalars are restricted to be
nonnegative.  We choose this definition as it allows us to use the `Module` API to work with cones.

## Main statements

In `Mathlib/Analysis/Convex/Cone/Extension.lean` we prove
the M. Riesz extension theorem and a form of the Hahn-Banach theorem.

In `Mathlib/Analysis/Convex/Cone/Dual.lean` we prove
a variant of the hyperplane separation theorem.

## References

* https://en.wikipedia.org/wiki/Convex_cone
* [Stephen P. Boyd and Lieven Vandenberghe, *Convex Optimization*][boydVandenberghe2004]
* [Emo Welzl and Bernd Gärtner, *Cone Programming*][welzl_garter]
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

section PointedCone

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C C₁ C₂ : PointedCone R E} {x : E} {r : R}

@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

@[aesop 90% (rule_sets := [SetLike])]
nonrec lemma smul_mem (C : PointedCone R E) (hr : 0 ≤ r) (hx : x ∈ C) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx

lemma convex (C : PointedCone R E) : Convex R (C : Set E) :=
  convex_iff_add_mem.2 fun _ hx _ hy _ _ ha hb _ ↦ add_mem (C.smul_mem ha hx) (C.smul_mem hb hy)

end PointedCone

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

section LinearOrderedField

variable {𝕜 M : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section AddCommMonoid

variable [AddCommMonoid M] [Module 𝕜 M]

lemma smul_mem_iff (C : PointedCone 𝕜 M)
    {c : 𝕜} (hc : 0 < c) {x : M} : c • x ∈ C ↔ x ∈ C :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc).le h, C.smul_mem hc.le⟩

end AddCommMonoid

section AddCommGroup

open Pointwise

variable [AddCommGroup M] [Module 𝕜 M] {C : PointedCone 𝕜 M} {s : Set M} {x : M}

/-- The cone hull of a convex set is simply the union of the halflines through that set. -/
lemma mem_hull_of_convex {hs : Convex 𝕜 s} {hs₂ : s.Nonempty} :
    x ∈ hull 𝕜 s ↔ ∃ r : 𝕜, 0 ≤ r ∧ x ∈ r • s where
  mp hx := (Submodule.span_le (R := {c : 𝕜 // 0 ≤ c}) (p := {
              carrier := {y | ∃ r : 𝕜, 0 ≤ r ∧ y ∈ r • s}
              zero_mem' := ⟨0, by simp [hs₂]⟩
              add_mem' := by
                rintro y₁ y₂ ⟨r₁, hr₁, hy₁⟩ ⟨r₂, hr₂, hy₂⟩
                refine ⟨r₁ + r₂, add_nonneg hr₁ hr₂, ?_⟩
                rw [hs.add_smul hr₁ hr₂]
                exact Set.add_mem_add hy₁ hy₂
              smul_mem' := by
                intro ⟨r₁, hr₁⟩ y ⟨r₂, hr₂, hy⟩
                refine ⟨r₁ * r₂, mul_nonneg hr₁ hr₂, ?_⟩
                rw [mul_smul]
                exact Set.smul_mem_smul_set hy
            })).mpr (fun y hy ↦ ⟨1, by simpa⟩) hx
  mpr := by rintro ⟨r, hr, y, hy, rfl⟩; exact (hull 𝕜 s).smul_mem hr <| subset_hull hy

/-- The cone hull of a convex set is simply the union of the halflines through that set. -/
lemma coe_hull_of_convex (hs : Convex 𝕜 s) (hs₂ : s.Nonempty) :
    hull 𝕜 s = {x | ∃ r : 𝕜, 0 ≤ r ∧ x ∈ r • s} := by ext; simp [mem_hull_of_convex, *]

end AddCommGroup

end LinearOrderedField

section PositiveCone

variable (R E)
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]

/-- The positive cone is the pointed cone formed by the set of nonnegative elements in an ordered
module. -/
@[simps!]
def positive : PointedCone R E where
  __ := AddSubmonoid.nonneg E
  smul_mem' c _ hx := by simpa using smul_nonneg c.property hx

@[simp]
theorem mem_positive {x : E} : x ∈ positive R E ↔ 0 ≤ x :=
  Iff.rfl

lemma positive.isPointed {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    [Module R G] [PosSMulMono R G] : (positive R G).IsPointed :=
  AddSubmonoid.nonneg.isPointed G

end PositiveCone

section AddCommGroup

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

lemma sup_inf_assoc_of_le_submodule {C : PointedCone R E} (D : PointedCone R E)
    {S : Submodule R E} (hCS : C ≤ S) : (C ⊔ D) ⊓ S = C ⊔ (D ⊓ S) :=
  sup_inf_assoc_of_le_of_neg_le _ hCS (fun _ hx => by simpa using hCS hx)

lemma inf_sup_assoc_of_le_of_submodule_le {C : PointedCone R E} (D : PointedCone R E)
    {S : Submodule R E} (hSC : S ≤ C) : (C ⊓ D) ⊔ S = C ⊓ (D ⊔ S) :=
  inf_sup_assoc_of_le_of_neg_le _ hSC (fun _ hx => by apply hSC; simpa [hSC] using hx)

end AddCommGroup

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

@[deprecated (since := "2026-03-26")]
alias salient_iff_inter_neg_eq_singleton := isPointed_iff_support_eq_bot

end PointedCone
