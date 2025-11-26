/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.RingTheory.Congruence.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.RingQuot

/-!
# Congruence relations and ring homomorphisms

This file contains elementary definitions involving congruence
relations and morphisms for rings and semirings

## Main definitions

* `RingCon.ker`: the kernel of a monoid homomorphism as a congruence relation
* `RingCon.lift`, `RingCon.liftₐ`: the homomorphism / the algebra morphism
  on the quotient given that the congruence is in the kernel
* `RingCon.map`, `RingCon.mapₐ`: homomorphism / algebra morphism
  from a smaller to a larger quotient

* `RingCon.quotientKerEquivRangeS`, `RingCon.quotientKerEquivRange`,
  `RingCon.quotientKerEquivRangeₐ` :
  the first isomorphism theorem for semirings (using `RingHom.rangeS`),
  rings (using `RingHom.range`) and algebras (using `AlgHom.range`).
* `RingCon.comapQuotientEquivRangeS`, `RingCon.comapQuotientEquivRange`,
  `RingCon.comapQuotientEquivRangeₐ` : the second isomorphism theorem
  for semirings (using `RingHom.rangeS`), rings (using `RingHom.range`)
  and algebras (using `AlgHom.range`).

* `RingCon.quotientQuotientEquivQuotient`, `RingCon.quotientQuotientEquivQuotientₐ` :
  the third isomorphism theorem for semirings (or rings) and algebras

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, ring,
quotient ring
-/

@[expose] public section

variable {M : Type*} {N : Type*} {P : Type*}

open Function Setoid

namespace RingCon

section

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P] {c d : RingCon M}

/-- The kernel of a ring homomorphism as a ring congruence relation. -/
def ker (f : M →+* N) : RingCon M := comap ⊥ f

theorem comap_bot (f : M →+* N) : comap ⊥ f = ker f := rfl

/-- The definition of the ring congruence relation defined by a ring homomorphism's kernel. -/
@[simp]
theorem ker_apply (f : M →+* N) {x y} : ker f x y ↔ f x = f y :=
  Iff.rfl

/-- The kernel of the quotient map induced by a ring congruence relation `c` equals `c`. -/
theorem ker_mk'_eq (c : RingCon M) : ker c.mk' = c :=
  ext fun _ _ => Quotient.eq''

theorem ker_comp {f : M →+* N} {g : N →+* P} :
    ker (g.comp f) = (ker g).comap f :=
  ext fun x y ↦ by simp [ker_apply, comap_rel]

theorem comap_eq {g : N →+* M} :
    c.comap g = ker (c.mk'.comp g) := by
  rw [ker_comp, ker_mk'_eq]

/-- Makes an isomorphism of quotients by two ring congruence
relations, given that the relations are equal. -/
protected def congr (h : c = d) :
    c.Quotient ≃+* d.Quotient :=
  { Quotient.congr (Equiv.refl M) <| by apply RingCon.ext_iff.mp h with
    map_add' x y := by rcases x with ⟨⟩; rcases y with ⟨⟩; rfl
    map_mul' x y := by rcases x with ⟨⟩; rcases y with ⟨⟩; rfl }

@[simp] theorem congr_mk (h : c = d) (a : M) :
    RingCon.congr h (a : c.Quotient) = (a : d.Quotient) := rfl

/-- Given a function `f`, the smallest ring congruence relation containing the binary
relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to
the elements of `f⁻¹(y)` by a ring congruence relation `c`.' -/
def mapGen {c : RingCon M} (f : M → N) : RingCon N :=
  ringConGen <| Relation.Map c f f

/-- If `c` is a ring congruence on `M`, then the smallest ring
congruence relation on `N` deduced from `c` by a ring homomorphism
from `M` to `N` is the relation deduced from `c`. -/
theorem mapGen_eq_map_of_surjective
    {c : RingCon M} (f : M →+* N) (h : ker f ≤ c) (hf : Surjective f) :
    c.mapGen f = Relation.Map c f f := by
  refine le_antisymm ?_ <| (RingCon.gi N).gc.le_u_l _
  have := Relation.map_equivalence c.toSetoid.2 _ hf h
  intro _ _ hg
  induction hg with
  | of _ _ a => exact a
  | refl x => exact this.refl x
  | symm _ h => exact this.symm h
  | trans _ _ h₁ h₂ => exact this.trans h₁ h₂
  | add _ _ h₁ h₂ =>
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a + p, b + q, c.add h1 h2, map_add f _ _, map_add f _ _⟩
  | mul _ _ h₁ h₂ =>
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a * p, b * q, c.mul h1 h2, map_mul f _ _, map_mul f _ _⟩

theorem mapGen_apply_apply_of_surjective
    {c : RingCon M} (f : M →+* N) (h : ker f ≤ c) (hf : Surjective f) {x y : M} :
    c.mapGen f (f x) (f y) ↔ c x y := by
  rw [mapGen_eq_map_of_surjective f h hf, Relation.map_apply]
  refine ⟨fun ⟨a, b, h₁, h₂, h₃⟩ ↦ ?_, by grind⟩
  exact c.trans (h h₂.symm) <| c.trans h₁ <| h h₃

/-- Given a ring congruence relation `c` on a semiring `M`, the order-preserving
bijection between the set of ring congruence relations containing `c` and the
ring congruence relations on the quotient of `M` by `c`. -/
def correspondence {c : RingCon M} : Set.Ici c ≃o RingCon c.Quotient where
  toFun d := d.1.mapGen c.mk'
  invFun d := ⟨d.comap (mk' c), c.ker_mk'_eq.symm.trans_le <| comap_bot c.mk' ▸ comap_mono bot_le⟩
  left_inv d := by
    ext
    simp only [comap_rel]
    rw [mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le d.2) c.mk'_surjective]
  right_inv d := by
    ext x y
    simp only
    obtain ⟨x, rfl⟩ := c.mk'_surjective x
    obtain ⟨y, rfl⟩ := c.mk'_surjective y
    rw [mapGen_apply_apply_of_surjective _ (comap_bot c.mk' ▸ comap_mono bot_le) c.mk'_surjective,
      comap_rel]
  map_rel_iff' {s t} := by
    simp only [Equiv.coe_fn_mk, le_def, c.mk'_surjective.forall, ← Subtype.coe_le_coe]
    simp_rw [mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le s.2) c.mk'_surjective,
      mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le t.2) c.mk'_surjective]

variable (c : RingCon M)

variable (x y : M)

variable (f : M →+* P)

/-- The homomorphism on the quotient of a ring by a congruence relation `c`
induced by a homomorphism constant on the equivalence classes of `c`. -/
def lift (H : c ≤ ker f) : c.Quotient →+* P where
  __ := c.toAddCon.lift f.toAddMonoidHom H
  map_one' := f.map_one
  map_mul' x y := Con.induction_on₂ x y fun m n => f.map_mul m n

variable {c f}

/-- The diagram describing the universal property for quotients of ring commutes. -/
theorem lift_mk' (H : c ≤ ker f) (x) : c.lift f H (c.mk' x) = f x :=
  rfl

/-- The diagram describing the universal property for quotients of rings commutes. -/
@[simp] theorem lift_coe (H : c ≤ ker f) (x : M) : c.lift f H x = f x :=
  rfl

/-- The diagram describing the universal property for quotients of rings commutes. -/
@[simp] theorem lift_comp_mk' (H : c ≤ ker f) : (c.lift f H).comp c.mk' = f := rfl

/-- Given a homomorphism `f` from the quotient of a ring by a ring congruence
relation, `f` equals the homomorphism on the quotient induced by `f` composed
with the natural map from the ring to the quotient. -/
theorem lift_apply_mk' (f : c.Quotient →+* P) :
    (c.lift (f.comp c.mk') fun x y h => show f ↑x = f ↑y by rw [c.eq.2 h]) = f := by
  ext x; rcases x with ⟨⟩; rfl

/-- Homomorphisms on the quotient of a ring by a ring congruence relation are
equal if they are equal on elements that are coercions from the ring. -/
@[ext high] -- This should have higher priority than `RingHom.ext`
theorem Quotient.hom_ext {f g : c.Quotient →+* P} (h : f.comp c.mk' = g.comp c.mk') : f = g :=
  DFunLike.ext _ _ <| c.mk'_surjective.forall.mpr fun x ↦ by exact congr($h x)

/-- The uniqueness part of the universal property for quotients of rings. -/
theorem lift_unique (H : c ≤ ker f) (g : c.Quotient →+* P) (Hg : g.comp c.mk' = f) :
    g = c.lift f H :=
  Quotient.hom_ext (by aesop)

/-- Surjective ring homomorphisms constant on a the equivalence classes
of a ring congruence relation induce a surjective homomorphism on the quotient. -/
theorem lift_surjective_iff {h : c ≤ ker f} :
    Surjective (c.lift f h) ↔ Surjective f := by
  refine ⟨fun H ↦ (Quot.surjective_lift fun x x_1 h_1 ↦ h h_1).mp H,
    fun H ↦ AddCon.lift_surjective_of_surjective h H⟩

/-- Surjective ring homomorphisms constant on a the equivalence classes
of a ring congruence relation induce a surjective homomorphism on the quotient. -/
theorem lift_surjective_of_surjective (h : c ≤ ker f) (hf : Surjective f) :
    Surjective (c.lift f h) :=
  lift_surjective_iff.mpr hf

/-- Given a ring homomorphism `f` from `M` to `P` whose kernel contains `c`,
the lift of `M`to `N` is injective iff `ker f = c`. -/
theorem lift_injective_iff {h : c ≤ ker f} :
    Function.Injective (c.lift f h) ↔ c = ker f := by
  refine ⟨fun H ↦ ext'' (Setoid.ker_eq_lift_of_injective f h H).symm, ?_⟩
  rintro H ⟨x⟩ ⟨y⟩
  simp [H]

theorem lift_bijective_iff {h : c ≤ ker f} :
    Function.Bijective (c.lift f h) ↔ c = ker f ∧ Surjective f := by
  unfold Function.Bijective
  simp only [lift_injective_iff, lift_surjective_iff]

/-- Given a ring homomorphism `f` from `M` to `P`, the kernel of `f` is the
unique ring congruence relation on `M` whose induced map from the quotient of
`M` to `P` is injective. -/
theorem ker_eq_lift_of_injective (H : c ≤ ker f) (h : Injective (c.lift f H)) : ker f = c :=
  (lift_injective_iff.mp h).symm

variable (f)

/-- The homomorphism induced on the quotient of a ring by the kernel of a ring homomorphism. -/
def kerLift : (ker f).Quotient →+* P :=
  (ker f).lift f fun _ _ => id

variable {f}

/-- The diagram described by the universal property for quotients of rings, when
the ring congruence relation is the kernel of the homomorphism, commutes. -/
theorem kerLift_mk (x : M) : kerLift f x = f x :=
  rfl

/-- A ring homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
theorem kerLift_injective (f : M →+* P) : Injective (kerLift f) :=
  AddCon.kerLift_injective (f : M →+ P)

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
`d`'s quotient map induces a homomorphism from the quotient by `c` to the
quotient by `d`. -/
def map (c d : RingCon M) (h : c ≤ d) : c.Quotient →+* d.Quotient :=
  c.lift d.mk' fun x y hc => show ker d.mk' x y from (ker_mk'_eq d).symm ▸ h hc

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map. -/
theorem map_apply {c d : RingCon M} (h : c ≤ d) (x) :
    c.map d h x = c.lift d.mk' (fun _ _ hc => d.eq.2 <| h hc) x :=
  rfl

end

section

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P]

variable {c : RingCon M}

@[simp] theorem rangeS_mk' : RingHom.rangeS c.mk' = ⊤ :=
  RingHom.rangeS_eq_top.mpr (mk'_surjective _)

variable {f : M →+* P}

/-- Given a congruence relation `c` on a semiring and a homomorphism
`f` constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient. -/
@[simp] theorem rangeS_lift (H : c ≤ ker f) :
    RingHom.rangeS (c.lift f H) = f.rangeS :=
  SetLike.coe_injective <| Set.range_quot_lift _

/-- Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/
@[simp] theorem rangeS_kerLift :
    RingHom.rangeS (kerLift f) = RingHom.rangeS f :=
  rangeS_lift fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for semirings**. -/
noncomputable def quotientKerEquivRangeS (f : M →+* P) :
    (ker f).Quotient ≃+* f.rangeS where
  __ := RingHom.codRestrict (kerLift f) _ _
  __ := Setoid.quotientKerEquivRange _

@[simp] theorem coe_quotientKerEquivRangeS_mk (f : M →+* P) (x : M) :
    (quotientKerEquivRangeS f x) = f x := rfl

/-- The first isomorphism theorem for semirings in the case of a homomorphism with right inverse. -/
def quotientKerEquivOfRightInverse (f : M →+* P) (g : P → M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃+* P where
  __ := kerLift f
  __ := Setoid.quotientKerEquivOfRightInverse _ _ hf

@[simp] theorem quotientKerEquivOfRightInverse_apply
    (f : M →+* P) (g : P → M) (hf : Function.RightInverse g f) (x : (ker f).Quotient) :
    quotientKerEquivOfRightInverse f g hf x = kerLift f x :=
  rfl

/-- The first isomorphism theorem for rings in the case of a surjective homomorphism.

For a `computable` version, see `RingCon.quotientKerEquivOfRightInverse`.
-/
noncomputable def quotientKerEquivOfSurjective (f : M →+* P) (hf : Surjective f) :
    (ker f).Quotient ≃+* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

@[simp] theorem quotientKerEquivOfSurjective_mk (f : M →+* P) (hf : Surjective f) (x : M) :
    quotientKerEquivOfSurjective f hf x = f x := rfl

/-- A surjective ring homomorphisms`f : M →+* N` induces
a ring equivalence `d.Quotient ≃+* c.Quotient`,
whenever `c : RingCon M` and `d : RingCon N` are such that `d = c.comap f`. -/
noncomputable def comapQuotientEquivOfSurj
    (c : RingCon M) (f : N →+* M) (hf : Function.Surjective f)
    {d : RingCon N} (hcd : d = c.comap f) :
    d.Quotient ≃+* c.Quotient :=
  (RingCon.congr (hcd.trans c.comap_eq)).trans
    <| RingCon.quotientKerEquivOfSurjective (c.mk'.comp f)
    (c.mk'_surjective.comp hf)

@[simp] lemma comapQuotientEquivOfSurj_mk
    (c : RingCon M) {f : N →+* M} (hf : Function.Surjective f)
    {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    c.comapQuotientEquivOfSurj f hf hcd x = f x := rfl

@[simp] lemma comapQuotientEquivOfSurj_symm_mk
    (c : RingCon M) {f : N →+* M} (hf)
    {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    (c.comapQuotientEquivOfSurj f hf hcd).symm (f x) = x := by
  rw [← c.comapQuotientEquivOfSurj_mk hf hcd x, RingEquiv.symm_apply_apply]

/-- This version infers the surjectivity of the function from a RingEquiv function -/
@[simp] lemma comapQuotientEquivOfSurj_symm_mk' (c : RingCon M) (f : N ≃+* M)
    {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    (comapQuotientEquivOfSurj c (f : N →+* M) f.surjective hcd).symm ⟦f x⟧ = ↑x := by
  convert RingEquiv.symm_apply_apply _ _
  rw [comapQuotientEquivOfSurj_mk, RingEquiv.coe_toRingHom]
  rfl

/-- The **second isomorphism theorem for semirings**. -/
noncomputable def comapQuotientEquivRangeS (f : N →+* M)
    {d : RingCon N} (hcd : d = comap c f) :
    d.Quotient ≃+* RingHom.rangeS (c.mk'.comp f) :=
  (RingCon.congr (hcd.trans comap_eq)).trans <| quotientKerEquivRangeS <| c.mk'.comp f

@[simp] theorem comapQuotientEquivRangeS_mk (f : N →+* M)
    {d : RingCon N} (hcd : d = comap c f) (x : N) :
    c.comapQuotientEquivRangeS f hcd x = ⟨f x, (c.mk'.comp f).mem_rangeS_self x⟩ :=
  rfl

@[simp] theorem comapQuotientEquivRangeS_symm_mk (f : N →+* M)
    {d : RingCon N} (hcd : d = comap c f) (x : N) :
    (c.comapQuotientEquivRangeS f hcd).symm
      (⟨f x, RingHom.mem_rangeS_self (c.mk'.comp f) x ⟩) = x :=  by
  simp [RingEquiv.symm_apply_eq]

/-- The **third isomorphism theorem for (semi-)rings**. -/
def quotientQuotientEquivQuotient (c d : RingCon M) (h : c ≤ d) :
    (RingCon.ker (c.map d h)).Quotient ≃+* d.Quotient :=
  { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_add' x y :=
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a + d.mk' b by rw [← d.mk'.map_add]; rfl
    map_mul' x y :=
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }

@[simp] theorem quotientQuotientEquivQuotient_mk_mk (c d : RingCon M) (h : c ≤ d) (x : M) :
    c.quotientQuotientEquivQuotient d h ⟦⟦x⟧⟧ = ⟦x⟧ := rfl

@[simp] theorem quotientQuotientEquivQuotient_coe_coe (c d : RingCon M) (h : c ≤ d) (x : M) :
    c.quotientQuotientEquivQuotient d h ↑(x : c.Quotient) = x :=
  rfl

@[simp] theorem quotientQuotientEquivQuotient_symm_mk (c d : RingCon M) (h : c ≤ d) (x : M) :
    (c.quotientQuotientEquivQuotient d h).symm ⟦x⟧ = ⟦⟦x⟧⟧ :=
  rfl

end

section

variable [Ring M] [Ring N] [Ring P]

variable {c : RingCon M}

theorem range_mk' : RingHom.range c.mk' = ⊤ :=
  RingHom.range_eq_top.mpr (mk'_surjective _)

variable {f : M →+* P}

/-- Given a congruence relation `c` on a ring and a homomorphism `f`
constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient. -/
@[simp] theorem range_lift (H : c ≤ ker f) :
    RingHom.range (c.lift f H) = f.range :=
  SetLike.coe_injective <| Set.range_quot_lift _

/-- Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/
@[simp] theorem kerLift_range_eq :
    RingHom.range (kerLift f) = RingHom.range f :=
  range_lift fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for rings**. -/
noncomputable def quotientKerEquivRange (f : M →+* P) :
    (ker f).Quotient ≃+* f.range :=
  quotientKerEquivRangeS f

/-- The **second isomorphism theorem for rings**. -/
noncomputable def comapQuotientEquivRange (f : N →+* M) {d : RingCon N} (hcd : d = c.comap f) :
    d.Quotient ≃+* RingHom.range (c.mk'.comp f) :=
  c.comapQuotientEquivRangeS f hcd

theorem comapQuotientEquivRange_mk
    (f : N →+* M) {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    c.comapQuotientEquivRange f hcd x = ⟨f x, (c.mk'.comp f).mem_range_self x⟩ :=
  rfl

@[simp] theorem coe_comapQuotientEquivRange_mk
    (f : N →+* M) {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    (c.comapQuotientEquivRange f hcd x) = (f x : c.Quotient) :=
  rfl

@[simp] theorem comapQuotientEquivRange_symm_mk (f : N →+* M)
    {d : RingCon N} (hcd : d = comap c f) (x : N) :
    (c.comapQuotientEquivRange f hcd).symm
      (⟨f x, RingHom.mem_range_self (c.mk'.comp f) x ⟩) = x :=  by
  simp [RingEquiv.symm_apply_eq, ← Subtype.coe_inj]

end

section

variable {R : Type*} [CommSemiring R]
  [Semiring M] [Algebra R M] [Semiring N] [Algebra R N] [Semiring P] [Algebra R P]

variable {c d : RingCon M} {f : M →ₐ[R] P}

variable (R) in
/-- Makes an algebra isomorphism of quotients by two ring congruence
relations, given that the relations are equal. -/
protected def congrₐ {c d : RingCon M} (h : c = d) :
    c.Quotient ≃ₐ[R] d.Quotient :=
  { RingCon.congr h with
    commutes' _ := rfl }

theorem congrₐ_mk {c d : RingCon M} (h : c = d) (a : M) :
    RingCon.congrₐ R h (a : c.Quotient) = (a : d.Quotient) :=
  rfl

theorem range_mkₐ : AlgHom.range (mkₐ R c) = ⊤ :=
  (AlgHom.range_eq_top _).mpr (mkₐ_surjective _)

/-- The algebra homomorphism on the quotient of an algebra by a
congruence relation `c` induced by an algebra homomorphism
constant on the equivalence classes of `c`. -/
def liftₐ (c : RingCon M) (f : M →ₐ[R] P) (H : c ≤ ker f.toRingHom) :
    c.Quotient →ₐ[R] P :=
  { c.lift f H with
    commutes' r := AlgHomClass.commutes ↑f r }

theorem liftₐ_coe_toRingHom (c : RingCon M) (f : M →ₐ[R] P) (H : c ≤ ker f.toRingHom) :
    (c.liftₐ f H).toRingHom = c.lift f H :=
  rfl

theorem coe_liftₐ (c : RingCon M) (f : M →ₐ[R] P) (H : c ≤ ker f.toRingHom) :
    ⇑(c.liftₐ f H) = c.lift f H :=
  rfl

@[simp] theorem liftₐ_mk (c : RingCon M) (f : M →ₐ[R] P) (H : c ≤ ker f.toRingHom) (x : M) :
    c.liftₐ f H x = f x :=
  rfl

/-- Given a congruence relation `c` on an algebra and a homomorphism `f`
constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient. -/
theorem liftₐ_range (H : c ≤ ker f.toRingHom) :
    AlgHom.range (liftₐ c f H) = f.range :=
  Subalgebra.toSubsemiring_injective <| rangeS_lift H

variable (f) in
/-- The homomorphism induced on the quotient of a ring by the kernel of a ring homomorphism. -/
def kerLiftₐ : (ker f.toRingHom).Quotient →ₐ[R] P :=
  liftₐ (ker f.toRingHom) f (le_refl _)

/- Note : This can't be @[simp] because
  `(ker f.toRingHom).Quotient` is tranformed into `(ker ↑f).Quotient`.
  Maybe `kerLiftₐ` should use the latter. -/
/-- The diagram described by the universal property for quotients of rings, when
the ring congruence relation is the kernel of the homomorphism, commutes. -/
theorem kerLiftₐ_mk (x : M) : kerLiftₐ f x = f x := by
  rfl

/-- A ring homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
theorem kerLiftₐ_injective (f : M →ₐ[R] P) :
    Injective (kerLiftₐ f) := kerLift_injective f.toRingHom

variable (R) in
/-- Given ring congruence relations `c, d` on an algebra such that `d`
contains `c`, `d`'s quotient map induces an algebra homomorphism from
the quotient by `c` to the quotient by `d`. -/
def factorₐ {c d : RingCon M} (h : c ≤ d) :
    c.Quotient →ₐ[R] d.Quotient :=
  (liftₐ c (d.mkₐ R)) fun x y hc ↦ show (ker d.mk') x y from (ker_mk'_eq d).symm ▸ h hc

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map. -/
theorem factorₐ_apply {c d : RingCon M} (h : c ≤ d) (x) :
    factorₐ R h x = liftₐ c (d.mkₐ R) (fun _ _ hc ↦ d.eq.2 <| h hc) x :=
  rfl

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map. -/
@[simp] theorem factorₐ_mk {c d : RingCon M} (h : c ≤ d) (x : M) :
    factorₐ R h ⟦x⟧ = ⟦x⟧ :=
  rfl

@[simp] theorem mkₐ_comp_factorₐ_comp_mkₐ {c d : RingCon M} (h : c ≤ d) :
    (factorₐ R h).comp (c.mkₐ R) = d.mkₐ R :=
  rfl

/-- Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/
@[simp] theorem kerLiftₐ_range_eq :
    AlgHom.range (kerLiftₐ f) = AlgHom.range f :=
  liftₐ_range fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for algebra morphisms**. -/
noncomputable def quotientKerEquivRangeₐ (f : M →ₐ[R] P) :
    (ker (f : M →+* P)).Quotient ≃ₐ[R] f.range where
  __ := AlgHom.codRestrict (kerLiftₐ f) _ _
  __ := quotientKerEquivRangeS f.toRingHom

theorem quotientKerEquivRangeₐ_mkₐ (f : M →ₐ[R] P) (x : M) :
    quotientKerEquivRangeₐ f x = ⟨f x, AlgHom.mem_range_self f x⟩ :=
  rfl

@[simp]
theorem coe_quotientKerEquivRangeₐ_mkₐ (f : M →ₐ[R] P) (x : M) :
    (quotientKerEquivRangeₐ f x : P) = f x := by
  rfl

/-- The **second isomorphism theorem for algebras**. -/
noncomputable def comapQuotientEquivRangeₐ (f : N →ₐ[R] M) {d : RingCon N} (h : d = comap c f) :
    d.Quotient ≃ₐ[R] AlgHom.range ((c.mkₐ _).comp f) :=
  (RingCon.congrₐ R (h.trans comap_eq)).trans <| quotientKerEquivRangeₐ ((c.mkₐ _).comp f)

theorem comapQuotientEquivRangeₐ_mk (f : N →ₐ[R] M) {d : RingCon N} (h : d = comap c f) (x : N) :
    c.comapQuotientEquivRangeₐ f h x = ⟨f x, AlgHom.mem_range_self _ x⟩ :=
  rfl

@[simp] theorem coe_comapQuotientEquivRangeₐ_mk
    (f : N →ₐ[R] M) (x : N) {d : RingCon N} (h : d = comap c f) :
    (c.comapQuotientEquivRangeₐ f h x : c.Quotient) = f x :=
  rfl

@[simp] theorem coe_comapQuotientEquivRangeₐ_symm_mk
    (f : N →ₐ[R] M) (x : N) {d : RingCon N} (h : d = c.comap f) :
    (c.comapQuotientEquivRangeₐ f h).symm (⟨f x, AlgHom.mem_range_self _ x⟩) = x := by
  simp [AlgEquiv.symm_apply_eq, ← Subtype.coe_inj]

variable (R)

/-- The **third isomorphism theorem for algebras**. -/
def quotientQuotientEquivQuotientₐ {c d : RingCon M} (h : c ≤ d) :
    (RingCon.ker (factorₐ R h : c.Quotient →+* d.Quotient)).Quotient ≃ₐ[R] d.Quotient :=
  { quotientQuotientEquivQuotient c d h with
    commutes' _ := by rfl }

@[simp]
theorem quotientQuotientEquivQuotientₐ_mk_mk {c d : RingCon M} (h : c ≤ d) (x : M) :
    quotientQuotientEquivQuotientₐ R h ⟦⟦x⟧⟧ = ⟦x⟧ := rfl

@[simp]
theorem quotientQuotientEquivQuotientₐ_coe_coe {c d : RingCon M} (h : c ≤ d) (x : M) :
    quotientQuotientEquivQuotientₐ R h ↑(x : c.Quotient) = x :=
  quotientQuotientEquivQuotientₐ_mk_mk R h x

@[simp]
theorem quotientQuotientEquivQuotientₐ_symm_mk {c d : RingCon M} (h : c ≤ d) (x : M) :
    (quotientQuotientEquivQuotientₐ R h).symm ⟦x⟧ = ⟦⟦x⟧⟧ :=
  rfl

end

end RingCon
