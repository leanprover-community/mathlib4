/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.RingQuot

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


variable {M : Type*} {N : Type*} {P : Type*}

open Function Setoid

namespace RingCon

section

variable [Mul M] [Add M] [Mul N] [Add N] [Mul P] [Add P]
  {F} [FunLike F M N] [MulHomClass F M N] [AddHomClass F M N]

/-- The kernel of a ring homomorphism as a ring congruence relation. -/
def ker (f : F) : RingCon M where
  toSetoid := Setoid.ker f
  add' h1 h2 := by
    dsimp [Setoid.ker, onFun] at *
    rw [map_add, h1, h2, map_add]
  mul' h1 h2 := by
    dsimp [Setoid.ker, onFun] at *
    rw [map_mul, h1, h2, map_mul]

/-- The definition of the ring congruence relation defined by a ring homomorphism's kernel. -/
theorem ker_apply (f : F) {x y} : ker f x y ↔ f x = f y :=
  Iff.rfl

end

section

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P]
  {F} [FunLike F M N] [RingHomClass F M N]

/-- Makes an isomorphism of quotients by two ring congruence
relations, given that the relations are equal. -/
protected def congr {c d : RingCon M} (h : c = d) :
    c.Quotient ≃+* d.Quotient :=
  { Quotient.congr (Equiv.refl M) <| by apply RingCon.ext_iff.mp h with
    map_add' x y := by rcases x with ⟨⟩; rcases y with ⟨⟩; rfl
    map_mul' x y := by rcases x with ⟨⟩; rcases y with ⟨⟩; rfl }

theorem congr_mk {c d : RingCon M} (h : c = d) (a : M) :
    RingCon.congr h (a : c.Quotient) = (a : d.Quotient) := rfl

theorem comap_eq {c : RingCon M} {f : N →+* M} :
    c.comap f = ker (c.mk'.comp f) :=
  ext fun x y => show c _ _ ↔ c.mk' _ = c.mk' _ by rw [← c.eq]; rfl

theorem comap_rel {c : RingCon M} {f : N →+* M} {x y : N} :
    c.comap f x y ↔ c (f x) (f y) := Iff.rfl

/-- The kernel of the quotient map induced by a ring congruence relation `c` equals `c`. -/
theorem ker_mk'_eq (c : RingCon M) : ker c.mk' = c :=
  ext fun _ _ => Quotient.eq''

/-- Given a function `f`, the smallest ring congruence relation containing the binary
relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to
the elements of `f⁻¹(y)` by a ring congruence relation `c`.' -/
def mapGen {c : RingCon M} (f : M → N) : RingCon N :=
  ringConGen <| Relation.Map c f f

/-- Given a surjective ring homomorphism `f` whose kernel is contained in a ring
congruence relation `c`, the ring congruence relation on `f`'s codomain defined by
'`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/
def mapOfSurjective {c : RingCon M} (f : F) (h : ker f ≤ c) (hf : Surjective f) : RingCon N where
  __ := c.toSetoid.mapOfSurjective f h hf
  add' h₁ h₂ := by
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a + p, b + q, c.add h1 h2, map_add f _ _, map_add f _ _⟩
  mul' h₁ h₂ := by
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a * p, b * q, c.mul h1 h2, map_mul f _ _, map_mul f _ _⟩

/-- A specialization of 'the smallest ring congruence relation containing a ring
congruence relation `c` equals `c`'. -/
theorem mapOfSurjective_eq_mapGen {c : RingCon M} {f : F} (h : ker f ≤ c) (hf : Surjective f) :
    c.mapGen f = c.mapOfSurjective f h hf := by
  rw [← ringConGen_of_ringCon (c.mapOfSurjective f h hf)]; rfl

/-- Given a ring congruence relation `c` on a semiring `M`, the order-preserving
bijection between the set of ring congruence relations containing `c` and the
ring congruence relations on the quotient of `M` by `c`. -/
def correspondence {c : RingCon M} : { d // c ≤ d } ≃o RingCon c.Quotient where
  toFun d :=
    d.1.mapOfSurjective (mk' c) (by rw [RingCon.ker_mk'_eq]; exact d.2) <|
      Quotient.mk_surjective
  invFun d := ⟨RingCon.comap d (mk' c), fun x y h ↦
    show d x y by rw [c.eq.mpr h]; exact d.refl _⟩
  left_inv d :=
    Subtype.ext_iff_val.2 <|
      ext fun x y =>
        ⟨fun ⟨a, b, H, hx, hy⟩ =>
          d.1.trans (d.1.symm <| d.2 <| c.eq.1 hx) <| d.1.trans H <| d.2 <| c.eq.1 hy,
          fun h => ⟨_, _, h, rfl, rfl⟩⟩
  right_inv d :=
    ext fun x y =>
      ⟨fun ⟨_, _, H, hx, hy⟩ =>
        hx ▸ hy ▸ H,
        Con.induction_on₂ x y fun w z h => ⟨w, z, h, rfl, rfl⟩⟩
  map_rel_iff' {s t} := by
    constructor
    · intros h x y hs
      rcases h ⟨x, y, hs, rfl, rfl⟩ with ⟨a, b, ht, hx, hy⟩
      exact t.1.trans (t.1.symm <| t.2 <| c.eq.1 hx) (t.1.trans ht (t.2 <| c.eq.1 hy))
    · exact Relation.map_mono

variable (c : RingCon M)

variable (x y : M)

/-- The kernel of the natural homomorphism from a ring to its quotient by a ring
congruence relation `c` equals `c`. -/
theorem mk'_ker : ker c.mk' = c :=
  ext fun _ _ => c.eq

variable (f : M →+* P)

/-- The homomorphism on the quotient of a monoid by a congruence relation `c`
induced by a homomorphism constant on the equivalence classes of `c`. -/
def lift (H : c ≤ ker f) : c.Quotient →+* P where
  toFun x := (Con.liftOn x f) fun _ _ h => H h
  map_zero' := by rw [← f.map_zero]; rfl
  map_one' := by rw [← f.map_one]; rfl
  map_add' x y := Con.induction_on₂ x y fun m n => by
    simp only [Con.liftOn_coe, ← map_add]
    exact Con.liftOn_coe ..
  map_mul' x y := Con.induction_on₂ x y fun m n => by
    simp only [Con.liftOn_coe, ← map_mul]
    exact Con.liftOn_coe ..

variable {c f}

/-- The diagram describing the universal property for quotients of ring commutes. -/
theorem lift_mk' (H : c ≤ ker f) (x) : c.lift f H (c.mk' x) = f x :=
  rfl

/-- The diagram describing the universal property for quotients of rings commutes. -/
theorem lift_coe (H : c ≤ ker f) (x : M) : c.lift f H x = f x :=
  rfl

/-- The diagram describing the universal property for quotients of rings commutes. -/
theorem lift_comp_mk' (H : c ≤ ker f) : (c.lift f H).comp c.mk' = f := by ext; rfl

/-- Given a homomorphism `f` from the quotient of a ring by a ring congruence
relation, `f` equals the homomorphism on the quotient induced by `f` composed
with the natural map from the ring to the quotient. -/
theorem lift_apply_mk' (f : c.Quotient →+* P) :
    (c.lift (f.comp c.mk') fun x y h => show f ↑x = f ↑y by rw [c.eq.2 h]) = f := by
  ext x; rcases x with ⟨⟩; rfl

/-- Homomorphisms on the quotient of a ring by a ring congruence relation are
equal if they are equal on elements that are coercions from the ring. -/
theorem lift_funext (f g : c.Quotient →+* P) (h : ∀ a : M, f a = g a) : f = g := by
  rw [← lift_apply_mk' f, ← lift_apply_mk' g]
  congr 1
  exact DFunLike.ext_iff.2 h

/-- The uniqueness part of the universal property for quotients of rings. -/
theorem lift_unique (H : c ≤ ker f) (g : c.Quotient →+* P) (Hg : g.comp c.mk' = f) :
    g = c.lift f H :=
  (lift_funext g (c.lift f H)) fun x => by
    subst f
    rfl

/-- Surjective ring homomorphisms constant on a the equivalence classes
of a ring congruence relation induce a surjective homomorphism on the quotient. -/
theorem lift_surjective_of_surjective (h : c ≤ ker f) (hf : Surjective f) :
    Surjective (c.lift f h) := fun y =>
  (Exists.elim (hf y)) fun w hw => ⟨w, (lift_mk' h w).symm ▸ hw⟩

variable (c f)

/-- Given a ring homomorphism `f` from `M` to `P`, the kernel of `f` is the
unique ring congruence relation on `M` whose induced map from the quotient of
`M` to `P` is injective. -/
theorem ker_eq_lift_of_injective (H : c ≤ ker f) (h : Injective (c.lift f H)) : ker f = c :=
  RingCon.toSetoid_inj <| Setoid.ker_eq_lift_of_injective f H h

variable {c}

/-- The homomorphism induced on the quotient of a ring by the kernel of a ring homomorphism. -/
def kerLift : (ker f).Quotient →+* P :=
  ((ker f).lift f) fun _ _ => id

variable {f}

/-- The diagram described by the universal property for quotients of rings, when
the ring congruence relation is the kernel of the homomorphism, commutes. -/
theorem kerLift_mk (x : M) : kerLift f x = f x :=
  rfl

/-- A ring homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
theorem kerLift_injective (f : M →+* P) : Injective (kerLift f) := fun x y =>
  Quotient.inductionOn₂' x y fun _ _ => (ker f).eq.2

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
`d`'s quotient map induces a homomorphism from the quotient by `c` to the
quotient by `d`. -/
def map (c d : RingCon M) (h : c ≤ d) : c.Quotient →+* d.Quotient :=
  (c.lift d.mk') fun x y hc => show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc

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

theorem rangeS_mk' : RingHom.rangeS c.mk' = ⊤ :=
  RingHom.rangeS_eq_top.mpr (mk'_surjective _)

variable {f : M →+* P}

/-- Given a congruence relation `c` on a semiring and a homomorphism
`f` constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient. -/
theorem lift_rangeS (H : c ≤ ker f) :
    RingHom.rangeS (c.lift f H) = f.rangeS :=
  Subsemiring.ext_iff.mpr (fun x ↦
    ⟨by rintro ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, by rintro ⟨y, hy⟩; exact ⟨↑y, hy⟩⟩)

/-- Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/
theorem kerLift_rangeS_eq : RingHom.rangeS (kerLift f) = RingHom.rangeS f :=
  lift_rangeS fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for semirings**. -/
noncomputable def quotientKerEquivRangeS (f : M →+* P) :
    (ker f).Quotient ≃+* f.rangeS := by
  apply RingEquiv.ofBijective
    (RingHom.codRestrict (kerLift f) _ (fun x ↦ by rw [← kerLift_rangeS_eq]; simp))
  constructor
  · exact RingHom.injective_codRestrict.mpr (kerLift_injective f)
  · refine RingHom.surjective_codRestrict.mpr ?_
    rw [kerLift_rangeS_eq]
    rfl

/-- The first isomorphism theorem for semirings in the case of a homomorphism with right inverse. -/
def quotientKerEquivOfRightInverse (f : M →+* P) (g : P → M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃+* P :=
  { kerLift f with
    toFun := kerLift f
    invFun := (↑) ∘ g
    left_inv := fun x => kerLift_injective _ (by rw [Function.comp_apply, kerLift_mk, hf])
    right_inv := fun x => by (conv_rhs => rw [← hf x]); rfl }

/-- The first isomorphism theorem for rings in the case of a surjective homomorphism.

For a `computable` version, see `RingCon.quotientKerEquivOfRightInverse`.
-/
noncomputable def quotientKerEquivOfSurjective (f : M →+* P) (hf : Surjective f) :
    (ker f).Quotient ≃+* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

/-- If `e : M →+* N` is surjective then
`(c.comap e).Quotient ≃+* c.Quotient` with `c : RingCon N` -/
noncomputable def comapQuotientEquivOfSurj
    (c : RingCon M) (f : N →+* M) (hf : Function.Surjective f) :
    (c.comap f).Quotient ≃+* c.Quotient :=
  (RingCon.congr (c.comap_eq)).trans
    <| RingCon.quotientKerEquivOfSurjective (c.mk'.comp f)
    (c.mk'_surjective.comp hf)

lemma comapQuotientEquivOfSurj_mk
    (c : RingCon M) {f : N →+* M} (hf : Function.Surjective f) (x : N) :
    comapQuotientEquivOfSurj c f hf x = f x := rfl

lemma comapQuotientEquivOfSurj_symm_mk (c : RingCon M) {f : N →+* M} (hf) (x : N) :
    (comapQuotientEquivOfSurj c f hf).symm (f x) = x := by
  suffices f x = (comapQuotientEquivOfSurj c f hf) x by
    simp [this]
  rw [comapQuotientEquivOfSurj_mk]

/-- This version infers the surjectivity of the function from a RingEquiv function -/
lemma comapQuotientEquivOfSurj_symm_mk' (c : RingCon M) (f : N ≃+* M) (x : N) :
    ((RingEquiv.symm
      (R := RingCon.Quotient (comap c f : RingCon N))
      (comapQuotientEquivOfSurj c (f : N →+* M) f.surjective))
      ⟦f x⟧) = ↑x := by
  suffices ⟦f x⟧ = (comapQuotientEquivOfSurj c (f : N →+* M) f.surjective) x by
    rw [this]
    apply RingEquiv.symm_apply_apply
  exact quot_mk_eq_coe c (f x)

/-- The **second isomorphism theorem for semirings**. -/
noncomputable def comapQuotientEquivRangeS (f : N →+* M) :
    (comap c f).Quotient ≃+* RingHom.rangeS (c.mk'.comp f) :=
  (RingCon.congr comap_eq).trans <| quotientKerEquivRangeS <| c.mk'.comp f

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
theorem lift_range (H : c ≤ ker f) :
    RingHom.range (c.lift f H) = f.range :=
  Subring.ext_iff.mpr (fun x ↦
    ⟨by rintro ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, by rintro ⟨y, hy⟩; exact ⟨↑y, hy⟩⟩)

/-- Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/
theorem kerLift_range_eq : RingHom.range (kerLift f) = RingHom.range f :=
  lift_range fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for rings**. -/
noncomputable def quotientKerEquivRange (f : M →+* P) :
    (ker f).Quotient ≃+* f.range :=
  quotientKerEquivRangeS f

/-- The **second isomorphism theorem for semirings**. -/
noncomputable def comapQuotientEquivRange (f : N →+* M) :
    (comap c f).Quotient ≃+* RingHom.range (c.mk'.comp f) :=
  c.comapQuotientEquivRangeS f

end

section

variable {R : Type*} [CommSemiring R]
  [Semiring M] [Algebra R M] [Semiring N] [Algebra R N] [Semiring P] [Algebra R P]

variable {c d : RingCon M} {f : M →ₐ[R] P}

variable (R) in
/-- Makes an algebra isomorphism of quotients by two ring congruence
relations, given that the relations are equal. -/
protected def congrₐ {c d : RingCon M} (h : c = d) :
    c.Quotient ≃ₐ[R] d.Quotient := {
  RingCon.congr h with
  commutes' _ := rfl }

theorem congrₐ_mk {c d : RingCon M} (h : c = d) (a : M) :
    RingCon.congrₐ R h (a : c.Quotient) = (a : d.Quotient) :=
  rfl

theorem range_mk'ₐ :
    AlgHom.range (mk'ₐ R c) = ⊤ :=
  (AlgHom.range_eq_top _).mpr (mk'ₐ_surjective _)

/-- The algebra homomorphism on the quotient of an algebra by a
congruence relation `c` induced by an algebra homomorphism
constant on the equivalence classes of `c`. -/
def liftₐ (c : RingCon M) (f : M →ₐ[R] P) (H : c ≤ ker f) :
    c.Quotient →ₐ[R] P := {
  c.lift f H with
  commutes' r := AlgHomClass.commutes (↑f) r }

/-- Given a congruence relation `c` on a ring and a homomorphism `f`
constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient. -/
theorem liftₐ_range (H : c ≤ ker f) :
    AlgHom.range (liftₐ c f H) = f.range := by
  ext p
  exact Subsemiring.ext_iff.mp (lift_rangeS H) p

variable (f) in
/-- The homomorphism induced on the quotient of a ring by the kernel of a ring homomorphism. -/
def kerLiftₐ : (ker f).Quotient →ₐ[R] P :=
  liftₐ (ker f) f (le_refl _)

/-- The diagram described by the universal property for quotients of rings, when
the ring congruence relation is the kernel of the homomorphism, commutes. -/
theorem kerLiftₐ_mk (x : M) : kerLiftₐ f x = f x :=
  rfl

/-- A ring homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
theorem kerLiftₐ_injective (f : M →ₐ[R] P) :
    Injective (kerLiftₐ f) := kerLift_injective f.toRingHom

variable (R) in
/-- Given ring congruence relations `c, d` on an algebra such that `d`
contains `c`, `d`'s quotient map induces an algebra homomorphism from
the quotient by `c` to the quotient by `d`. -/
def mapₐ (c d : RingCon M) (h : c ≤ d) :
    c.Quotient →ₐ[R] d.Quotient :=
  (liftₐ c (d.mk'ₐ R)) fun x y hc ↦ show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map. -/
theorem mapₐ_apply {c d : RingCon M} (h : c ≤ d) (x) :
    mapₐ (R := R) c d h x =
      liftₐ (R := R) c (d.mk'ₐ R) (fun _ _ hc ↦ d.eq.2 <| h hc) x :=
  rfl

/-- Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/
theorem kerLiftₐ_range_eq :
    AlgHom.range (kerLiftₐ f) = AlgHom.range f :=
  liftₐ_range fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for algebra morphisms**. -/
noncomputable def quotientKerEquivRangeₐ (f : M →ₐ[R] P) :
    (ker f).Quotient ≃ₐ[R] f.range := by
  apply AlgEquiv.ofBijective
    (AlgHom.codRestrict (kerLiftₐ f) _ (fun x ↦ by rw [← kerLiftₐ_range_eq]; simp))
  exact (quotientKerEquivRangeS f.toRingHom).bijective

/-- The **second isomorphism theorem for algebras**. -/
noncomputable def comapQuotientEquivRangeₐ (f : N →ₐ[R] M) :
    (comap c f).Quotient ≃ₐ[R] AlgHom.range ((c.mk'ₐ _).comp f) := by
  apply (RingCon.congrₐ R comap_eq).trans
    <| quotientKerEquivRangeₐ ((c.mk'ₐ _).comp f)

/-- The **third isomorphism theorem for algebras**. -/
def quotientQuotientEquivQuotientₐ (c d : RingCon M) (h : c ≤ d) :
    (RingCon.ker (mapₐ R c d h)).Quotient ≃ₐ[R] d.Quotient :=
  { quotientQuotientEquivQuotient c d h with
    commutes' _ := by rfl }

end

end RingCon
