/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.Congruence.Hom

/-!
# Congruence relations

This file proves basic properties of the quotient of a type by a congruence relation.

The second half of the file concerns congruence relations on monoids, in which case the
quotient by the congruence relation is also a monoid. There are results about the universal
property of quotients of monoids, and the isomorphism theorems for monoids.

## Implementation notes

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid, isomorphism theorems
-/


variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

variable {M}

namespace Con

section

variable [Mul M] [Mul N] [Mul P] (c : Con M)

variable {c}

/-- Given types with multiplications `M, N`, the product of two congruence relations `c` on `M` and
`d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁` is related to `y₁`
by `c` and `x₂` is related to `y₂` by `d`. -/
@[to_additive prod /-- Given types with additions `M, N`, the product of two congruence relations
`c` on `M` and `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁`
is related to `y₁` by `c` and `x₂` is related to `y₂` by `d`. -/]
protected def prod (c : Con M) (d : Con N) : Con (M × N) :=
  { c.toSetoid.prod d.toSetoid with
    mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }

/-- The product of an indexed collection of congruence relations. -/
@[to_additive /-- The product of an indexed collection of additive congruence relations. -/]
def pi {ι : Type*} {f : ι → Type*} [∀ i, Mul (f i)] (C : ∀ i, Con (f i)) : Con (∀ i, f i) :=
  { @piSetoid _ _ fun i => (C i).toSetoid with
    mul' := fun h1 h2 i => (C i).mul (h1 i) (h2 i) }

/-- Makes an isomorphism of quotients by two congruence relations, given that the relations are
equal. -/
@[to_additive /-- Makes an additive isomorphism of quotients by two additive congruence relations,
given that the relations are equal. -/]
protected def congr {c d : Con M} (h : c = d) : c.Quotient ≃* d.Quotient :=
  { Quotient.congr (Equiv.refl M) <| by apply Con.ext_iff.mp h with
    map_mul' := fun x y => by rcases x with ⟨⟩; rcases y with ⟨⟩; rfl }

@[to_additive (attr := simp)]
theorem congr_mk {c d : Con M} (h : c = d) (a : M) :
    Con.congr h (a : c.Quotient) = (a : d.Quotient) := rfl

@[to_additive]
theorem le_comap_conGen {M N : Type*} [Mul M] [Mul N] (f : M → N)
    (H : ∀ (x y : M), f (x * y) = f x * f y) (rel : N → N → Prop) :
    conGen (fun x y ↦ rel (f x) (f y)) ≤ Con.comap f H (conGen rel) := by
  intro x y h
  simp only [Con.comap_rel]
  exact .rec (fun x y h ↦ .of (f x) (f y) h) (fun x ↦ .refl (f x))
    (fun _ h ↦ .symm h) (fun _ _ h1 h2 ↦ h1.trans h2) (fun {w x y z} _ _ h1 h2 ↦
    (congrArg (fun a ↦ conGen rel a (f (x * z))) (H w y)).mpr
    (((congrArg (fun a ↦ conGen rel (f w * f y) a) (H x z))).mpr
    (.mul h1 h2))) h

@[to_additive]
theorem comap_conGen_equiv {M N : Type*} [Mul M] [Mul N] (f : MulEquiv M N) (rel : N → N → Prop) :
    Con.comap f (map_mul f) (conGen rel) = conGen (fun x y ↦ rel (f x) (f y)) := by
  apply le_antisymm _ (le_comap_conGen f (map_mul f) rel)
  intro a b h
  simp only [Con.comap_rel] at h
  have H : ∀ n1 n2, (conGen rel) n1 n2 → ∀ a b, f a = n1 → f b = n2 →
      (conGen fun x y ↦ rel (f x) (f y)) a b := by
    intro n1 n2 h
    induction h with
    | of x y h =>
      intro _ _ fa fb
      apply ConGen.Rel.of
      rwa [fa, fb]
    | refl x =>
      intro _ _ fc fd
      rw [f.injective (fc.trans fd.symm)]
      exact ConGen.Rel.refl _
    | symm _ h => exact fun a b fs fb ↦ ConGen.Rel.symm (h b a fb fs)
    | trans _ _ ih ih1 =>
      exact fun a b fa fb ↦ Exists.casesOn (f.surjective _) fun c' hc' ↦
      ConGen.Rel.trans (ih a c' fa hc') (ih1 c' b hc' fb)
    | mul _ _ ih ih1 =>
      rename_i w x y z _ _
      intro a b fa fb
      rw [← f.eq_symm_apply, map_mul] at fa fb
      rw [fa, fb]
      exact ConGen.Rel.mul (ih (f.symm w) (f.symm x) (by simp) (by simp))
        (ih1 (f.symm y) (f.symm z) (by simp) (by simp))
  exact H (f a) (f b) h a b (refl _) (refl _)

@[to_additive]
theorem comap_conGen_of_bijective {M N : Type*} [Mul M] [Mul N] (f : M → N)
    (hf : Function.Bijective f) (H : ∀ (x y : M), f (x * y) = f x * f y) (rel : N → N → Prop) :
    Con.comap f H (conGen rel) = conGen (fun x y ↦ rel (f x) (f y)) :=
  comap_conGen_equiv (MulEquiv.ofBijective (MulHom.mk f H) hf) rel

end

section MulOneClass

variable [MulOneClass M] [MulOneClass N] [MulOneClass P] (c : Con M)

/-- The submonoid of `M × M` defined by a congruence relation on a monoid `M`. -/
@[to_additive (attr := coe) /-- The `AddSubmonoid` of `M × M` defined by an additive congruence
relation on an `AddMonoid` `M`. -/]
protected def submonoid : Submonoid (M × M) where
  carrier := { x | c x.1 x.2 }
  one_mem' := c.iseqv.1 1
  mul_mem' := c.mul

variable {c}

/-- The congruence relation on a monoid `M` from a submonoid of `M × M` for which membership
is an equivalence relation. -/
@[to_additive /-- The additive congruence relation on an `AddMonoid` `M` from
an `AddSubmonoid` of `M × M` for which membership is an equivalence relation. -/]
def ofSubmonoid (N : Submonoid (M × M)) (H : Equivalence fun x y => (x, y) ∈ N) : Con M where
  r x y := (x, y) ∈ N
  iseqv := H
  mul' := N.mul_mem

/-- Coercion from a congruence relation `c` on a monoid `M` to the submonoid of `M × M` whose
elements are `(x, y)` such that `x` is related to `y` by `c`. -/
@[to_additive /-- Coercion from a congruence relation `c` on an `AddMonoid` `M`
to the `AddSubmonoid` of `M × M` whose elements are `(x, y)` such that `x`
is related to `y` by `c`. -/]
instance toSubmonoid : Coe (Con M) (Submonoid (M × M)) :=
  ⟨fun c => c.submonoid⟩

@[to_additive]
theorem mem_coe {c : Con M} {x y} : (x, y) ∈ (↑c : Submonoid (M × M)) ↔ (x, y) ∈ c :=
  Iff.rfl

@[to_additive]
theorem to_submonoid_inj (c d : Con M) (H : (c : Submonoid (M × M)) = d) : c = d :=
  ext fun x y => show (x, y) ∈ c.submonoid ↔ (x, y) ∈ d from H ▸ Iff.rfl

@[to_additive]
theorem le_iff {c d : Con M} : c ≤ d ↔ (c : Submonoid (M × M)) ≤ d :=
  ⟨fun h _ H => h H, fun h x y hc => h <| show (x, y) ∈ c from hc⟩

variable (x y : M)

@[to_additive (attr := simp)]
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): removed dot notation
theorem mrange_mk' : MonoidHom.mrange c.mk' = ⊤ :=
  MonoidHom.mrange_eq_top.2 mk'_surjective

variable {f : M →* P}

/-- Given a congruence relation `c` on a monoid and a homomorphism `f` constant on `c`'s
equivalence classes, `f` has the same image as the homomorphism that `f` induces on the
quotient. -/
@[to_additive /-- Given an additive congruence relation `c` on an `AddMonoid` and a homomorphism `f`
constant on `c`'s equivalence classes, `f` has the same image as the homomorphism that `f` induces
on the quotient. -/]
theorem lift_range (H : c ≤ ker f) : MonoidHom.mrange (c.lift f H) = MonoidHom.mrange f :=
  Submonoid.ext fun x => ⟨by rintro ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨↑y, hy⟩⟩

/-- Given a monoid homomorphism `f`, the induced homomorphism on the quotient by `f`'s kernel has
the same image as `f`. -/
@[to_additive (attr := simp) /-- Given an `AddMonoid` homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/]
theorem kerLift_range_eq : MonoidHom.mrange (kerLift f) = MonoidHom.mrange f :=
  lift_range fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for monoids**. -/
@[to_additive /-- The first isomorphism theorem for `AddMonoid`s. -/]
noncomputable def quotientKerEquivRange (f : M →* P) : (ker f).Quotient ≃* MonoidHom.mrange f :=
  { Equiv.ofBijective
        ((@MulEquiv.toMonoidHom (MonoidHom.mrange (kerLift f)) _ _ _ <|
              MulEquiv.submonoidCongr kerLift_range_eq).comp
          (kerLift f).mrangeRestrict) <|
      ((Equiv.bijective (@MulEquiv.toEquiv (MonoidHom.mrange (kerLift f)) _ _ _ <|
          MulEquiv.submonoidCongr kerLift_range_eq)).comp
        ⟨fun x y h =>
          kerLift_injective f <| by rcases x with ⟨⟩; rcases y with ⟨⟩; injections,
          fun ⟨w, z, hz⟩ => ⟨z, by rcases hz with ⟨⟩; rfl⟩⟩) with
    map_mul' := MonoidHom.map_mul _ }

/-- The first isomorphism theorem for monoids in the case of a homomorphism with right inverse. -/
@[to_additive (attr := simps)
  /-- The first isomorphism theorem for `AddMonoid`s in the case of a homomorphism
  with right inverse. -/]
def quotientKerEquivOfRightInverse (f : M →* P) (g : P → M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃* P :=
  { kerLift f with
    toFun := kerLift f
    invFun := (↑) ∘ g
    left_inv := fun x => kerLift_injective _ (by rw [Function.comp_apply, kerLift_mk, hf])
    right_inv := fun x => by (conv_rhs => rw [← hf x]); rfl }

/-- The first isomorphism theorem for Monoids in the case of a surjective homomorphism.

For a `computable` version, see `Con.quotientKerEquivOfRightInverse`.
-/
@[to_additive /-- The first isomorphism theorem for `AddMonoid`s in the case of a surjective
homomorphism.

For a `computable` version, see `AddCon.quotientKerEquivOfRightInverse`. -/]
noncomputable def quotientKerEquivOfSurjective (f : M →* P) (hf : Surjective f) :
    (ker f).Quotient ≃* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

/-- If e : M →* N is surjective then (c.comap e).Quotient ≃* c.Quotient with c : Con N -/
@[to_additive /-- If e : M →* N is surjective then (c.comap e).Quotient ≃* c.Quotient with c :
AddCon N -/]
noncomputable def comapQuotientEquivOfSurj (c : Con M) (f : N →* M) (hf : Function.Surjective f) :
    (Con.comap f f.map_mul c).Quotient ≃* c.Quotient :=
  (Con.congr Con.comap_eq).trans <| Con.quotientKerEquivOfSurjective (c.mk'.comp f) <|
    Con.mk'_surjective.comp hf

@[to_additive (attr := simp)]
lemma comapQuotientEquivOfSurj_mk (c : Con M) {f : N →* M} (hf : Function.Surjective f) (x : N) :
    comapQuotientEquivOfSurj c f hf x = f x := rfl

@[to_additive (attr := simp)]
lemma comapQuotientEquivOfSurj_symm_mk (c : Con M) {f : N →* M} (hf) (x : N) :
    (comapQuotientEquivOfSurj c f hf).symm (f x) = x :=
  (MulEquiv.symm_apply_eq (c.comapQuotientEquivOfSurj f hf)).mpr rfl

/-- This version infers the surjectivity of the function from a MulEquiv function -/
@[to_additive (attr := simp) /-- This version infers the surjectivity of the function from a
MulEquiv function -/]
lemma comapQuotientEquivOfSurj_symm_mk' (c : Con M) (f : N ≃* M) (x : N) :
    ((@MulEquiv.symm (Con.Quotient (comap ⇑f _ c)) _ _ _
      (comapQuotientEquivOfSurj c (f : N →* M) f.surjective)) ⟦f x⟧) = ↑x :=
  (MulEquiv.symm_apply_eq (@comapQuotientEquivOfSurj M N _ _ c f _)).mpr rfl

/-- The **second isomorphism theorem for monoids**. -/
@[to_additive /-- The second isomorphism theorem for `AddMonoid`s. -/]
noncomputable def comapQuotientEquiv (f : N →* M) :
    (comap f f.map_mul c).Quotient ≃* MonoidHom.mrange (c.mk'.comp f) :=
  (Con.congr comap_eq).trans <| quotientKerEquivRange <| c.mk'.comp f

/-- The **third isomorphism theorem for monoids**. -/
@[to_additive /-- The third isomorphism theorem for `AddMonoid`s. -/]
def quotientQuotientEquivQuotient (c d : Con M) (h : c ≤ d) :
    (ker (c.map d h)).Quotient ≃* d.Quotient :=
  { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_mul' := fun x y =>
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }

end MulOneClass

section Monoids

@[to_additive]
theorem smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) (a : α)
    {w x : M} (h : c w x) : c (a • w) (a • x) := by
  simpa only [smul_one_mul] using c.mul (c.refl' (a • (1 : M) : M)) h

end Monoids

section Actions

@[to_additive]
instance instSMul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) :
    SMul α c.Quotient where
  smul a := (Quotient.map' (a • ·)) fun _ _ => c.smul a

@[to_additive]
theorem coe_smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M)
    (a : α) (x : M) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient) :=
  rfl

instance instSMulCommClass {α β M : Type*} [MulOneClass M] [SMul α M] [SMul β M]
    [IsScalarTower α M M] [IsScalarTower β M M] [SMulCommClass α β M] (c : Con M) :
    SMulCommClass α β c.Quotient where
  smul_comm a b := Quotient.ind' fun m => congr_arg Quotient.mk'' <| smul_comm a b m

instance instIsScalarTower {α β M : Type*} [MulOneClass M] [SMul α β] [SMul α M] [SMul β M]
    [IsScalarTower α M M] [IsScalarTower β M M] [IsScalarTower α β M] (c : Con M) :
    IsScalarTower α β c.Quotient where
  smul_assoc a b := Quotient.ind' fun m => congr_arg Quotient.mk'' <| smul_assoc a b m

instance instIsCentralScalar {α M : Type*} [MulOneClass M] [SMul α M] [SMul αᵐᵒᵖ M]
    [IsScalarTower α M M] [IsScalarTower αᵐᵒᵖ M M] [IsCentralScalar α M] (c : Con M) :
    IsCentralScalar α c.Quotient where
  op_smul_eq_smul a := Quotient.ind' fun m => congr_arg Quotient.mk'' <| op_smul_eq_smul a m

@[to_additive]
instance mulAction {α M : Type*} [Monoid α] [MulOneClass M] [MulAction α M] [IsScalarTower α M M]
    (c : Con M) : MulAction α c.Quotient where
  one_smul := Quotient.ind' fun _ => congr_arg Quotient.mk'' <| one_smul _ _
  mul_smul _ _ := Quotient.ind' fun _ => congr_arg Quotient.mk'' <| mul_smul _ _ _

instance mulDistribMulAction {α M : Type*} [Monoid α] [Monoid M] [MulDistribMulAction α M]
    [IsScalarTower α M M] (c : Con M) : MulDistribMulAction α c.Quotient :=
  { smul_one := fun _ => congr_arg Quotient.mk'' <| smul_one _
    smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| smul_mul' _ _ _ }

end Actions

end Con
