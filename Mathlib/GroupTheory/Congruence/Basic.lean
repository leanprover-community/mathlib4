/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.GroupWithZero.Action.Defs
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
@[to_additive prod "Given types with additions `M, N`, the product of two congruence relations
`c` on `M` and `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁`
is related to `y₁` by `c` and `x₂` is related to `y₂` by `d`."]
protected def prod (c : Con M) (d : Con N) : Con (M × N) :=
  { c.toSetoid.prod d.toSetoid with
    mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }

/-- The product of an indexed collection of congruence relations. -/
@[to_additive "The product of an indexed collection of additive congruence relations."]
def pi {ι : Type*} {f : ι → Type*} [∀ i, Mul (f i)] (C : ∀ i, Con (f i)) : Con (∀ i, f i) :=
  { @piSetoid _ _ fun i => (C i).toSetoid with
    mul' := fun h1 h2 i => (C i).mul (h1 i) (h2 i) }

/-- Makes an isomorphism of quotients by two congruence relations, given that the relations are
    equal. -/
@[to_additive "Makes an additive isomorphism of quotients by two additive congruence relations,
given that the relations are equal."]
protected def congr {c d : Con M} (h : c = d) : c.Quotient ≃* d.Quotient :=
  { Quotient.congr (Equiv.refl M) <| by apply Con.ext_iff.mp h with
    map_mul' := fun x y => by rcases x with ⟨⟩; rcases y with ⟨⟩; rfl }

-- The complete lattice of congruence relations on a type
/-- For congruence relations `c, d` on a type `M` with a multiplication, `c ≤ d` iff `∀ x y ∈ M`,
    `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
@[to_additive "For additive congruence relations `c, d` on a type `M` with an addition, `c ≤ d` iff
`∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`."]
instance : LE (Con M) where
  le c d := ∀ ⦃x y⦄, c x y → d x y

/-- Definition of `≤` for congruence relations. -/
@[to_additive "Definition of `≤` for additive congruence relations."]
theorem le_def {c d : Con M} : c ≤ d ↔ ∀ {x y}, c x y → d x y :=
  Iff.rfl

/-- The infimum of a set of congruence relations on a given type with a multiplication. -/
@[to_additive "The infimum of a set of additive congruence relations on a given type with
an addition."]
instance : InfSet (Con M) where
  sInf S :=
    { r := fun x y => ∀ c : Con M, c ∈ S → c x y
      iseqv := ⟨fun x c _ => c.refl x, fun h c hc => c.symm <| h c hc,
        fun h1 h2 c hc => c.trans (h1 c hc) <| h2 c hc⟩
      mul' := fun h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc }

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
@[to_additive "The infimum of a set of additive congruence relations is the same as the infimum of
the set's image under the map to the underlying equivalence relation."]
theorem sInf_toSetoid (S : Set (Con M)) : (sInf S).toSetoid = sInf (toSetoid '' S) :=
  Setoid.ext' fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying binary relation. -/
@[to_additive (attr := simp, norm_cast)
  "The infimum of a set of additive congruence relations is the same as the infimum
  of the set's image under the map to the underlying binary relation."]
theorem coe_sInf (S : Set (Con M)) :
    ⇑(sInf S) = sInf ((⇑) '' S) := by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_iInf {ι : Sort*} (f : ι → Con M) : ⇑(iInf f) = ⨅ i, ⇑(f i) := by
  rw [iInf, coe_sInf, ← Set.range_comp, sInf_range, Function.comp_def]

@[to_additive]
instance : PartialOrder (Con M) where
  le_refl _ _ _ := id
  le_trans _ _ _ h1 h2 _ _ h := h2 <| h1 h
  le_antisymm _ _ hc hd := ext fun _ _ => ⟨fun h => hc h, fun h => hd h⟩

/-- The complete lattice of congruence relations on a given type with a multiplication. -/
@[to_additive "The complete lattice of additive congruence relations on a given type with
an addition."]
instance : CompleteLattice (Con M) where
  __ := completeLatticeOfInf (Con M) fun s =>
      ⟨fun r hr x y h => (h : ∀ r ∈ s, (r : Con M) x y) r hr, fun r hr x y h r' hr' =>
        hr hr'
          h⟩
  inf c d := ⟨c.toSetoid ⊓ d.toSetoid, fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩⟩
  inf_le_left _ _ := fun _ _ h => h.1
  inf_le_right _ _ := fun _ _ h => h.2
  le_inf  _ _ _ hb hc := fun _ _ h => ⟨hb h, hc h⟩
  top := { Setoid.completeLattice.top with mul' := by tauto }
  le_top _ := fun _ _ _ => trivial
  bot := { Setoid.completeLattice.bot with mul' := fun h1 h2 => h1 ▸ h2 ▸ rfl }
  bot_le c := fun x y h => h ▸ c.refl x

/-- The infimum of two congruence relations equals the infimum of the underlying binary
    operations. -/
@[to_additive (attr := simp, norm_cast)
  "The infimum of two additive congruence relations equals the infimum of the underlying binary
  operations."]
theorem coe_inf {c d : Con M} : ⇑(c ⊓ d) = ⇑c ⊓ ⇑d :=
  rfl

/-- Definition of the infimum of two congruence relations. -/
@[to_additive "Definition of the infimum of two additive congruence relations."]
theorem inf_iff_and {c d : Con M} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y :=
  Iff.rfl

/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
    the infimum of the set of congruence relations containing `r`. -/
@[to_additive addConGen_eq "The inductively defined smallest additive congruence relation
containing a binary relation `r` equals the infimum of the set of additive congruence relations
containing `r`."]
theorem conGen_eq (r : M → M → Prop) : conGen r = sInf { s : Con M | ∀ x y, r x y → s x y } :=
  le_antisymm
    (le_sInf (fun s hs x y (hxy : (conGen r) x y) =>
      show s x y by
        apply ConGen.Rel.recOn (motive := fun x y _ => s x y) hxy
        · exact fun x y h => hs x y h
        · exact s.refl'
        · exact fun _ => s.symm'
        · exact fun _ _ => s.trans'
        · exact fun _ _ => s.mul))
    (sInf_le ConGen.Rel.of)

/-- The smallest congruence relation containing a binary relation `r` is contained in any
    congruence relation containing `r`. -/
@[to_additive addConGen_le "The smallest additive congruence relation containing a binary
relation `r` is contained in any additive congruence relation containing `r`."]
theorem conGen_le {r : M → M → Prop} {c : Con M} (h : ∀ x y, r x y → c x y) :
    conGen r ≤ c := by rw [conGen_eq]; exact sInf_le h

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
    containing `s` contains the smallest congruence relation containing `r`. -/
@[to_additive addConGen_mono "Given binary relations `r, s` with `r` contained in `s`, the
smallest additive congruence relation containing `s` contains the smallest additive congruence
relation containing `r`."]
theorem conGen_mono {r s : M → M → Prop} (h : ∀ x y, r x y → s x y) : conGen r ≤ conGen s :=
  conGen_le fun x y hr => ConGen.Rel.of _ _ <| h x y hr

/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
@[to_additive (attr := simp) addConGen_of_addCon "Additive congruence relations equal the smallest
additive congruence relation in which they are contained."]
theorem conGen_of_con (c : Con M) : conGen c = c :=
  le_antisymm (by rw [conGen_eq]; exact sInf_le fun _ _ => id) ConGen.Rel.of

-- Porting note: removing simp, simp can prove it
/-- The map sending a binary relation to the smallest congruence relation in which it is
    contained is idempotent. -/
@[to_additive addConGen_idem "The map sending a binary relation to the smallest additive
congruence relation in which it is contained is idempotent."]
theorem conGen_idem (r : M → M → Prop) : conGen (conGen r) = conGen r :=
  conGen_of_con _

/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
    the binary relation '`x` is related to `y` by `c` or `d`'. -/
@[to_additive sup_eq_addConGen "The supremum of additive congruence relations `c, d` equals the
smallest additive congruence relation containing the binary relation '`x` is related to `y`
by `c` or `d`'."]
theorem sup_eq_conGen (c d : Con M) : c ⊔ d = conGen fun x y => c x y ∨ d x y := by
  rw [conGen_eq]
  apply congr_arg sInf
  simp only [le_def, or_imp, ← forall_and]

/-- The supremum of two congruence relations equals the smallest congruence relation containing
    the supremum of the underlying binary operations. -/
@[to_additive "The supremum of two additive congruence relations equals the smallest additive
congruence relation containing the supremum of the underlying binary operations."]
theorem sup_def {c d : Con M} : c ⊔ d = conGen (⇑c ⊔ ⇑d) := by rw [sup_eq_conGen]; rfl

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
    containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by
    `c`'. -/
@[to_additive sSup_eq_addConGen "The supremum of a set of additive congruence relations `S` equals
the smallest additive congruence relation containing the binary relation 'there exists `c ∈ S`
such that `x` is related to `y` by `c`'."]
theorem sSup_eq_conGen (S : Set (Con M)) :
    sSup S = conGen fun x y => ∃ c : Con M, c ∈ S ∧ c x y := by
  rw [conGen_eq]
  apply congr_arg sInf
  ext
  exact ⟨fun h _ _ ⟨r, hr⟩ => h hr.1 hr.2, fun h r hS _ _ hr => h _ _ ⟨r, hS, hr⟩⟩

/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
    containing the supremum of the set's image under the map to the underlying binary relation. -/
@[to_additive "The supremum of a set of additive congruence relations is the same as the smallest
additive congruence relation containing the supremum of the set's image under the map to the
underlying binary relation."]
theorem sSup_def {S : Set (Con M)} :
    sSup S = conGen (sSup ((⇑) '' S)) := by
  rw [sSup_eq_conGen, sSup_image]
  congr with (x y)
  simp only [sSup_image, iSup_apply, iSup_Prop_eq, exists_prop, rel_eq_coe]

variable (M)

/-- There is a Galois insertion of congruence relations on a type with a multiplication `M` into
    binary relations on `M`. -/
@[to_additive "There is a Galois insertion of additive congruence relations on a type with
an addition `M` into binary relations on `M`."]
protected def gi : @GaloisInsertion (M → M → Prop) (Con M) _ _ conGen DFunLike.coe where
  choice r _ := conGen r
  gc _ c := ⟨fun H _ _ h => H <| ConGen.Rel.of _ _ h, @fun H => conGen_of_con c ▸ conGen_mono H⟩
  le_l_u x := (conGen_of_con x).symm ▸ le_refl x
  choice_eq _ _ := rfl

variable {M} (c)

/-- Given a function `f`, the smallest congruence relation containing the binary relation on `f`'s
    image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)`
    by a congruence relation `c`.' -/
@[to_additive "Given a function `f`, the smallest additive congruence relation containing the
binary relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the
elements of `f⁻¹(y)` by an additive congruence relation `c`.'"]
def mapGen (f : M → N) : Con N :=
  conGen fun x y => ∃ a b, f a = x ∧ f b = y ∧ c a b

/-- Given a surjective multiplicative-preserving function `f` whose kernel is contained in a
    congruence relation `c`, the congruence relation on `f`'s codomain defined by '`x ≈ y` iff the
    elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/
@[to_additive "Given a surjective addition-preserving function `f` whose kernel is contained in
an additive congruence relation `c`, the additive congruence relation on `f`'s codomain defined
by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.'"]
def mapOfSurjective (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (h : mulKer f H ≤ c)
    (hf : Surjective f) : Con N :=
  { c.toSetoid.mapOfSurjective f h hf with
    mul' := fun h₁ h₂ => by
      rcases h₁ with ⟨a, b, rfl, rfl, h1⟩
      rcases h₂ with ⟨p, q, rfl, rfl, h2⟩
      exact ⟨a * p, b * q, by rw [H], by rw [H], c.mul h1 h2⟩ }

/-- A specialization of 'the smallest congruence relation containing a congruence relation `c`
    equals `c`'. -/
@[to_additive "A specialization of 'the smallest additive congruence relation containing
an additive congruence relation `c` equals `c`'."]
theorem mapOfSurjective_eq_mapGen {c : Con M} {f : M → N} (H : ∀ x y, f (x * y) = f x * f y)
    (h : mulKer f H ≤ c) (hf : Surjective f) : c.mapGen f = c.mapOfSurjective f H h hf := by
  rw [← conGen_of_con (c.mapOfSurjective f H h hf)]; rfl

/-- Given types with multiplications `M, N` and a congruence relation `c` on `N`, a
    multiplication-preserving map `f : M → N` induces a congruence relation on `f`'s domain
    defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' -/
@[to_additive "Given types with additions `M, N` and an additive congruence relation `c` on `N`,
an addition-preserving map `f : M → N` induces an additive congruence relation on `f`'s domain
defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' "]
def comap (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (c : Con N) : Con M :=
  { c.toSetoid.comap f with
    mul' := @fun w x y z h1 h2 => show c (f (w * y)) (f (x * z)) by rw [H, H]; exact c.mul h1 h2 }

@[to_additive (attr := simp)]
theorem comap_rel {f : M → N} (H : ∀ x y, f (x * y) = f x * f y) {c : Con N} {x y : M} :
    comap f H c x y ↔ c (f x) (f y) :=
  Iff.rfl

section

open Quotient

/-- Given a congruence relation `c` on a type `M` with a multiplication, the order-preserving
    bijection between the set of congruence relations containing `c` and the congruence relations
    on the quotient of `M` by `c`. -/
@[to_additive "Given an additive congruence relation `c` on a type `M` with an addition,
the order-preserving bijection between the set of additive congruence relations containing `c` and
the additive congruence relations on the quotient of `M` by `c`."]
def correspondence : { d // c ≤ d } ≃o Con c.Quotient where
  toFun d :=
    d.1.mapOfSurjective (↑) (fun x y => rfl) (by rw [mul_ker_mk_eq]; exact d.2) <|
      @Quotient.exists_rep _ c.toSetoid
  invFun d :=
    ⟨comap ((↑) : M → c.Quotient) (fun x y => rfl) d, fun x y h =>
      show d x y by rw [c.eq.2 h]; exact d.refl _⟩
  left_inv d :=
    -- Porting note: by exact needed for unknown reason
    by exact
      Subtype.ext_iff_val.2 <|
        ext fun x y =>
          ⟨fun h =>
            let ⟨a, b, hx, hy, H⟩ := h
            d.1.trans (d.1.symm <| d.2 <| c.eq.1 hx) <| d.1.trans H <| d.2 <| c.eq.1 hy,
            fun h => ⟨_, _, rfl, rfl, h⟩⟩
  right_inv d :=
    -- Porting note: by exact needed for unknown reason
    by exact
      ext fun x y =>
        ⟨fun h =>
          let ⟨_, _, hx, hy, H⟩ := h
          hx ▸ hy ▸ H,
          Con.induction_on₂ x y fun w z h => ⟨w, z, rfl, rfl, h⟩⟩
  map_rel_iff' := @fun s t => by
    constructor
    · intros h x y hs
      rcases h ⟨x, y, rfl, rfl, hs⟩ with ⟨a, b, hx, hy, ht⟩
      exact t.1.trans (t.1.symm <| t.2 <| Quotient.eq_rel.1 hx)
        (t.1.trans ht (t.2 <| Quotient.eq_rel.1 hy))
    · intros h _ _ hs
      rcases hs with ⟨a, b, hx, hy, Hs⟩
      exact ⟨a, b, hx, hy, h Hs⟩

end

end

section MulOneClass

variable [MulOneClass M] [MulOneClass N] [MulOneClass P] (c : Con M)

-- Porting note: made M implicit
/-- The submonoid of `M × M` defined by a congruence relation on a monoid `M`. -/
@[to_additive (attr := coe) "The `AddSubmonoid` of `M × M` defined by an additive congruence
relation on an `AddMonoid` `M`."]
protected def submonoid : Submonoid (M × M) where
  carrier := { x | c x.1 x.2 }
  one_mem' := c.iseqv.1 1
  mul_mem' := c.mul

variable {c}

/-- The congruence relation on a monoid `M` from a submonoid of `M × M` for which membership
    is an equivalence relation. -/
@[to_additive "The additive congruence relation on an `AddMonoid` `M` from
an `AddSubmonoid` of `M × M` for which membership is an equivalence relation."]
def ofSubmonoid (N : Submonoid (M × M)) (H : Equivalence fun x y => (x, y) ∈ N) : Con M where
  r x y := (x, y) ∈ N
  iseqv := H
  mul' := N.mul_mem

/-- Coercion from a congruence relation `c` on a monoid `M` to the submonoid of `M × M` whose
    elements are `(x, y)` such that `x` is related to `y` by `c`. -/
@[to_additive "Coercion from a congruence relation `c` on an `AddMonoid` `M`
to the `AddSubmonoid` of `M × M` whose elements are `(x, y)` such that `x`
is related to `y` by `c`."]
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
-- Porting note: removed dot notation
theorem mrange_mk' : MonoidHom.mrange c.mk' = ⊤ :=
  MonoidHom.mrange_top_iff_surjective.2 mk'_surjective

variable {f : M →* P}

/-- Given a congruence relation `c` on a monoid and a homomorphism `f` constant on `c`'s
    equivalence classes, `f` has the same image as the homomorphism that `f` induces on the
    quotient. -/
@[to_additive "Given an additive congruence relation `c` on an `AddMonoid` and a homomorphism `f`
constant on `c`'s equivalence classes, `f` has the same image as the homomorphism that `f` induces
on the quotient."]
theorem lift_range (H : c ≤ ker f) : MonoidHom.mrange (c.lift f H) = MonoidHom.mrange f :=
  Submonoid.ext fun x => ⟨by rintro ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨↑y, hy⟩⟩

/-- Given a monoid homomorphism `f`, the induced homomorphism on the quotient by `f`'s kernel has
    the same image as `f`. -/
@[to_additive (attr := simp) "Given an `AddMonoid` homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`."]
theorem kerLift_range_eq : MonoidHom.mrange (kerLift f) = MonoidHom.mrange f :=
  lift_range fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for monoids**. -/
@[to_additive "The first isomorphism theorem for `AddMonoid`s."]
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
  "The first isomorphism theorem for `AddMonoid`s in the case of a homomorphism
  with right inverse."]
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
@[to_additive "The first isomorphism theorem for `AddMonoid`s in the case of a surjective
homomorphism.

For a `computable` version, see `AddCon.quotientKerEquivOfRightInverse`.
"]
noncomputable def quotientKerEquivOfSurjective (f : M →* P) (hf : Surjective f) :
    (ker f).Quotient ≃* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

/-- If e : M →* N is surjective then (c.comap e).Quotient ≃* c.Quotient
with c : Con N -/
@[to_additive "If e : M →* N is surjective then (c.comap e).Quotient ≃* c.Quotient
with c : AddCon N"]
noncomputable def comapQuotientEquivOfSurj (c : Con M) (f : N →* M) (hf : Function.Surjective f) :
    (Con.comap f f.map_mul c).Quotient ≃* c.Quotient :=
  (Con.congr Con.comap_eq).trans <| Con.quotientKerEquivOfSurjective
  (c.mk'.comp f) <| Con.mk'_surjective.comp hf

/-- The **second isomorphism theorem for monoids**. -/
@[to_additive "The second isomorphism theorem for `AddMonoid`s."]
noncomputable def comapQuotientEquiv (f : N →* M) :
    (comap f f.map_mul c).Quotient ≃* MonoidHom.mrange (c.mk'.comp f) :=
  (Con.congr comap_eq).trans <| quotientKerEquivRange <| c.mk'.comp f

/-- The **third isomorphism theorem for monoids**. -/
@[to_additive "The third isomorphism theorem for `AddMonoid`s."]
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
