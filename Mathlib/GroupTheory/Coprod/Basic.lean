/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.GroupTheory.Congruence.Basic

/-!
# Coproduct (free product) of two monoids or groups

In this file we define `Monoid.Coprod M N` (notation: `M ∗ N`)
to be the coproduct (a.k.a. free product) of two monoids.
The same type is used for the coproduct of two monoids and for the coproduct of two groups.

The coproduct `M ∗ N` has the following universal property:
for any monoid `P` and homomorphisms `f : M →* P`, `g : N →* P`,
there exists a unique homomorphism `fg : M ∗ N →* P`
such that `fg ∘ Monoid.Coprod.inl = f` and `fg ∘ Monoid.Coprod.inr = g`,
where `Monoid.Coprod.inl : M →* M ∗ N`
and `Monoid.Coprod.inr : N →* M ∗ N` are canonical embeddings.
This homomorphism `fg` is given by `Monoid.Coprod.lift f g`.

We also define some homomorphisms and isomorphisms about `M ∗ N`,
and provide additive versions of all definitions and theorems.

## Main definitions

### Types

* `Monoid.Coprod M N` (a.k.a. `M ∗ N`):
  the free product (a.k.a. coproduct) of two monoids `M` and `N`.
* `AddMonoid.Coprod M N` (no notation): the additive version of `Monoid.Coprod`.

In other sections, we only list multiplicative definitions.

### Instances

* `MulOneClass`, `Monoid`, and `Group` structures on the coproduct `M ∗ N`.

### Monoid homomorphisms

* `Monoid.Coprod.mk`: the projection `FreeMonoid (M ⊕ N) →* M ∗ N`.

* `Monoid.Coprod.inl`, `Monoid.Coprod.inr`: canonical embeddings `M →* M ∗ N` and `N →* M ∗ N`.

* `Monoid.Coprod.lift`: construct a monoid homomorphism `M ∗ N →* P`
  from homomorphisms `M →* P` and `N →* P`; see also `Monoid.Coprod.liftEquiv`.

* `Monoid.Coprod.clift`: a constructor for homomorphisms `M ∗ N →* P`
  that allows the user to control the computational behavior.

* `Monoid.Coprod.map`: combine two homomorphisms `f : M →* N` and `g : M' →* N'`
  into `M ∗ M' →* N ∗ N'`.

* `Monoid.Coprod.swap`: the natural homomorphism `M ∗ N →* N ∗ M`.

* `Monoid.Coprod.fst`, `Monoid.Coprod.snd`, and `Monoid.Coprod.toProd`:
  natural projections `M ∗ N →* M`, `M ∗ N →* N`, and `M ∗ N →* M × N`.

### Monoid isomorphisms

* `MulEquiv.coprodCongr`: a `MulEquiv` version of `Monoid.Coprod.map`.
* `MulEquiv.coprodComm`: a `MulEquiv` version of `Monoid.Coprod.swap`.
* `MulEquiv.coprodAssoc`: associativity of the coproduct.
* `MulEquiv.coprodPUnit`, `MulEquiv.punitCoprod`:
  free product by `PUnit` on the left or on the right is isomorphic to the original monoid.

## Main results

The universal property of the coproduct
is given by the definition `Monoid.Coprod.lift` and the lemma `Monoid.Coprod.lift_unique`.

We also prove a slightly more general extensionality lemma `Monoid.Coprod.hom_ext`
for homomorphisms `M ∗ N →* P` and prove lots of basic lemmas like `Monoid.Coprod.fst_comp_inl`.

## Implementation details

The definition of the coproduct of an indexed family of monoids is formalized in `Monoid.CoprodI`.
While mathematically `M ∗ N` is a particular case
of the coproduct of an indexed family of monoids,
it is easier to build API from scratch instead of using something like

```
def Monoid.Coprod M N := Monoid.CoprodI ![M, N]
```

or

```
def Monoid.Coprod M N := Monoid.CoprodI (fun b : Bool => cond b M N)
```

There are several reasons to build an API from scratch.

- API about `Con` makes it easy to define the required type and prove the universal property,
  so there is little overhead compared to transferring API from `Monoid.CoprodI`.
- If `M` and `N` live in different universes, then the definition has to add `ULift`s;
  this makes it harder to transfer API and definitions.
- As of now, we have no way
  to automatically build an instance of `(k : Fin 2) → Monoid (![M, N] k)`
  from `[Monoid M]` and `[Monoid N]`,
  not even speaking about more advanced typeclass assumptions that involve both `M` and `N`.
- Using a list of `M ⊕ N` instead of, e.g., a list of `Σ k : Fin 2, ![M, N] k`
  as the underlying type makes it possible to write computationally effective code
  (though this point is not tested yet).

## TODO

- Prove `Monoid.CoprodI (f : Fin 2 → Type*) ≃* f 0 ∗ f 1` and
  `Monoid.CoprodI (f : Bool → Type*) ≃* f false ∗ f true`.

## Tags

group, monoid, coproduct, free product
-/

assert_not_exists MonoidWithZero

open FreeMonoid Function List Set

namespace Monoid

/-- The minimal congruence relation `c` on `FreeMonoid (M ⊕ N)`
such that `FreeMonoid.of ∘ Sum.inl` and `FreeMonoid.of ∘ Sum.inr` are monoid homomorphisms
to the quotient by `c`. -/
@[to_additive /-- The minimal additive congruence relation `c` on `FreeAddMonoid (M ⊕ N)`
such that `FreeAddMonoid.of ∘ Sum.inl` and `FreeAddMonoid.of ∘ Sum.inr`
are additive monoid homomorphisms to the quotient by `c`. -/]
def coprodCon (M N : Type*) [MulOneClass M] [MulOneClass N] : Con (FreeMonoid (M ⊕ N)) :=
  sInf {c |
    (∀ x y : M, c (of (Sum.inl (x * y))) (of (Sum.inl x) * of (Sum.inl y)))
    ∧ (∀ x y : N, c (of (Sum.inr (x * y))) (of (Sum.inr x) * of (Sum.inr y)))
    ∧ c (of <| Sum.inl 1) 1 ∧ c (of <| Sum.inr 1) 1}

/-- Coproduct of two monoids or groups. -/
@[to_additive /-- Coproduct of two additive monoids or groups. -/]
def Coprod (M N : Type*) [MulOneClass M] [MulOneClass N] := (coprodCon M N).Quotient

namespace Coprod

@[inherit_doc]
scoped infix:30 " ∗ " => Coprod

section MulOneClass

variable {M N M' N' P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass M'] [MulOneClass N']
  [MulOneClass P]

@[to_additive] protected instance : MulOneClass (M ∗ N) := Con.mulOneClass _

/-- The natural projection `FreeMonoid (M ⊕ N) →* M ∗ N`. -/
@[to_additive /-- The natural projection `FreeAddMonoid (M ⊕ N) →+ AddMonoid.Coprod M N`. -/]
def mk : FreeMonoid (M ⊕ N) →* M ∗ N := Con.mk' _

@[to_additive (attr := simp)]
theorem con_ker_mk : Con.ker mk = coprodCon M N := Con.mk'_ker _

@[to_additive]
theorem mk_surjective : Surjective (@mk M N _ _) := Quot.mk_surjective

@[to_additive (attr := simp)]
theorem mrange_mk : MonoidHom.mrange (@mk M N _ _) = ⊤ := Con.mrange_mk'

@[to_additive]
theorem mk_eq_mk {w₁ w₂ : FreeMonoid (M ⊕ N)} : mk w₁ = mk w₂ ↔ coprodCon M N w₁ w₂ := Con.eq _

/-- The natural embedding `M →* M ∗ N`. -/
@[to_additive /-- The natural embedding `M →+ AddMonoid.Coprod M N`. -/]
def inl : M →* M ∗ N where
  toFun := fun x => mk (of (.inl x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.1
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.1 x y

/-- The natural embedding `N →* M ∗ N`. -/
@[to_additive /-- The natural embedding `N →+ AddMonoid.Coprod M N`. -/]
def inr : N →* M ∗ N where
  toFun := fun x => mk (of (.inr x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.2
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.2.1 x y

@[to_additive (attr := simp)]
theorem mk_of_inl (x : M) : (mk (of (.inl x)) : M ∗ N) = inl x := rfl

@[to_additive (attr := simp)]
theorem mk_of_inr (x : N) : (mk (of (.inr x)) : M ∗ N) = inr x := rfl

@[to_additive (attr := elab_as_elim)]
theorem induction_on' {C : M ∗ N → Prop} (m : M ∗ N)
    (one : C 1)
    (inl_mul : ∀ m x, C x → C (inl m * x))
    (inr_mul : ∀ n x, C x → C (inr n * x)) : C m := by
  rcases mk_surjective m with ⟨x, rfl⟩
  induction x using FreeMonoid.inductionOn' with
  | one => exact one
  | mul_of x xs ih =>
    cases x with
    | inl m => simpa using inl_mul m _ ih
    | inr n => simpa using inr_mul n _ ih

@[to_additive (attr := elab_as_elim)]
theorem induction_on {C : M ∗ N → Prop} (m : M ∗ N)
    (inl : ∀ m, C (inl m)) (inr : ∀ n, C (inr n)) (mul : ∀ x y, C x → C y → C (x * y)) : C m :=
  induction_on' m (by simpa using inl 1) (fun _ _ ↦ mul _ _ (inl _)) fun _ _ ↦ mul _ _ (inr _)

/-- Lift a monoid homomorphism `FreeMonoid (M ⊕ N) →* P` satisfying additional properties to
`M ∗ N →* P`. In many cases, `Coprod.lift` is more convenient.

Compared to `Coprod.lift`,
this definition allows a user to provide a custom computational behavior.
Also, it only needs `MulOneClass` assumptions while `Coprod.lift` needs a `Monoid` structure.
-/
@[to_additive /-- Lift an additive monoid homomorphism `FreeAddMonoid (M ⊕ N) →+ P` satisfying
additional properties to `AddMonoid.Coprod M N →+ P`.

Compared to `AddMonoid.Coprod.lift`,
this definition allows a user to provide a custom computational behavior.
Also, it only needs `AddZeroClass` assumptions
while `AddMonoid.Coprod.lift` needs an `AddMonoid` structure. -/]
def clift (f : FreeMonoid (M ⊕ N) →* P)
    (hM₁ : f (of (.inl 1)) = 1) (hN₁ : f (of (.inr 1)) = 1)
    (hM : ∀ x y, f (of (.inl (x * y))) = f (of (.inl x) * of (.inl y)))
    (hN : ∀ x y, f (of (.inr (x * y))) = f (of (.inr x) * of (.inr y))) :
    M ∗ N →* P :=
  Con.lift _ f <| sInf_le ⟨hM, hN, hM₁.trans (map_one f).symm, hN₁.trans (map_one f).symm⟩

@[to_additive (attr := simp)]
theorem clift_apply_inl (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : M) :
    clift f hM₁ hN₁ hM hN (inl x) = f (of (.inl x)) :=
  rfl

@[to_additive (attr := simp)]
theorem clift_apply_inr (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : N) :
    clift f hM₁ hN₁ hM hN (inr x) = f (of (.inr x)) :=
  rfl

@[to_additive (attr := simp)]
theorem clift_apply_mk (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN w) :
    clift f hM₁ hN₁ hM hN (mk w) = f w :=
  rfl

@[to_additive (attr := simp)]
theorem clift_comp_mk (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) :
    (clift f hM₁ hN₁ hM hN).comp mk = f :=
  DFunLike.ext' rfl

@[to_additive (attr := simp)]
theorem mclosure_range_inl_union_inr :
    Submonoid.closure (range (inl : M →* M ∗ N) ∪ range (inr : N →* M ∗ N)) = ⊤ := by
  rw [← mrange_mk, MonoidHom.mrange_eq_map, ← closure_range_of, MonoidHom.map_mclosure,
    ← range_comp, Sum.range_eq]; rfl

@[to_additive (attr := simp)] theorem mrange_inl_sup_mrange_inr :
    MonoidHom.mrange (inl : M →* M ∗ N) ⊔ MonoidHom.mrange (inr : N →* M ∗ N) = ⊤ := by
  rw [← mclosure_range_inl_union_inr, Submonoid.closure_union, ← MonoidHom.coe_mrange,
    ← MonoidHom.coe_mrange, Submonoid.closure_eq, Submonoid.closure_eq]

@[to_additive]
theorem codisjoint_mrange_inl_mrange_inr :
    Codisjoint (MonoidHom.mrange (inl : M →* M ∗ N)) (MonoidHom.mrange inr) :=
  codisjoint_iff.2 mrange_inl_sup_mrange_inr

@[to_additive] theorem mrange_eq (f : M ∗ N →* P) :
    MonoidHom.mrange f = MonoidHom.mrange (f.comp inl) ⊔ MonoidHom.mrange (f.comp inr) := by
  rw [MonoidHom.mrange_eq_map, ← mrange_inl_sup_mrange_inr, Submonoid.map_sup, MonoidHom.map_mrange,
    MonoidHom.map_mrange]

/-- Extensionality lemma for monoid homomorphisms `M ∗ N →* P`.
If two homomorphisms agree on the ranges of `Monoid.Coprod.inl` and `Monoid.Coprod.inr`,
then they are equal. -/
@[to_additive (attr := ext 1100)
  /-- Extensionality lemma for additive monoid homomorphisms `AddMonoid.Coprod M N →+ P`.
  If two homomorphisms agree on the ranges of `AddMonoid.Coprod.inl` and `AddMonoid.Coprod.inr`,
  then they are equal. -/]
theorem hom_ext {f g : M ∗ N →* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr) :
    f = g :=
  MonoidHom.eq_of_eqOn_denseM mclosure_range_inl_union_inr <| eqOn_union.2
    ⟨eqOn_range.2 <| DFunLike.ext'_iff.1 h₁, eqOn_range.2 <| DFunLike.ext'_iff.1 h₂⟩

@[to_additive (attr := simp)]
theorem clift_mk :
    clift (mk : FreeMonoid (M ⊕ N) →* M ∗ N) (map_one inl) (map_one inr) (map_mul inl)
      (map_mul inr) = .id _ :=
  hom_ext rfl rfl

/-- Map `M ∗ N` to `M' ∗ N'` by applying `Sum.map f g` to each element of the underlying list. -/
@[to_additive /-- Map `AddMonoid.Coprod M N` to `AddMonoid.Coprod M' N'`
by applying `Sum.map f g` to each element of the underlying list. -/]
def map (f : M →* M') (g : N →* N') : M ∗ N →* M' ∗ N' :=
  clift (mk.comp <| FreeMonoid.map <| Sum.map f g)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_one, mk_of_inl])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_one, mk_of_inr])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_mul, mk_of_inl])
    fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_mul, mk_of_inr]

@[to_additive (attr := simp)]
theorem map_mk_ofList (f : M →* M') (g : N →* N') (l : List (M ⊕ N)) :
    map f g (mk (ofList l)) = mk (ofList (l.map (Sum.map f g))) :=
  rfl

@[to_additive (attr := simp)]
theorem map_apply_inl (f : M →* M') (g : N →* N') (x : M) : map f g (inl x) = inl (f x) := rfl

@[to_additive (attr := simp)]
theorem map_apply_inr (f : M →* M') (g : N →* N') (x : N) : map f g (inr x) = inr (g x) := rfl

@[to_additive (attr := simp)]
theorem map_comp_inl (f : M →* M') (g : N →* N') : (map f g).comp inl = inl.comp f := rfl

@[to_additive (attr := simp)]
theorem map_comp_inr (f : M →* M') (g : N →* N') : (map f g).comp inr = inr.comp g := rfl

@[to_additive (attr := simp)]
theorem map_id_id : map (.id M) (.id N) = .id (M ∗ N) := hom_ext rfl rfl

@[to_additive]
theorem map_comp_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' →* M'') (g' : N' →* N'')
    (f : M →* M') (g : N →* N') : (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) :=
  hom_ext rfl rfl

@[to_additive]
theorem map_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' →* M'') (g' : N' →* N'')
    (f : M →* M') (g : N →* N') (x : M ∗ N) :
    map f' g' (map f g x) = map (f'.comp f) (g'.comp g) x :=
  DFunLike.congr_fun (map_comp_map f' g' f g) x

variable (M N)

/-- Map `M ∗ N` to `N ∗ M` by applying `Sum.swap` to each element of the underlying list.

See also `MulEquiv.coprodComm` for a `MulEquiv` version. -/
@[to_additive /-- Map `AddMonoid.Coprod M N` to `AddMonoid.Coprod N M`
  by applying `Sum.swap` to each element of the underlying list.

See also `AddEquiv.coprodComm` for an `AddEquiv` version. -/]
def swap : M ∗ N →* N ∗ M :=
  clift (mk.comp <| FreeMonoid.map Sum.swap)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_one])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_one])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_mul])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_mul])

@[to_additive (attr := simp)]
theorem swap_comp_swap : (swap M N).comp (swap N M) = .id _ := hom_ext rfl rfl

variable {M N}

@[to_additive (attr := simp)]
theorem swap_swap (x : M ∗ N) : swap N M (swap M N x) = x :=
  DFunLike.congr_fun (swap_comp_swap _ _) x

@[to_additive]
theorem swap_comp_map (f : M →* M') (g : N →* N') :
    (swap M' N').comp (map f g) = (map g f).comp (swap M N) :=
  hom_ext rfl rfl

@[to_additive]
theorem swap_map (f : M →* M') (g : N →* N') (x : M ∗ N) :
    swap M' N' (map f g x) = map g f (swap M N x) :=
  DFunLike.congr_fun (swap_comp_map f g) x

@[to_additive (attr := simp)] theorem swap_comp_inl : (swap M N).comp inl = inr := rfl
@[to_additive (attr := simp)] theorem swap_inl (x : M) : swap M N (inl x) = inr x := rfl
@[to_additive (attr := simp)] theorem swap_comp_inr : (swap M N).comp inr = inl := rfl
@[to_additive (attr := simp)] theorem swap_inr (x : N) : swap M N (inr x) = inl x := rfl

@[to_additive]
theorem swap_injective : Injective (swap M N) := LeftInverse.injective swap_swap

@[to_additive (attr := simp)]
theorem swap_inj {x y : M ∗ N} : swap M N x = swap M N y ↔ x = y := swap_injective.eq_iff

@[to_additive (attr := simp)]
theorem swap_eq_one {x : M ∗ N} : swap M N x = 1 ↔ x = 1 := swap_injective.eq_iff' (map_one _)

@[to_additive]
theorem swap_surjective : Surjective (swap M N) := LeftInverse.surjective swap_swap

@[to_additive]
theorem swap_bijective : Bijective (swap M N) := ⟨swap_injective, swap_surjective⟩

@[to_additive (attr := simp)]
theorem mker_swap : MonoidHom.mker (swap M N) = ⊥ := Submonoid.ext fun _ ↦ swap_eq_one

@[to_additive (attr := simp)]
theorem mrange_swap : MonoidHom.mrange (swap M N) = ⊤ :=
  MonoidHom.mrange_eq_top_of_surjective _ swap_surjective

end MulOneClass

section Lift

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [Monoid P]

/-- Lift a pair of monoid homomorphisms `f : M →* P`, `g : N →* P`
to a monoid homomorphism `M ∗ N →* P`.

See also `Coprod.clift` for a version that allows custom computational behavior
and works for a `MulOneClass` codomain.
-/
@[to_additive /-- Lift a pair of additive monoid homomorphisms `f : M →+ P`, `g : N →+ P`
to an additive monoid homomorphism `AddMonoid.Coprod M N →+ P`.

See also `AddMonoid.Coprod.clift` for a version that allows custom computational behavior
and works for an `AddZeroClass` codomain. -/]
def lift (f : M →* P) (g : N →* P) : (M ∗ N) →* P :=
  clift (FreeMonoid.lift <| Sum.elim f g) (map_one f) (map_one g) (map_mul f) (map_mul g)

@[to_additive (attr := simp)]
theorem lift_apply_mk (f : M →* P) (g : N →* P) (x : FreeMonoid (M ⊕ N)) :
    lift f g (mk x) = FreeMonoid.lift (Sum.elim f g) x :=
  rfl

@[to_additive (attr := simp)]
theorem lift_apply_inl (f : M →* P) (g : N →* P) (x : M) : lift f g (inl x) = f x :=
  rfl

@[to_additive]
theorem lift_unique {f : M →* P} {g : N →* P} {fg : M ∗ N →* P} (h₁ : fg.comp inl = f)
    (h₂ : fg.comp inr = g) : fg = lift f g :=
  hom_ext h₁ h₂

@[to_additive (attr := simp)]
theorem lift_comp_inl (f : M →* P) (g : N →* P) : (lift f g).comp inl = f := rfl

@[to_additive (attr := simp)]
theorem lift_apply_inr (f : M →* P) (g : N →* P) (x : N) : lift f g (inr x) = g x :=
  rfl

@[to_additive (attr := simp)]
theorem lift_comp_inr (f : M →* P) (g : N →* P) : (lift f g).comp inr = g := rfl

@[to_additive (attr := simp)]
theorem lift_comp_swap (f : M →* P) (g : N →* P) : (lift f g).comp (swap N M) = lift g f :=
  hom_ext rfl rfl

@[to_additive (attr := simp)]
theorem lift_swap (f : M →* P) (g : N →* P) (x : N ∗ M) : lift f g (swap N M x) = lift g f x :=
  DFunLike.congr_fun (lift_comp_swap f g) x

@[to_additive]
theorem comp_lift {P' : Type*} [Monoid P'] (f : P →* P') (g₁ : M →* P) (g₂ : N →* P) :
    f.comp (lift g₁ g₂) = lift (f.comp g₁) (f.comp g₂) :=
  hom_ext (by rw [MonoidHom.comp_assoc, lift_comp_inl, lift_comp_inl]) <| by
    rw [MonoidHom.comp_assoc, lift_comp_inr, lift_comp_inr]

/-- `Coprod.lift` as an equivalence. -/
@[to_additive /-- `AddMonoid.Coprod.lift` as an equivalence. -/]
def liftEquiv : (M →* P) × (N →* P) ≃ (M ∗ N →* P) where
  toFun fg := lift fg.1 fg.2
  invFun f := (f.comp inl, f.comp inr)
  right_inv _ := Eq.symm <| lift_unique rfl rfl

@[to_additive (attr := simp)]
theorem mrange_lift (f : M →* P) (g : N →* P) :
    MonoidHom.mrange (lift f g) = MonoidHom.mrange f ⊔ MonoidHom.mrange g := by
  simp [mrange_eq]

end Lift

section ToProd

variable {M N : Type*} [Monoid M] [Monoid N]

@[to_additive] instance : Monoid (M ∗ N) :=
  { mul_assoc := (Con.monoid _).mul_assoc
    one_mul := (Con.monoid _).one_mul
    mul_one := (Con.monoid _).mul_one }

/-- The natural projection `M ∗ N →* M`. -/
@[to_additive /-- The natural projection `AddMonoid.Coprod M N →+ M`. -/]
def fst : M ∗ N →* M := lift (.id M) 1

/-- The natural projection `M ∗ N →* N`. -/
@[to_additive /-- The natural projection `AddMonoid.Coprod M N →+ N`. -/]
def snd : M ∗ N →* N := lift 1 (.id N)

/-- The natural projection `M ∗ N →* M × N`. -/
@[to_additive toProd /-- The natural projection `AddMonoid.Coprod M N →+ M × N`. -/]
def toProd : M ∗ N →* M × N := lift (.inl _ _) (.inr _ _)

@[to_additive (attr := simp)] theorem fst_comp_inl : (fst : M ∗ N →* M).comp inl = .id _ := rfl
@[to_additive (attr := simp)] theorem fst_apply_inl (x : M) : fst (inl x : M ∗ N) = x := rfl
@[to_additive (attr := simp)] theorem fst_comp_inr : (fst : M ∗ N →* M).comp inr = 1 := rfl
@[to_additive (attr := simp)] theorem fst_apply_inr (x : N) : fst (inr x : M ∗ N) = 1 := rfl
@[to_additive (attr := simp)] theorem snd_comp_inl : (snd : M ∗ N →* N).comp inl = 1 := rfl
@[to_additive (attr := simp)] theorem snd_apply_inl (x : M) : snd (inl x : M ∗ N) = 1 := rfl
@[to_additive (attr := simp)] theorem snd_comp_inr : (snd : M ∗ N →* N).comp inr = .id _ := rfl
@[to_additive (attr := simp)] theorem snd_apply_inr (x : N) : snd (inr x : M ∗ N) = x := rfl

@[to_additive (attr := simp) toProd_comp_inl]
theorem toProd_comp_inl : (toProd : M ∗ N →* M × N).comp inl = .inl _ _ := rfl

@[to_additive (attr := simp) toProd_comp_inr]
theorem toProd_comp_inr : (toProd : M ∗ N →* M × N).comp inr = .inr _ _ := rfl

@[to_additive (attr := simp) toProd_apply_inl]
theorem toProd_apply_inl (x : M) : toProd (inl x : M ∗ N) = (x, 1) := rfl

@[to_additive (attr := simp) toProd_apply_inr]
theorem toProd_apply_inr (x : N) : toProd (inr x : M ∗ N) = (1, x) := rfl

@[to_additive (attr := simp) fst_prod_snd]
theorem fst_prod_snd : (fst : M ∗ N →* M).prod snd = toProd := by ext1 <;> rfl

@[to_additive (attr := simp) prod_mk_fst_snd]
theorem prod_mk_fst_snd (x : M ∗ N) : (fst x, snd x) = toProd x := by
  rw [← fst_prod_snd, MonoidHom.prod_apply]

@[to_additive (attr := simp) fst_comp_toProd]
theorem fst_comp_toProd : (MonoidHom.fst M N).comp toProd = fst := by
  rw [← fst_prod_snd, MonoidHom.fst_comp_prod]

@[to_additive (attr := simp) fst_toProd]
theorem fst_toProd (x : M ∗ N) : (toProd x).1 = fst x := by
  rw [← fst_comp_toProd]; rfl

@[to_additive (attr := simp) snd_comp_toProd]
theorem snd_comp_toProd : (MonoidHom.snd M N).comp toProd = snd := by
  rw [← fst_prod_snd, MonoidHom.snd_comp_prod]

@[to_additive (attr := simp) snd_toProd]
theorem snd_toProd (x : M ∗ N) : (toProd x).2 = snd x := by
  rw [← snd_comp_toProd]; rfl

@[to_additive (attr := simp)]
theorem fst_comp_swap : fst.comp (swap M N) = snd := lift_comp_swap _ _

@[to_additive (attr := simp)]
theorem fst_swap (x : M ∗ N) : fst (swap M N x) = snd x := lift_swap _ _ _

@[to_additive (attr := simp)]
theorem snd_comp_swap : snd.comp (swap M N) = fst := lift_comp_swap _ _

@[to_additive (attr := simp)]
theorem snd_swap (x : M ∗ N) : snd (swap M N x) = fst x := lift_swap _ _ _

@[to_additive (attr := simp)]
theorem lift_inr_inl : lift (inr : M →* N ∗ M) inl = swap M N := hom_ext rfl rfl

@[to_additive (attr := simp)]
theorem lift_inl_inr : lift (inl : M →* M ∗ N) inr = .id _ := hom_ext rfl rfl

@[to_additive]
theorem inl_injective : Injective (inl : M →* M ∗ N) := LeftInverse.injective fst_apply_inl

@[to_additive]
theorem inr_injective : Injective (inr : N →* M ∗ N) := LeftInverse.injective snd_apply_inr

@[to_additive]
theorem fst_surjective : Surjective (fst : M ∗ N →* M) := LeftInverse.surjective fst_apply_inl

@[to_additive]
theorem snd_surjective : Surjective (snd : M ∗ N →* N) := LeftInverse.surjective snd_apply_inr

@[to_additive toProd_surjective]
theorem toProd_surjective : Surjective (toProd : M ∗ N →* M × N) := fun x =>
  ⟨inl x.1 * inr x.2, by rw [map_mul, toProd_apply_inl, toProd_apply_inr, Prod.fst_mul_snd]⟩

end ToProd

section Group

variable {G H : Type*} [Group G] [Group H]

@[to_additive]
theorem mk_of_inv_mul : ∀ x : G ⊕ H, mk (of (x.map Inv.inv Inv.inv)) * mk (of x) = 1
  | Sum.inl _ => map_mul_eq_one inl (inv_mul_cancel _)
  | Sum.inr _ => map_mul_eq_one inr (inv_mul_cancel _)

@[to_additive]
theorem con_inv_mul_cancel (x : FreeMonoid (G ⊕ H)) :
    coprodCon G H (ofList (x.toList.map (Sum.map Inv.inv Inv.inv)).reverse * x) 1 := by
  rw [← mk_eq_mk, map_mul, map_one]
  induction x using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x xs ihx =>
    simp only [toList_of_mul, map_cons, reverse_cons, ofList_append, map_mul, ofList_singleton]
    rwa [mul_assoc, ← mul_assoc (mk (of _)), mk_of_inv_mul, one_mul]

@[to_additive]
instance : Inv (G ∗ H) where
  inv := Quotient.map' (fun w => ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) fun _ _ ↦
    (coprodCon G H).map_of_mul_left_rel_one _ con_inv_mul_cancel

@[to_additive]
theorem inv_def (w : FreeMonoid (G ⊕ H)) :
    (mk w)⁻¹ = mk (ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) :=
  rfl

@[to_additive]
instance : Group (G ∗ H) where
  inv_mul_cancel := mk_surjective.forall.2 fun x => mk_eq_mk.2 (con_inv_mul_cancel x)

@[to_additive (attr := simp)]
theorem closure_range_inl_union_inr :
    Subgroup.closure (range (inl : G →* G ∗ H) ∪ range inr) = ⊤ :=
  Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_range_inl_union_inr

@[to_additive (attr := simp)] theorem range_inl_sup_range_inr :
    MonoidHom.range (inl : G →* G ∗ H) ⊔ MonoidHom.range inr = ⊤ := by
  rw [← closure_range_inl_union_inr, Subgroup.closure_union, ← MonoidHom.coe_range,
    ← MonoidHom.coe_range, Subgroup.closure_eq, Subgroup.closure_eq]

@[to_additive]
theorem codisjoint_range_inl_range_inr :
    Codisjoint (MonoidHom.range (inl : G →* G ∗ H)) (MonoidHom.range inr) :=
  codisjoint_iff.2 range_inl_sup_range_inr

@[to_additive (attr := simp)] theorem range_swap : MonoidHom.range (swap G H) = ⊤ :=
  MonoidHom.range_eq_top.2 swap_surjective

variable {K : Type*} [Group K]

@[to_additive] theorem range_eq (f : G ∗ H →* K) :
    MonoidHom.range f = MonoidHom.range (f.comp inl) ⊔ MonoidHom.range (f.comp inr) := by
  rw [MonoidHom.range_eq_map, ← range_inl_sup_range_inr, Subgroup.map_sup, MonoidHom.map_range,
    MonoidHom.map_range]

@[to_additive (attr := simp)] theorem range_lift (f : G →* K) (g : H →* K) :
    MonoidHom.range (lift f g) = MonoidHom.range f ⊔ MonoidHom.range g := by
  simp [range_eq]

end Group

end Monoid.Coprod

open Monoid Coprod

namespace MulEquiv

section MulOneClass

variable {M N M' N' : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass M']
  [MulOneClass N']

/-- Lift two monoid equivalences `e : M ≃* N` and `e' : M' ≃* N'` to a monoid equivalence
`(M ∗ M') ≃* (N ∗ N')`. -/
@[to_additive (attr := simps! -fullyApplied) /-- Lift two additive monoid
equivalences `e : M ≃+ N` and `e' : M' ≃+ N'` to an additive monoid equivalence
`(AddMonoid.Coprod M M') ≃+ (AddMonoid.Coprod N N')`. -/]
def coprodCongr (e : M ≃* N) (e' : M' ≃* N') : (M ∗ M') ≃* (N ∗ N') :=
  (Coprod.map (e : M →* N) (e' : M' →* N')).toMulEquiv (Coprod.map e.symm e'.symm)
    (by ext <;> simp) (by ext <;> simp)

variable (M N)

/-- A `MulEquiv` version of `Coprod.swap`. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- An `AddEquiv` version of `AddMonoid.Coprod.swap`. -/]
def coprodComm : M ∗ N ≃* N ∗ M :=
  (Coprod.swap _ _).toMulEquiv (Coprod.swap _ _) (Coprod.swap_comp_swap _ _)
    (Coprod.swap_comp_swap _ _)

end MulOneClass

variable (M N P : Type*) [Monoid M] [Monoid N] [Monoid P]

/-- A multiplicative equivalence between `(M ∗ N) ∗ P` and `M ∗ (N ∗ P)`. -/
@[to_additive /-- An additive equivalence between `AddMonoid.Coprod (AddMonoid.Coprod M N) P` and
`AddMonoid.Coprod M (AddMonoid.Coprod N P)`. -/]
def coprodAssoc : (M ∗ N) ∗ P ≃* M ∗ (N ∗ P) :=
  MonoidHom.toMulEquiv
    (Coprod.lift (Coprod.map (.id M) inl) (inr.comp inr))
    (Coprod.lift (inl.comp inl) (Coprod.map inr (.id P)))
    (by ext <;> rfl) (by ext <;> rfl)

variable {M N P}

@[to_additive (attr := simp)]
theorem coprodAssoc_apply_inl_inl (x : M) : coprodAssoc M N P (inl (inl x)) = inl x := rfl

@[to_additive (attr := simp)]
theorem coprodAssoc_apply_inl_inr (x : N) : coprodAssoc M N P (inl (inr x)) = inr (inl x) := rfl

@[to_additive (attr := simp)]
theorem coprodAssoc_apply_inr (x : P) : coprodAssoc M N P (inr x) = inr (inr x) := rfl

@[to_additive (attr := simp)]
theorem coprodAssoc_symm_apply_inl (x : M) : (coprodAssoc M N P).symm (inl x) = inl (inl x) :=
  rfl

@[to_additive (attr := simp)]
theorem coprodAssoc_symm_apply_inr_inl (x : N) :
    (coprodAssoc M N P).symm (inr (inl x)) = inl (inr x) :=
  rfl

@[to_additive (attr := simp)]
theorem coprodAssoc_symm_apply_inr_inr (x : P) :
    (coprodAssoc M N P).symm (inr (inr x)) = inr x :=
  rfl

variable (M)

/-- Isomorphism between `M ∗ PUnit` and `M`. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Isomorphism between `AddMonoid.Coprod M PUnit` and `M`. -/]
def coprodPUnit : M ∗ PUnit ≃* M :=
  MonoidHom.toMulEquiv fst inl (hom_ext rfl <| Subsingleton.elim _ _) fst_comp_inl

/-- Isomorphism between `PUnit ∗ M` and `M`. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Isomorphism between `AddMonoid.Coprod PUnit M` and `M`. -/]
def punitCoprod : PUnit ∗ M ≃* M :=
  MonoidHom.toMulEquiv snd inr (hom_ext (Subsingleton.elim _ _) rfl) snd_comp_inr

end MulEquiv
