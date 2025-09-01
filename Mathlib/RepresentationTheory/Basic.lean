/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * `Representation`
  * `Representation.directSum`
  * `Representation.prod`
  * `Representation.tprod`
  * `Representation.linHom`
  * `Representation.dual`
  * `Representation.free`

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`. We use the abbreviation `Representation` for this hom space.

The theorem `asAlgebraHom_def` constructs a module over the group `k`-algebra of `G` (implemented
as `MonoidAlgebra k G`) corresponding to a representation. If `ρ : Representation k G V`, this
module can be accessed via `ρ.asModule`. Conversely, given a `MonoidAlgebra k G`-module `M`,
`M.ofModule` is the associated representation seen as a homomorphism.
-/

open MonoidAlgebra (lift of)
open LinearMap Module

section

variable (k G V : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A representation of `G` on the `k`-module `V` is a homomorphism `G →* (V →ₗ[k] V)`.
-/
abbrev Representation :=
  G →* V →ₗ[k] V

end

namespace Representation

section trivial

variable (k G V : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- The trivial representation of `G` on a `k`-module V.
-/
def trivial : Representation k G V :=
  1

variable {G V}

@[simp]
theorem trivial_apply (g : G) (v : V) : trivial k G V g v = v :=
  rfl

variable {k}

/-- A predicate for representations that fix every element. -/
class IsTrivial (ρ : Representation k G V) : Prop where
  out : ∀ g, ρ g = LinearMap.id := by aesop

instance : IsTrivial (trivial k G V) where

@[simp]
theorem isTrivial_def (ρ : Representation k G V) [IsTrivial ρ] (g : G) :
    ρ g = LinearMap.id := IsTrivial.out g

theorem isTrivial_apply (ρ : Representation k G V) [IsTrivial ρ] (g : G) (x : V) :
    ρ g x = x := congr($(isTrivial_def ρ g) x)

end trivial

section Group

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

@[simp]
theorem inv_self_apply (g : G) (x : V) :
    ρ g⁻¹ (ρ g x) = x := by
  simp [← Module.End.mul_apply, ← map_mul]

@[simp]
theorem self_inv_apply (g : G) (x : V) :
    ρ g (ρ g⁻¹ x) = x := by
  simp [← Module.End.mul_apply, ← map_mul]

lemma apply_bijective (g : G) :
    Function.Bijective (ρ g) :=
  Equiv.bijective ⟨ρ g, ρ g⁻¹, inv_self_apply ρ g, self_inv_apply ρ g⟩

end Group

section MonoidAlgebra

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/-- A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `MonoidAlgebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def asAlgebraHom : MonoidAlgebra k G →ₐ[k] Module.End k V :=
  (lift k G _) ρ

theorem asAlgebraHom_def : asAlgebraHom ρ = (lift k G _) ρ :=
  rfl

@[simp]
theorem asAlgebraHom_single (g : G) (r : k) :
    asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g := by
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]

theorem asAlgebraHom_single_one (g : G) : asAlgebraHom ρ (MonoidAlgebra.single g 1) = ρ g := by simp

theorem asAlgebraHom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g := by
  simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul]

/-- If `ρ : Representation k G V`, then `ρ.asModule` is a type synonym for `V`,
which we equip with an instance `Module (MonoidAlgebra k G) ρ.asModule`.

You should use `asModuleEquiv : ρ.asModule ≃+ V` to translate terms.
-/
@[nolint unusedArguments]
def asModule (_ : Representation k G V) :=
  V
deriving AddCommMonoid, Module k

instance : Inhabited ρ.asModule where
  default := 0

/-- A `k`-linear representation of `G` on `V` can be thought of as
a module over `MonoidAlgebra k G`.
-/
noncomputable instance : Module (MonoidAlgebra k G) ρ.asModule :=
  Module.compHom V (asAlgebraHom ρ).toRingHom

/-- The additive equivalence from the `Module (MonoidAlgebra k G)` to the original vector space
of the representative.

This is just the identity, but it is helpful for typechecking and keeping track of instances.
-/
def asModuleEquiv : ρ.asModule ≃ₗ[k] V :=
  LinearEquiv.refl _ _

@[simp]
theorem asModuleEquiv_map_smul (r : MonoidAlgebra k G) (x : ρ.asModule) :
    ρ.asModuleEquiv (r • x) = ρ.asAlgebraHom r (ρ.asModuleEquiv x) :=
  rfl

theorem asModuleEquiv_symm_map_smul (r : k) (x : V) :
    ρ.asModuleEquiv.symm (r • x) = algebraMap k (MonoidAlgebra k G) r • ρ.asModuleEquiv.symm x := by
  rw [LinearEquiv.symm_apply_eq]
  simp

@[simp]
theorem asModuleEquiv_symm_map_rho (g : G) (x : V) :
    ρ.asModuleEquiv.symm (ρ g x) = MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm x := by
  rw [LinearEquiv.symm_apply_eq]
  simp

/-- Build a `Representation k G M` from a `[Module (MonoidAlgebra k G) M]`.

This version is not always what we want, as it relies on an existing `[Module k M]`
instance, along with a `[IsScalarTower k (MonoidAlgebra k G) M]` instance.

We remedy this below in `ofModule`
(with the tradeoff that the representation is defined
only on a type synonym of the original module.)
-/
noncomputable def ofModule' (M : Type*) [AddCommMonoid M] [Module k M]
    [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M] : Representation k G M :=
  (MonoidAlgebra.lift k G (M →ₗ[k] M)).symm (Algebra.lsmul k k M)

section

variable (M : Type*) [AddCommMonoid M] [Module (MonoidAlgebra k G) M]

/-- Build a `Representation` from a `[Module (MonoidAlgebra k G) M]`.

Note that the representation is built on `restrictScalars k (MonoidAlgebra k G) M`,
rather than on `M` itself.
-/
noncomputable def ofModule : Representation k G (RestrictScalars k (MonoidAlgebra k G) M) :=
  (MonoidAlgebra.lift k G
        (RestrictScalars k (MonoidAlgebra k G) M →ₗ[k]
          RestrictScalars k (MonoidAlgebra k G) M)).symm
    (RestrictScalars.lsmul k (MonoidAlgebra k G) M)

/-!
## `ofModule` and `asModule` are inverses.

This requires a little care in both directions:
this is a categorical equivalence, not an isomorphism.

See `Rep.equivalenceModuleMonoidAlgebra` for the full statement.

Starting with `ρ : Representation k G V`, converting to a module and back again
we have a `Representation k G (restrictScalars k (MonoidAlgebra k G) ρ.asModule)`.
To compare these, we use the composition of `restrictScalarsAddEquiv` and `ρ.asModuleEquiv`.

Similarly, starting with `Module (MonoidAlgebra k G) M`,
after we convert to a representation and back to a module,
we have `Module (MonoidAlgebra k G) (restrictScalars k (MonoidAlgebra k G) M)`.
-/


@[simp]
theorem ofModule_asAlgebraHom_apply_apply (r : MonoidAlgebra k G)
    (m : RestrictScalars k (MonoidAlgebra k G) M) :
    ((ofModule M).asAlgebraHom r) m =
      (RestrictScalars.addEquiv _ _ _).symm (r • RestrictScalars.addEquiv _ _ _ m) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single, Representation.ofModule,
      RestrictScalars.lsmul_apply_apply]
  · intro f g fw gw
    simp only [fw, gw, map_add, add_smul, LinearMap.add_apply]
  · intro r f w
    simp only [w, map_smul, LinearMap.smul_apply, RestrictScalars.addEquiv_symm_map_smul_smul]

@[simp]
theorem ofModule_asModule_act (g : G) (x : RestrictScalars k (MonoidAlgebra k G) ρ.asModule) :
    ofModule (k := k) (G := G) ρ.asModule g x = -- Porting note: more help with implicit
      (RestrictScalars.addEquiv _ _ _).symm
        (ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv (RestrictScalars.addEquiv _ _ _ x)))) := by
  apply_fun RestrictScalars.addEquiv _ _ ρ.asModule using
    (RestrictScalars.addEquiv _ _ ρ.asModule).injective
  dsimp [ofModule, RestrictScalars.lsmul_apply_apply]
  simp

theorem smul_ofModule_asModule (r : MonoidAlgebra k G) (m : (ofModule M).asModule) :
    (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (r • m)) =
      r • (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (G := G) m) := by
  dsimp
  simp only [AddEquiv.apply_symm_apply, ofModule_asAlgebraHom_apply_apply]

end

@[simp]
lemma single_smul (t : k) (g : G) (v : ρ.asModule) :
    MonoidAlgebra.single (g : G) t • v = t • ρ g (ρ.asModuleEquiv v) := by
  rw [← LinearMap.smul_apply, ← asAlgebraHom_single, ← asModuleEquiv_map_smul]
  rfl

instance : IsScalarTower k (MonoidAlgebra k G) ρ.asModule where
  smul_assoc t x v := by
    revert t
    apply x.induction_on
    · simp
    · intro y z hy hz
      simp [add_smul, hy, hz]
    · intro s y hy t
      rw [← smul_assoc, smul_eq_mul, hy (t * s), ← smul_eq_mul, smul_assoc]
      aesop

end MonoidAlgebra

section Norm

variable {k G V : Type*} [CommSemiring k] [Group G] [Fintype G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/-- Given a representation `(V, ρ)` of a finite group `G`, `norm ρ` is the linear map `V →ₗ[k] V`
defined by `x ↦ ∑ ρ g x` for `g` in `G`. -/
def norm : Module.End k V := ∑ g : G, ρ g

@[simp]
lemma norm_comp_self (g : G) : norm ρ ∘ₗ ρ g = norm ρ := by
  ext
  simpa [norm] using Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ <| by simp

@[simp]
lemma norm_self_apply (g : G) (x : V) : norm ρ (ρ g x) = norm ρ x :=
  LinearMap.ext_iff.1 (norm_comp_self _ _) x

@[simp]
lemma self_comp_norm (g : G) : ρ g ∘ₗ norm ρ = norm ρ := by
  ext
  simpa [norm] using Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ <| by simp

@[simp]
lemma self_norm_apply (g : G) (x : V) : ρ g (norm ρ x) = norm ρ x :=
  LinearMap.ext_iff.1 (self_comp_norm _ _) x

end Norm

section Subrepresentation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
@[simps]
def subrepresentation (W : Submodule k V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    Representation k G W where
  toFun g := (ρ g).restrict <| le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end Subrepresentation

section Quotient

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
@[simps]
def quotient (W : Submodule k V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    Representation k G (V ⧸ W) where
  toFun g := Submodule.mapQ _ _ (ρ g) <| le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end Quotient

section OfQuotient

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G)

lemma apply_eq_of_coe_eq [IsTrivial (ρ.comp S.subtype)] (g h : G) (hgh : (g : G ⧸ S) = h) :
    ρ g = ρ h := by
  ext x
  apply (ρ.apply_bijective g⁻¹).1
  simpa [← Module.End.mul_apply, ← map_mul, -isTrivial_def] using
    (congr($(isTrivial_def (ρ.comp S.subtype) ⟨g⁻¹ * h, QuotientGroup.eq.1 hgh⟩) x)).symm

variable [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
def ofQuotient [IsTrivial (ρ.comp S.subtype)] :
    Representation k (G ⧸ S) V :=
  (QuotientGroup.con S).lift ρ <| by
    rintro x y ⟨⟨z, hz⟩, rfl⟩
    ext w
    change ρ (_ * z.unop) _ = _
    exact congr($(apply_eq_of_coe_eq ρ S _ _ (by simp_all)) w)

@[simp]
lemma ofQuotient_coe_apply [IsTrivial (ρ.comp S.subtype)] (g : G) (x : V) :
    ofQuotient ρ S (g : G ⧸ S) x = ρ g x :=
  rfl

end OfQuotient

section AddCommGroup

variable {k G V : Type*} [CommRing k] [Monoid G] [I : AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

instance : AddCommGroup ρ.asModule :=
  I

/- Given a representation `(V, ρ)` of a monoid `G`, this says
`(ρ(g) - Id)(x + ρ(g)(x) + ... + ρ(gⁿ)(x)) = ρ(gⁿ⁺¹)(x) - x` for all `n : ℕ, g : G` and `x : V`. -/
lemma apply_sub_id_partialSum_eq (n : ℕ) (g : G) (x : V) :
    (ρ g - LinearMap.id (R := k) (M := V)) ((Fin.last _).partialSum
      (fun (j : Fin (n + 1)) => ρ (g ^ (j : ℕ)) x)) = ρ (g ^ (n + 1)) x - x := by
  induction n with
  | zero => simp [Fin.partialSum]
  | succ n h =>
    have : Fin.init (fun (j : Fin (n + 2)) => ρ (g ^ (j : ℕ)) x) =
      fun (j : Fin (n + 1)) => ρ (g ^ (j : ℕ)) x := by ext; simp [Fin.init]
    rw [← Fin.succ_eq_last_succ.2 rfl, Fin.partialSum_succ, ← Fin.partialSum_init, map_add,
      this, h]
    simp [pow_succ']

end AddCommGroup

section MulAction

variable (k : Type*) [CommSemiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
noncomputable def ofMulAction : Representation k G (H →₀ k) where
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    ext x y
    simp
  map_mul' x y := by
    ext z w
    simp [mul_smul]

/-- The natural `k`-linear `G`-representation on `k[G]` induced by left multiplication in `G`. -/
noncomputable abbrev leftRegular := ofMulAction k G G

/-- The natural `k`-linear `G`-representation on `k[Gⁿ]` induced by left multiplication in `G`. -/
noncomputable abbrev diagonal (n : ℕ) := ofMulAction k G (Fin n → G)

variable {k G H}

theorem ofMulAction_def (g : G) : ofMulAction k G H g = Finsupp.lmapDomain k k (g • ·) :=
  rfl

@[simp]
theorem ofMulAction_single (g : G) (x : H) (r : k) :
    ofMulAction k G H g (Finsupp.single x r) = Finsupp.single (g • x) r :=
  Finsupp.mapDomain_single

end MulAction
section DistribMulAction

variable (k G A : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into a
`k`-linear `G`-representation on `A`. -/
def ofDistribMulAction : Representation k G A where
  toFun := fun m =>
    { DistribMulAction.toAddMonoidEnd G A m with
      map_smul' := smul_comm _ }
  map_one' := by ext; exact one_smul _ _
  map_mul' := by intros; ext; exact mul_smul _ _ _

variable {k G A}

@[simp] theorem ofDistribMulAction_apply_apply (g : G) (a : A) :
    ofDistribMulAction k G A g a = g • a := rfl

@[simp]
theorem norm_ofDistribMulAction_eq {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G A] [SMulCommClass G k A] (x : A) :
    (ofDistribMulAction k G A).norm x = ∑ g : G, g • x := by
  simp [norm]

end DistribMulAction
section MulDistribMulAction
variable (M G : Type*) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/-- Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`. -/
def ofMulDistribMulAction : Representation ℤ M (Additive G) :=
  (addMonoidEndRingEquivInt (Additive G) : AddMonoid.End (Additive G) →* _).comp
    ((monoidEndToAdditive G : _ →* _).comp (MulDistribMulAction.toMonoidEnd M G))

@[simp] theorem ofMulDistribMulAction_apply_apply (g : M) (a : Additive G) :
    ofMulDistribMulAction M G g a = Additive.ofMul (g • a.toMul) := rfl

@[simp]
theorem norm_ofMulDistribMulAction_eq {G M : Type} [Group G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M] (x : Additive M) :
    Additive.toMul ((ofMulDistribMulAction G M).norm x) =
      ∏ g : G, g • Additive.toMul x := by
  simp [norm]

end MulDistribMulAction
section Group

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

@[simp]
theorem ofMulAction_apply {H : Type*} [MulAction G H] (g : G) (f : H →₀ k) (h : H) :
    ofMulAction k G H g f h = f (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  let h' := g⁻¹ • h
  change ofMulAction k G H g f (g • h') = f h'
  have hg : Function.Injective (g • · : H → H) := by
    intro h₁ h₂
    simp
  simp only [ofMulAction_def, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply, hg]

-- Porting note: did not need this in ML3; noncomputable because IR check complains
noncomputable instance :
    HMul (MonoidAlgebra k G) ((ofMulAction k G G).asModule) (MonoidAlgebra k G) :=
  inferInstanceAs <| HMul (MonoidAlgebra k G) (MonoidAlgebra k G) (MonoidAlgebra k G)

theorem ofMulAction_self_smul_eq_mul (x : MonoidAlgebra k G) (y : (ofMulAction k G G).asModule) :
    x • y = (x * y : MonoidAlgebra k G) := -- by
  -- Porting note: trouble figuring out the motive
  x.induction_on (p := fun z => z • y = z * y)
    (fun g => by
      change asAlgebraHom (ofMulAction k G G) _ _ = _
      ext
      -- Porting note: single_mul_apply not firing in simp without parentheses
      simp [(MonoidAlgebra.single_mul_apply)]
    )
    (fun x y hx hy => by simp only [hx, hy, add_mul, add_smul]) fun r x hx => by
    change asAlgebraHom (ofMulAction k G G) _ _ = _  -- Porting note: was simpa [← hx]
    simp only [map_smul, smul_apply, Algebra.smul_mul_assoc]
    rw [← hx]
    rfl

/-- If we equip `k[G]` with the `k`-linear `G`-representation induced by the left regular action of
`G` on itself, the resulting object is isomorphic as a `k[G]`-module to `k[G]` with its natural
`k[G]`-module structure. -/
@[simps]
noncomputable def ofMulActionSelfAsModuleEquiv :
    (ofMulAction k G G).asModule ≃ₗ[MonoidAlgebra k G] MonoidAlgebra k G :=
  { (asModuleEquiv _).toAddEquiv with map_smul' := ofMulAction_self_smul_eq_mul }

/-- When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def asGroupHom : G →* Units (V →ₗ[k] V) :=
  MonoidHom.toHomUnits ρ

theorem asGroupHom_apply (g : G) : ↑(asGroupHom ρ g) = ρ g := by
  simp only [asGroupHom, MonoidHom.coe_toHomUnits]

section Finite

variable [Fintype G]

open Finsupp

lemma leftRegular_norm_apply :
    (leftRegular k G).norm =
      (LinearMap.lsmul k _).flip ((leftRegular k G).norm (single 1 1)) ∘ₗ
      linearCombination _ (fun _ => 1) := by
  ext i : 2
  simpa [Representation.norm] using Finset.sum_bijective _
    (Group.mulRight_bijective i) (by simp_all) (by simp_all)

lemma leftRegular_norm_eq_zero_iff (x : G →₀ k) :
    (leftRegular k G).norm x = 0 ↔ x.linearCombination k (fun _ => (1 : k)) = 0 := by
  rw [leftRegular_norm_apply]
  constructor
  · intro h
    simpa [norm, Representation.norm] using Finsupp.ext_iff.1 h 1
  · intro h
    ext
    simp_all

lemma ker_leftRegular_norm_eq :
    LinearMap.ker (leftRegular k G).norm =
      LinearMap.ker (linearCombination k (fun _ => (1 : k))) := by
  ext
  exact leftRegular_norm_eq_zero_iff _

end Finite
section Cyclic

lemma apply_eq_of_leftRegular_eq_of_generator (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (x : G →₀ k) (hx : leftRegular k G g x = x) (γ : G) :
    x γ = x g := by
  rcases hg γ with ⟨i, rfl⟩
  induction i with
  | zero =>
    simpa using (Finsupp.ext_iff.1 hx g)
  | succ n h =>
    simpa [← h, zpow_natCast, zpow_add_one, pow_mul_comm', pow_succ'] using
      (Finsupp.ext_iff.1 hx (g ^ (n + 1))).symm
  | pred n h =>
    simpa [zpow_sub, ← h, ← mul_inv_rev, ← pow_mul_comm']
      using Finsupp.ext_iff.1 hx (g ^ (-n : ℤ))

end Cyclic
end Group

section DirectSum

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable {ι : Type*} {V : ι → Type*}
variable [(i : ι) → AddCommMonoid (V i)] [(i : ι) → Module k (V i)]
variable (ρ : (i : ι) → Representation k G (V i))

open DirectSum

/-- Given representations of `G` on a family `V i` indexed by `i`, there is a
natural representation of `G` on their direct sum `⨁ i, V i`.
-/
@[simps]
noncomputable def directSum : Representation k G (⨁ i, V i) where
  toFun g := DirectSum.lmap (fun _ => ρ _ g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

end DirectSum

section Prod

variable {k G V W : Type*} [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρV : Representation k G V) (ρW : Representation k G W)

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
product `V × W`.
-/
@[simps!]
noncomputable def prod : Representation k G (V × W) where
  toFun g := (ρV g).prodMap (ρW g)
  map_one' := by simp
  map_mul' g h := by simp [prodMap_mul]

end Prod

section TensorProduct

variable {k G V W : Type*} [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρV : Representation k G V) (ρW : Representation k G W)

open TensorProduct

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
tensor product `V ⊗[k] W`.
-/
noncomputable def tprod : Representation k G (V ⊗[k] W) where
  toFun g := TensorProduct.map (ρV g) (ρW g)
  map_one' := by simp only [map_one, TensorProduct.map_one]
  map_mul' g h := by simp only [map_mul, TensorProduct.map_mul]

local notation ρV " ⊗ " ρW => tprod ρV ρW

@[simp]
theorem tprod_apply (g : G) : (ρV ⊗ ρW) g = TensorProduct.map (ρV g) (ρW g) :=
  rfl

theorem smul_tprod_one_asModule (r : MonoidAlgebra k G) (x : V) (y : W) :
    -- Porting note: required to since Lean 4 doesn't unfold asModule
    let x' : ρV.asModule := x
    let z : (ρV.tprod 1).asModule := x ⊗ₜ y
    r • z = (r • x') ⊗ₜ y := by
  change asAlgebraHom (ρV ⊗ 1) _ _ = asAlgebraHom ρV _ _ ⊗ₜ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorProduct.sum_tmul]
  rfl

theorem smul_one_tprod_asModule (r : MonoidAlgebra k G) (x : V) (y : W) :
    -- Porting note: required to since Lean 4 doesn't unfold asModule
    let y' : ρW.asModule := y
    let z : (1 ⊗ ρW).asModule := x ⊗ₜ y
    r • z = x ⊗ₜ (r • y') := by
  change asAlgebraHom (1 ⊗ ρW) _ _ = _ ⊗ₜ asAlgebraHom ρW _ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

end TensorProduct

section LinearHom

variable {k G V W : Type*} [CommSemiring k] [Group G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρV : Representation k G V) (ρW : Representation k G W)

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
def linHom : Representation k G (V →ₗ[k] W) where
  toFun g :=
    { toFun := fun f => ρW g ∘ₗ f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp_rw [add_comp, comp_add]
      map_smul' := fun r f => by simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
  map_one' := ext fun x => by simp [Module.End.one_eq_id]
  map_mul' g h := ext fun x => by simp [Module.End.mul_eq_comp, comp_assoc]

@[simp]
theorem linHom_apply (g : G) (f : V →ₗ[k] W) : (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹ :=
  rfl

/-- The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f = f ∘ₗ (ρ g⁻¹)`,
where `f : Module.Dual k V`.
-/
def dual : Representation k G (Module.Dual k V) where
  toFun g :=
    { toFun := fun f => f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp only [add_comp]
      map_smul' := fun r f => by
        ext
        simp only [coe_comp, Function.comp_apply, smul_apply, RingHom.id_apply] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]
theorem dual_apply (g : G) : (dual ρV) g = Module.Dual.transpose (R := k) (ρV g⁻¹) :=
  rfl

/-- Given $k$-modules $V, W$, there is a homomorphism $φ : V^* ⊗ W → Hom_k(V, W)$
(implemented by `dualTensorHom` in `Mathlib/LinearAlgebra/Contraction.lean`).
Given representations of $G$ on $V$ and $W$,there are representations of $G$ on $V^* ⊗ W$ and on
$Hom_k(V, W)$.
This lemma says that $φ$ is $G$-linear.
-/
theorem dualTensorHom_comm (g : G) :
    dualTensorHom k V W ∘ₗ TensorProduct.map (ρV.dual g) (ρW g) =
      (linHom ρV ρW) g ∘ₗ dualTensorHom k V W := by
  ext; simp [Module.Dual.transpose_apply]

end LinearHom

section

variable {k G : Type*} [CommSemiring k] [Monoid G] {α A B : Type*}
  [AddCommMonoid A] [Module k A] (ρ : Representation k G A)
  [AddCommMonoid B] [Module k B] (τ : Representation k G B)

open Finsupp

/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
@[simps -isSimp]
noncomputable def finsupp (α : Type*) :
    Representation k G (α →₀ A) where
  toFun g := lsum k fun i => (lsingle i).comp (ρ g)
  map_one' := lhom_ext (fun _ _ => by simp)
  map_mul' _ _ := lhom_ext (fun _ _ => by simp)

@[simp]
lemma finsupp_single (g : G) (x : α) (a : A) :
    ρ.finsupp α g (single x a) = single x (ρ g a) := by
  simp [finsupp_apply]

/-- The representation on `α →₀ k[G]` defined pointwise by the left regular representation. -/
noncomputable abbrev free (k G : Type*) [CommSemiring k] [Monoid G] (α : Type*) :
    Representation k G (α →₀ G →₀ k) :=
  finsupp (leftRegular k G) α

noncomputable instance (k G : Type*) [CommRing k] [Monoid G] (α : Type*) :
    AddCommGroup (free k G α).asModule :=
  Finsupp.instAddCommGroup

lemma free_single_single (g h : G) (i : α) (r : k) :
    free k G α g (single i (single h r)) = single i (single (g * h) r) := by
  simp

variable (k G) (α : Type*)

/-- The free `k[G]`-module on a type `α` is isomorphic to the representation `free k G α`. -/
noncomputable def finsuppLEquivFreeAsModule :
    (α →₀ MonoidAlgebra k G) ≃ₗ[MonoidAlgebra k G] (free k G α).asModule :=
  { AddEquiv.refl _ with
    map_smul' _ x := by
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
        AddEquiv.refl_apply, RingHom.id_apply]
      induction x using Finsupp.induction with
      | zero => simp only [smul_zero]
      | single_add _ _ _ _ _ h =>
        rw [smul_add, h]
        change _ + asAlgebraHom _ _ _ = asAlgebraHom _ _ _
        simp only [map_add, smul_single, smul_eq_mul, MonoidAlgebra.mul_def,
          asAlgebraHom_def, MonoidAlgebra.lift_apply]
        simp [free, MonoidAlgebra, asModule, ofMulAction_def, mapDomain, smul_sum, single_sum] }

/-- `α` gives a `k[G]`-basis of the representation `free k G α`. -/
noncomputable def freeAsModuleBasis :
    Basis α (MonoidAlgebra k G) (free k G α).asModule where
  repr := (finsuppLEquivFreeAsModule k G α).symm

theorem free_asModule_free :
    Module.Free (MonoidAlgebra k G) (free k G α).asModule :=
  Module.Free.of_basis (freeAsModuleBasis k G α)

end
end Representation
