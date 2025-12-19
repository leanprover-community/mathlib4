/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Lie.Cochain

/-!
# Extensions of Lie algebras
This file defines extensions of Lie algebras, given by short exact sequences of Lie algebra
homomorphisms. They are implemented in two ways: `IsExtension` is a `Prop`-valued class taking two
homomorphisms as parameters, and `Extension` is a structure that includes the middle Lie algebra.

Because our sign convention for differentials is opposite that of Chevalley-Eilenberg, there is a
change of signs in the "action" part of the Lie bracket.

## Main definitions
* `LieAlgebra.IsExtension`: A `Prop`-valued class characterizing an extension of Lie algebras.
* `LieAlgebra.Extension`: A bundled structure giving an extension of Lie algebras.
* `LieAlgebra.IsExtension.extension`: A function that builds the bundled structure from the class.
* `LieAlgebra.ofTwoCocycle`: The Lie algebra built from a direct product, but whose bracket product
  is sheared by a 2-cocycle.
* `LieAlgebra.Extension.ofTwoCocycle`: The Lie algebra extension constructed from a 2-cocycle.
* `LieAlgebra.Extension.ringModuleOf`: Given an extension whose kernel is abelian, we obtain a Lie
  action of the target on the kernel.
* `LieAlgebra.Extension.twoCocycle`: The 2-cocycle attached to an extension with a linear section.

## TODO
* `IsCentral` - central extensions
* `Equiv` - equivalence of extensions
* The 2-coboundary from two linear splittings of an extension.

## References
* [Chevalley, Eilenberg, *Cohomology Theory of Lie Groups and Lie
  Algebras*](chevalley_eilenberg_1948)
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

-/

@[expose] public section

namespace LieAlgebra

variable {R N L M : Type*}

section IsExtension

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/-- A sequence of two Lie algebra homomorphisms is an extension if it is short exact. -/
class IsExtension (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker

lemma _root_.LieHom.range_eq_ker_iff (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) :
    i.range = p.ker ↔ Function.Exact i p :=
  ⟨fun h x ↦ by simp [← LieHom.coe_range, h], fun h ↦ (p.ker.toLieSubalgebra.ext i.range h).symm⟩

/-- The equivalence from the kernel of the projection. -/
def IsExtension.kerEquivRange (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) [IsExtension i p] :
    p.ker ≃ₗ[R] i.range :=
  .ofEq (R := R) (M := L) p.ker i.range <| by simp [exact (i := i) (p := p)]

variable (R N M) in
/-- The type of all Lie extensions of `M` by `N`.  That is, short exact sequences of `R`-Lie algebra
homomorphisms `0 → N → L → M → 0` where `R`, `M`, and `N` are fixed. -/
structure Extension where
  /-- The middle object in the sequence. -/
  L : Type*
  /-- `L` is a Lie ring. -/
  instLieRing : LieRing L
  /-- `L` is a Lie algebra over `R`. -/
  instLieAlgebra : LieAlgebra R L
  /-- The inclusion homomorphism `N →ₗ⁅R⁆ L` -/
  incl : N →ₗ⁅R⁆ L
  /-- The projection homomorphism `L →ₗ⁅R⁆ M` -/
  proj : L →ₗ⁅R⁆ M
  IsExtension : IsExtension incl proj

instance (E : Extension R M N) : LieRing E.L := E.instLieRing
instance (E : Extension R M N) : LieAlgebra R E.L := E.instLieAlgebra

/-- The bundled `LieAlgebra.Extension` corresponding to `LieAlgebra.IsExtension` -/
@[simps] def IsExtension.extension {i : N →ₗ⁅R⁆ L} {p : L →ₗ⁅R⁆ M} (h : IsExtension i p) :
    Extension R N M :=
  ⟨L, _, _, i, p, h⟩

/-- A surjective Lie algebra homomorphism yields an extension. -/
lemma isExtension_of_surjective (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
    IsExtension f.ker.incl f where
  ker_eq_bot := LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

end IsExtension

namespace Extension

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

lemma incl_apply_mem_ker (E : Extension R M L) (x : M) :
    E.incl x ∈ E.proj.ker :=
  Function.Exact.apply_apply_eq_zero ((E.incl.range_eq_ker_iff E.proj).mp E.IsExtension.exact) x

@[simp] lemma proj_incl (E : Extension R M L) (x : M) :
    E.proj (E.incl x) = 0 :=
  LieHom.mem_ker.mp (incl_apply_mem_ker E x)

lemma incl_injective (E : Extension R M L) :
    Function.Injective E.incl :=
  (LieHom.ker_eq_bot E.incl).mp E.IsExtension.ker_eq_bot

lemma proj_surjective (E : Extension R M L) :
    Function.Surjective E.proj :=
  (LieHom.range_eq_top E.proj).mp E.IsExtension.range_eq_top

end Extension

section Algebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]

open LieModule.Cohomology

/-- A one-field structure giving a type synonym for a direct product. We use this to describe an
alternative Lie algebra structure on the product, where the bracket is shifted by a 2-cocycle. -/
structure ofTwoCocycle {R L M} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
    [Module R M] [LieRingModule L M] [LieModule R L M]
    (c : twoCocycle R L M) where
  /-- The underlying type. -/
  carrier : L × M

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (c : twoCocycle R L M)

/-- An equivalence between the direct product and the corresponding one-field structure. This is
used to transfer the additive and scalar-multiple structure on the direct product to the type
synonym. -/
def ofProd : L × M ≃ ofTwoCocycle c where
  toFun a := ⟨a⟩
  invFun a := a.carrier

-- transport instances along the equivalence
instance : AddCommGroup (ofTwoCocycle c) := (ofProd c).symm.addCommGroup
instance : Module R (ofTwoCocycle c) := (ofProd c).symm.module R

@[simp] lemma of_zero : ofProd c (0 : L × M) = 0 := rfl
@[simp] lemma of_add (x y : L × M) : ofProd c (x + y) = ofProd c x + ofProd c y := rfl
@[simp] lemma of_smul (r : R) (x : L × M) : (ofProd c) (r • x) = r • ofProd c x := rfl

@[simp] lemma of_symm_zero : (ofProd c).symm (0 : ofTwoCocycle c) = 0 := rfl
@[simp] lemma of_symm_add (x y : ofTwoCocycle c) :
    (ofProd c).symm (x + y) = (ofProd c).symm x + (ofProd c).symm y := rfl
@[simp] lemma of_symm_smul (r : R) (x : ofTwoCocycle c) :
    (ofProd c).symm (r • x) = r • (ofProd c).symm x := rfl

@[simp] lemma of_nsmul (n : ℕ) (x : L × M) : (ofProd c) (n • x) = n • (ofProd c) x := rfl
@[simp] lemma of_symm_nsmul (n : ℕ) (x : ofTwoCocycle c) :
    (ofProd c).symm (n • x) = n • (ofProd c).symm x := rfl

instance : LieRing (ofTwoCocycle c) where
  bracket x y :=
    letI x₁ := ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ofProd c (⁅x₁, y₁⁆, (c : L →ₗ[R] L →ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆)
  add_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [of_symm_add, Prod.fst_add, add_lie, twoCochain_val_apply, map_add,
      LinearMap.add_apply, Prod.snd_add, lie_add, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    abel
  lie_add x y z := by
    rw [← of_add]
    exact Equiv.congr_arg (by simp; abel)
  lie_self x := by
    rw [← of_zero, c.1.2]
    exact Equiv.congr_arg (by simp)
  leibniz_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [twoCochain_val_apply, Equiv.symm_apply_apply, lie_lie, Prod.mk_add_mk,
      sub_add_cancel, Prod.mk.injEq, true_and, lie_add, lie_sub]
    have hc := c.2
    rw [mem_twoCocycle_iff] at hc
    have := d₂₃_apply R L M c ((ofProd c).symm x).1 ((ofProd c).symm y).1 ((ofProd c).symm z).1
    simp only [hc, LinearMap.zero_apply] at this
    rw [← twoCochain_skew _ _ ⁅((ofProd c).symm x).1, ((ofProd c).symm z).1⁆,
      ← twoCochain_skew _ _ ⁅((ofProd c).symm y).1, ((ofProd c).symm z).1⁆, eq_sub_iff_add_eq,
      zero_add, neg_eq_iff_eq_neg] at this
    rw [this]
    abel

lemma bracket_ofTwoCocycle {c : twoCocycle R L M} (x y : ofTwoCocycle c) :
    letI x₁ := ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ⁅x, y⁆ = ofProd c (⁅x₁, y₁⁆, (c : L →ₗ[R] L →ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆) :=
  rfl

instance : LieAlgebra R (ofTwoCocycle c) where
  lie_smul r x y := by
    simp only [bracket_ofTwoCocycle]
    exact Equiv.congr_arg (by simp [← smul_add, smul_sub])

end Algebra

namespace Extension

open LieModule.Cohomology

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

section TwoCocycle

variable [IsLieAbelian M] [LieRingModule L M] [LieModule R L M] (c : twoCocycle R L M)

/-- The extension of Lie algebras defined by a 2-cocycle. -/
def ofTwoCocycle : Extension R M L where
  L := LieAlgebra.ofTwoCocycle c
  instLieRing := inferInstance
  instLieAlgebra := inferInstance
  incl :=
    { toFun x := ofProd c (0, x)
      map_add' _ _ := by simp [← of_add]
      map_smul' _ _ := by simp [← of_smul]
      map_lie' {_ _} := by simp [bracket_ofTwoCocycle] }
  proj :=
    { toFun x := ((ofProd c).symm x).1
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      map_lie' {_ _} := by simp [bracket_ofTwoCocycle] }
  IsExtension :=
    { ker_eq_bot := by
        rw [LieHom.ker_eq_bot]
        intro x y
        simp
      range_eq_top := by
        rw [LieHom.range_eq_top]
        intro x
        use (ofProd c (x, 0))
        simp
      exact := by
        ext x
        constructor
        · intro hx
          obtain ⟨n, h⟩ := hx
          rw [← h]
          rfl
        · intro hx
          have : ((ofProd c).symm x).1 = 0 := hx
          simp only [LieHom.mem_range, LieHom.coe_mk]
          use ((ofProd c).symm x).2
          nth_rw 2 [← Equiv.apply_symm_apply (ofProd c) x]
          rw [← this] }

/-- The Lie algebra isomorphism given by the type synonym. -/
def ofAlg : LieAlgebra.ofTwoCocycle c ≃ₗ⁅R⁆ (ofTwoCocycle c).L := LieEquiv.refl

lemma bracket (x y : (ofTwoCocycle c).L) :
    ⁅x, y⁆ = ofAlg c ⁅(ofAlg c).symm x, (ofAlg c).symm y⁆ :=
  rfl

@[simp]
lemma ofTwoCocycle_incl_apply (x : M) : (ofTwoCocycle c).incl x = ⟨(0, x)⟩ :=
  rfl

@[simp]
lemma ofTwoCocycle_proj_apply (x : (ofTwoCocycle c).L) : (ofTwoCocycle c).proj x = x.carrier.1 :=
  rfl

end TwoCocycle

lemma lie_incl_mem_ker {E : Extension R M L} (x : E.L) (y : M) :
    ⁅x, E.incl y⁆ ∈ E.proj.ker := by
  rw [LieHom.mem_ker, LieHom.map_lie, proj_incl, lie_zero]

/-- The Lie algebra isomorphism from the kernel of an extension to the kernel of the projection. -/
noncomputable def toKer (E : Extension R M L) :
    M ≃ₗ⁅R⁆ E.proj.ker where
  toFun m := ⟨E.incl m, E.incl_apply_mem_ker m⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' {x y} := by ext; simp [← LieHom.map_lie]
  invFun := (Equiv.ofInjective E.incl E.incl_injective).symm ∘ E.IsExtension.kerEquivRange
  left_inv _ := by
    simp [IsExtension.kerEquivRange, Equiv.symm_apply_eq]
    rfl
  right_inv x := by simpa [Subtype.ext_iff] using Equiv.apply_ofInjective_symm E.incl_injective _

@[simp] lemma lie_toKer_apply (E : Extension R M L) (x : M) (y : E.L) :
    ⁅y, (E.toKer x : E.L)⁆ = ⁅y, E.incl x⁆ := by
  rfl

instance [IsLieAbelian M] (E : Extension R M L) : IsLieAbelian E.proj.ker :=
  (lie_abelian_iff_equiv_lie_abelian E.toKer.symm).mpr inferInstance

/-- Given an extension of `L` by `M` whose kernel `M` is abelian, the kernel `M` gets an `L`-module
structure. We do not make this an instance, because we may have to work with more than one
extension. -/
@[simps]
noncomputable def ringModuleOf [IsLieAbelian M] (E : Extension R M L) : LieRingModule L M where
  bracket x y := E.toKer.symm ⁅E.proj_surjective.hasRightInverse.choose x, E.toKer y⁆
  add_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    rw [← map_add, ← add_lie, eq_comm, EquivLike.apply_eq_iff_eq, ← sub_eq_zero, ← sub_lie]
    exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
  lie_add x m n := by simp [← map_add, ← lie_add]
  leibniz_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    have aux (z : E.proj.ker) : ⁅⁅h.choose x, h.choose y⁆, z⁆ = ⁅h.choose ⁅x, y⁆, z⁆ := by
      rw [← sub_eq_zero, ← sub_lie]
      exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ z
    rw [← map_add, EquivLike.apply_eq_iff_eq, LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply,
      leibniz_lie, aux]

/-- Given an extension of `L` by `M` whose kernel `M` is abelian, the kernel `M` gets an `R`-linear
`L`-module structure. We do not make this an instance, because we may have to work with more than
one extension. -/
lemma lieModuleOf [IsLieAbelian M] (E : Extension R M L) :
    letI := E.ringModuleOf
    LieModule R L M := by
  letI := E.ringModuleOf
  set h := E.proj_surjective.hasRightInverse
  exact
    { smul_lie r x m := by
        rw [ringModuleOf_bracket, ringModuleOf_bracket, ← map_smul, ← smul_lie,
          EquivLike.apply_eq_iff_eq, ← sub_eq_zero, ← sub_lie]
        exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
      lie_smul r x m := by simp }

lemma toKer_bracket [IsLieAbelian M] (E : Extension R M L) (x : E.proj.ker) (y : L) :
    letI := E.ringModuleOf
    E.toKer ⁅y, E.toKer.symm x⁆ = ⁅E.proj_surjective.hasRightInverse.choose y, x⁆ := by
  simp

lemma lie_apply_proj_of_leftInverse_eq [IsLieAbelian M] (E : Extension R M L) {s : L →ₗ[R] E.L}
    (hs : Function.LeftInverse E.proj s) (x : E.L) (y : E.proj.ker) :
    ⁅s (E.proj x), y⁆ = ⁅x, y⁆ := by
  rw [← sub_eq_zero, ← sub_lie]
  exact trivial_lie_zero E.proj.ker E.proj.ker ⟨_, (by simp [hs.eq])⟩ y

set_option backward.privateInPublic true in
/-- A preparatory function for making a 2-cocycle from a linear splitting of an extension. -/
private abbrev twoCocycleAux (E : Extension R M L) {s : L →ₗ[R] E.L}
    (hs : Function.LeftInverse E.proj s) :
    L →ₗ[R] L →ₗ[R] E.proj.ker where
  toFun x :=
    { toFun y := ⟨⁅s x, s y⁆ - s ⁅x, y⁆, by simp [hs.eq]⟩
      map_add' _ _ := by simp; abel
      map_smul' _ _ := by simp [smul_sub] }
  map_add' x y := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The 2-cocycle attached to an extension with a linear section. -/
@[simps]
noncomputable def twoCocycleOf [IsLieAbelian M] (E : Extension R M L) {s : L →ₗ[R] E.L}
    (hs : Function.LeftInverse E.proj s) :
    letI := E.ringModuleOf
    have := E.lieModuleOf
    twoCocycle R L M where
  val := ⟨(E.twoCocycleAux hs).compr₂ E.toKer.symm, by simp⟩
  property := by
    -- TODO Try to golf this after https://github.com/leanprover-community/mathlib4/pull/27306 lands
    ext x y z
    suffices ⁅s x, ⁅s y, s z⁆⁆ - ⁅s x, s ⁅y, z⁆⁆ -
        (⁅s y, ⁅s x, s z⁆⁆ - ⁅s y, s ⁅x, z⁆⁆) + (⁅s z, ⁅s x, s y⁆⁆ - ⁅s z, s ⁅x, y⁆⁆) -
          (⁅s ⁅x, y⁆, s z⁆ - (s ⁅x, ⁅y, z⁆⁆ - s ⁅y, ⁅x, z⁆⁆)) +
        (⁅s ⁅x, z⁆, s y⁆ - (s ⁅x, ⁅z, y⁆⁆ - s ⁅z, ⁅x, y⁆⁆)) -
        (⁅s ⁅y, z⁆, s x⁆ - (s ⁅y, ⁅z, x⁆⁆ - s ⁅z, ⁅y, x⁆⁆)) = 0 by
      set h := E.proj_surjective.hasRightInverse
      have aux (u : L) (v : E.proj.ker) : ⁅h.choose u, v⁆ = ⁅s u, v⁆ := by
        rw [← E.lie_apply_proj_of_leftInverse_eq hs, h.choose_spec _]
      simpa [← map_sub, ← map_add, ← twoCochain_val_apply, Subtype.ext_iff, twoCocycleAux, aux]
    have hjac := lie_lie (s x) (s y) (s z)
    rw [← lie_skew, neg_eq_iff_eq_neg] at hjac
    have hja := congr_arg s (lie_lie x y z)
    rw [← lie_skew, map_neg, neg_eq_iff_eq_neg] at hja
    have hj := congr_arg s (lie_lie y x z)
    rw [← lie_skew, map_neg, neg_eq_iff_eq_neg] at hj
    rw [hjac, hj, hja, ← lie_skew y z, ← lie_skew _ (s (-⁅z, y⁆)), ← lie_skew (s ⁅x, z⁆),
      ← lie_skew (s ⁅x, y⁆), ← lie_skew x z]
    simp only [map_neg, neg_lie, neg_neg, neg_sub, lie_neg, sub_neg_eq_add,
      sub_add_cancel_right, map_add, neg_add_rev]
    abel_nf

end LieAlgebra.Extension
