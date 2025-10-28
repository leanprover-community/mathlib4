/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Lie.Cochain
import Mathlib.Algebra.Module.TransferInstance

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
* `LieAlgebra.Extension.ofIsExtension`: A function that builds the bundled structure from the class.
* `LieAlgebra.Extension.ofTwoCocycleAlg`: A Lie algebra built from a direct product, but whose
  bracket product is sheared by a 2-cocycle.
* `LieAlgebra.Extension.ofTwoCocycle` - A Lie algebra extension constructed from a 2-cocycle

## TODO

## References
* [Chevalley, Eilenberg, *Cohomology Theory of Lie Groups and Lie
  Algebras*](chevalley_eilenberg_1948)
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

-/

suppress_compilation

namespace LieAlgebra

variable {R N L M V : Type*}

section IsExtension

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/-- A sequence of two Lie algebra homomorphisms is an extension if it is short exact. -/
structure IsExtension (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker

lemma range_eq_ker_iff (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) : i.range = p.ker ↔ Function.Exact i p := by
  constructor
  · intro h x
    rw [← LieHom.coe_range, h]
    rfl
  · intro h
    exact (LieSubalgebra.ext (LieIdeal.toLieSubalgebra R L p.ker) i.range h).symm

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

/-- A surjective Lie algebra homomorphism yields an extension. -/
lemma isExtension.of_surjective (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
    IsExtension f.ker.incl f where
  ker_eq_bot := LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

lemma IsExtension.range_eq_ker (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) (h : IsExtension i p) :
    LinearMap.range i.toLinearMap = p.ker := by
  have := h.exact
  rw [← LieSubalgebra.coe_set_eq] at this
  exact Submodule.ext fun x ↦ Eq.to_iff (congrFun this x)

/-- The bundled `LieAlgebra.Extension` corresponding to `LieAlgebra.IsExtension` -/
@[simps] def Extension.ofIsExtension {i : N →ₗ⁅R⁆ L} {p : L →ₗ⁅R⁆ M}
   (h : LieAlgebra.IsExtension i p) :
    Extension R N M :=
  ⟨L, _, _, i, p, h⟩

end IsExtension

namespace Extension

section

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
[LieAlgebra R M] (E : Extension R N M)

instance : LieRing E.L := E.instLieRing

instance : LieAlgebra R E.L := E.instLieAlgebra

lemma incl_injective : Function.Injective E.incl :=
  (LieHom.ker_eq_bot E.incl).mp (IsExtension.ker_eq_bot E.IsExtension)

lemma proj_surjective : Function.Surjective E.proj :=
  (LieHom.range_eq_top E.proj).mp (IsExtension.range_eq_top E.IsExtension)

lemma exact : E.incl.range = E.proj.ker :=
  IsExtension.exact E.IsExtension

@[simp]
lemma proj_incl (x : N) : E.proj (E.incl x) = 0 :=
  LieHom.mem_ker.mp <| LieHom.mem_ker.mpr <| le_of_eq (exact E) <| LieHom.mem_range_self E.incl x

/-- The equivalence between the range of the inclusion and the source. -/
def sectLeft (E : Extension R N M) : E.incl.range ≃ₗ[R] N :=
  (LinearEquiv.ofInjective E.incl.toLinearMap E.incl_injective).symm

@[simp]
lemma incl_sectLeft (E : Extension R N M) (x : E.incl.range) :
    E.incl (E.sectLeft x) = x.val := by
  rw [sectLeft, ← LieHom.coe_toLinearMap, ← LinearEquiv.ofInjective_apply (h := E.incl_injective)]
  exact Subtype.eq_iff.mp <| LinearEquiv.apply_symm_apply _ x

/-- The equivalence between the kernel of projection and range of inclusion. -/
def projInclEquiv : E.proj.ker ≃ₗ[R] E.incl.range :=
  LinearEquiv.ofEq (LieSubmodule.toSubmodule (LieHom.ker E.proj))
    (LinearMap.range E.incl.toLinearMap)
    (Submodule.ext (fun x ↦ ((LieSubalgebra.ext_iff' _ _).mp E.IsExtension.exact) x)).symm

/-- Delete this. -/
def kerProjEquiv :
    E.proj.ker ≃ₗ[R] N := E.projInclEquiv ≪≫ₗ E.sectLeft

lemma eq_of_proj_eq (E : Extension R N M) {p : E.L →ₗ[R] N} {x y : E.L} (h : p x = p y)
    (hp : Function.LeftInverse p E.incl) (hE : E.proj x = E.proj y) : x = y := by
  have : x - y ∈ LinearMap.ker E.proj.toLinearMap := LinearMap.sub_mem_ker_iff.mpr hE
  have : ∃ z : N, E.incl z = x - y := by
    rw [← LieHom.ker_toSubmodule] at this
    rw [← LieHom.mem_range, exact]
    exact this
  obtain ⟨z, hz⟩ := this
  have : p (x - y) = 0 := by rw [LinearMap.map_sub, h, sub_eq_zero]
  have : z = 0 := by rw [← hp z, hz, this]
  rw [this, map_zero] at hz
  rw [← sub_eq_zero, ← hz]

/-- `Extension`s are equivalent iff there is a homomorphism making a commuting diagram. -/
@[ext] structure Equiv (E' : Extension R N M) where
  /-- The homomorphism -/
  toLieEquiv : E.L ≃ₗ⁅R⁆ E'.L
  /-- The left-hand side of the diagram commutes. -/
  incl_comm : toLieEquiv.comp E.incl = E'.incl
  /-- The right-hand side of the diagram commutes. -/
  proj_comm : E'.proj.comp toLieEquiv = E.proj

namespace Equiv

instance : Mul (E.Equiv E) where
  mul x y := {
    toLieEquiv := x.toLieEquiv.trans y.toLieEquiv
    incl_comm := by
      ext z
      rw [LieHom.comp_apply, LieEquiv.trans, LieHom.comp_apply, ← LieHom.comp_apply _ _ z,
        x.incl_comm, ← LieHom.comp_apply, y.incl_comm]
    proj_comm := by
      ext z
      rw [LieHom.comp_apply, LieEquiv.trans, LieHom.comp_apply,
        ← LieHom.comp_apply _ _ (x.toLieEquiv.toLieHom z), y.proj_comm, ← LieHom.comp_apply,
        x.proj_comm] }

@[simp]
lemma mul_eq (x y : E.Equiv E) : (x * y).toLieEquiv = x.toLieEquiv.trans y.toLieEquiv :=
  rfl

instance : One (E.Equiv E) where
  one := {
    toLieEquiv := LieEquiv.refl
    incl_comm := by ext; simp
    proj_comm := by ext; simp }

@[simp] lemma one_eq : (1 : E.Equiv E).toLieEquiv = LieEquiv.refl := rfl

instance : Inv (E.Equiv E) where
  inv x := {
    toLieEquiv := x.toLieEquiv.symm
    incl_comm := by
      ext y
      simp only [LieHom.coe_comp, LieEquiv.coe_coe, Function.comp_apply]
      nth_rw 2 [show E.incl y = x.toLieEquiv.symm (x.toLieEquiv (E.incl y)) by simp]
      have : (x.toLieEquiv (E.incl y)) = (x.toLieEquiv.comp E.incl) y := by
        rw [LieHom.comp_apply, LieEquiv.coe_toLieHom]
      rw [this, x.incl_comm]
    proj_comm := by
      ext y
      simp only [LieHom.coe_comp, LieEquiv.coe_coe, Function.comp_apply]
      rw [show E.proj y = E.proj.comp x.toLieEquiv (x.toLieEquiv.symm y) by simp, x.proj_comm]
  }

@[simp] lemma inv_eq (x : E.Equiv E) : x⁻¹.toLieEquiv = x.toLieEquiv.symm := rfl

instance : Group (E.Equiv E) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel x := by ext; simp

end Equiv

end

section Algebra

open LieModule.Cohomology

variable [CommRing R] [LieRing M] [LieAlgebra R M]

/-- A one-field structure giving a type synonym for a direct product. We use this to describe an
alternative Lie algebra structure on the product, where the bracket is shifted by a 2-cocycle. -/
structure ofTwoCocycleAlg {R M N} [CommRing R] [LieRing M] [LieAlgebra R M] [AddCommGroup N]
    [Module R N] [LieRingModule M N] [LieModule R M N]
    (c : twoCocycle R M N) where
  /-- The underlying type. -/
  carrier : M × N

variable [AddCommGroup N] [Module R N] [LieRingModule M N] [LieModule R M N]
(c : twoCocycle R M N)

/-- An equivalence between the direct product and the corresponding one-field structure. This is
used to transfer the additive and scalar-multiple structure on the direct product to the type
synonym. -/
def ofProd : M × N ≃ ofTwoCocycleAlg c where
  toFun a := ⟨ a ⟩
  invFun a := a.carrier

-- transport instances along equivalence!
instance : AddCommGroup (ofTwoCocycleAlg c) := (ofProd c).symm.addCommGroup

instance : Module R (ofTwoCocycleAlg c) := (ofProd c).symm.module R

@[simp] lemma of_zero : ofProd c (0 : M × N) = 0 := rfl
@[simp] lemma of_add (x y : M × N) : ofProd c (x + y) = ofProd c x + ofProd c y := rfl
@[simp] lemma of_smul (r : R) (x : M × N) : (ofProd c) (r • x) = r • ofProd c x := rfl

@[simp] lemma of_symm_zero : (ofProd c).symm (0 : ofTwoCocycleAlg c) = 0 := rfl
@[simp] lemma of_symm_add (x y : ofTwoCocycleAlg c) :
  (ofProd c).symm (x + y) = (ofProd c).symm x + (ofProd c).symm y := rfl
@[simp] lemma of_symm_smul (r : R) (x : ofTwoCocycleAlg c) :
  (ofProd c).symm (r • x) = r • (ofProd c).symm x := rfl

@[simp] lemma of_nsmul (n : ℕ) (x : M × N) : (ofProd c) (n • x) = n • (ofProd c) x := rfl
@[simp] lemma of_symm_nsmul (n : ℕ) (x : ofTwoCocycleAlg c) :
  (ofProd c).symm (n • x) = n • (ofProd c).symm x := rfl

instance : LieRing (ofTwoCocycleAlg c) where
  bracket x y := ofProd c (⁅((ofProd c).symm x).1, ((ofProd c).symm y).1⁆,
    c.1.val ((ofProd c).symm x).1 ((ofProd c).symm y).1 +
    ⁅((ofProd c).symm x).1, ((ofProd c).symm y).2⁆ - ⁅((ofProd c).symm y).1, ((ofProd c).symm x).2⁆)
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
    have := d₂₃_apply R M N c ((ofProd c).symm x).1 ((ofProd c).symm y).1 ((ofProd c).symm z).1
    simp only [hc, LinearMap.zero_apply] at this
    rw [← twoCochain_skew _ _ ⁅((ofProd c).symm x).1, ((ofProd c).symm z).1⁆,
      ← twoCochain_skew _ _ ⁅((ofProd c).symm y).1, ((ofProd c).symm z).1⁆, eq_sub_iff_add_eq,
      zero_add, neg_eq_iff_eq_neg] at this
    rw [this]
    abel

lemma bracket_ofTwoCocycleAlg {c : twoCocycle R M N} (x y : ofTwoCocycleAlg c) :
    ⁅x, y⁆ = ofProd c (⁅((ofProd c).symm x).1, ((ofProd c).symm y).1⁆,
      c.1.val ((ofProd c).symm x).1 ((ofProd c).symm y).1 +
      ⁅((ofProd c).symm x).1, ((ofProd c).symm y).2⁆ -
      ⁅((ofProd c).symm y).1, ((ofProd c).symm x).2⁆) :=
  rfl

instance : LieAlgebra R (ofTwoCocycleAlg c) where
  lie_smul r x y := by
    simp only [bracket_ofTwoCocycleAlg]
    exact Equiv.congr_arg (by simp [← smul_add, smul_sub])

/-- The Lie algebra map from a central extension derived from a 2-cocycle. -/
@[simps]
def twoCocycleProj : (ofTwoCocycleAlg c) →ₗ⁅R⁆ M where
  toLinearMap := {
    toFun x := ((ofProd c).symm x).1
    map_add' _ _ := by simp
    map_smul' _ _ := by simp }
  map_lie' {x y} := by simp [bracket_ofTwoCocycleAlg]

lemma surjective_of_cocycle : Function.Surjective (twoCocycleProj c) :=
  fun x ↦ Exists.intro ((ofProd c) (x, 0)) rfl

/-- An equivalence of extended Lie algebras induced by translation by a coboundary. -/
@[simps]
def LieEquiv.ofCoboundary (c' : twoCocycle R M N) (x : oneCochain R M N)
    (h : c' = c + d₁₂ R M N x) :
    LieEquiv R (ofTwoCocycleAlg c) (ofTwoCocycleAlg c') where
  toFun y := ofProd c' (((ofProd c).symm y).1, ((ofProd c).symm y).2 - x ((ofProd c).symm y).1)
  map_add' _ _ := by
    simp only [← of_add]
    exact Equiv.congr_arg (by simp; abel)
  map_smul' _ _ := by
    simp only [← of_smul]
    simp [smul_sub]
  map_lie' {a b} := by
    refine (Equiv.apply_eq_iff_eq_symm_apply (ofProd c')).mpr ?_
    simp only [bracket_ofTwoCocycleAlg, Equiv.symm_apply_apply, h, Submodule.coe_add,
      LinearMap.add_apply, Prod.mk.injEq, true_and]
    simp only [twoCochain_val_apply (d₁₂ R M N x), d₁₂_apply_apply, lie_sub]
    abel
  invFun z := ofProd c (((ofProd c').symm z).1, ((ofProd c').symm z).2 + x ((ofProd c').symm z).1)
  left_inv y := by simp
  right_inv z := by simp

end Algebra

section ofTwoCocycle

open LieModule.Cohomology

variable [CommRing R] [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N] [IsLieAbelian N]
[LieRingModule M N] [LieModule R M N] (c : twoCocycle R M N)

/-- An extension of Lie algebras defined by a 2-cocycle. -/
def ofTwoCocycle : Extension R N M where
  L := ofTwoCocycleAlg c
  instLieRing := inferInstance
  instLieAlgebra := inferInstance
  incl :=
    { toFun x := ofProd c (0, x)
      map_add' _ _ := by simp [← of_add]
      map_smul' _ _ := by simp [← of_smul]
      map_lie' {_ _} := by simp [bracket_ofTwoCocycleAlg] }
  proj :=
    { toFun x := ((ofProd c).symm x).1
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      map_lie' {_ _} := by simp [bracket_ofTwoCocycleAlg] }
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

instance : LieRing (ofTwoCocycle c).L := (ofTwoCocycle c).instLieRing
instance : LieAlgebra R (ofTwoCocycle c).L := (ofTwoCocycle c).instLieAlgebra

/-- The Lie algebra isomorphism given by the type synonym. -/
def ofAlg : ofTwoCocycleAlg c ≃ₗ⁅R⁆ (ofTwoCocycle c).L := LieEquiv.refl

lemma bracket_ofTwoCocycle (x y : (ofTwoCocycle c).L) :
    ⁅x, y⁆ = ofAlg c ⁅(ofAlg c).symm x, (ofAlg c).symm y⁆ := rfl

end ofTwoCocycle

variable [CommRing R] [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N]

open LieModule.Cohomology

lemma apply_sub_apply_mem_ker (E : Extension R N M) {s₁ s₂ : M →ₗ[R] E.L}
    (hs₁ : Function.LeftInverse E.proj s₁) (hs₂ : Function.LeftInverse E.proj s₂)
    (a : M) :
    (s₁ a) - (s₂ a) ∈ LinearMap.ker E.proj.toLinearMap := by
  rw [LinearMap.mem_ker, LieHom.coe_toLinearMap, map_sub, hs₁, hs₂, sub_eq_zero]

/-- The 1-cochain attached to a pair of splittings of an extension. -/
@[simps]
def oneCochain_of_two_splitting (E : Extension R N M) {s₁ s₂ : M →ₗ[R] E.L}
    (hs₁ : Function.LeftInverse E.proj s₁) (hs₂ : Function.LeftInverse E.proj s₂) :
    oneCochain R M N where
  toFun m := E.sectLeft (E.projInclEquiv ⟨(s₁ m) - (s₂ m), E.apply_sub_apply_mem_ker hs₁ hs₂ m⟩)
  map_add' _ _ := by
    rw [← map_add, ← map_add, AddMemClass.mk_add_mk, EquivLike.apply_eq_iff_eq,
      EquivLike.apply_eq_iff_eq]
    refine Subtype.mk_eq_mk.mpr ?_
    rw [map_add, map_add, add_sub_add_comm]
  map_smul' _ _ := by
    rw [RingHom.id_apply, ← map_smul, EquivLike.apply_eq_iff_eq, ← map_smul,
      EquivLike.apply_eq_iff_eq, SetLike.mk_smul_of_tower_mk]
    refine Subtype.mk_eq_mk.mpr ?_
    rw [LinearMap.map_smul_of_tower, smul_sub, LinearMap.map_smul_of_tower]

end Extension

end LieAlgebra
