/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

#align_import linear_algebra.clifford_algebra.even from "leanprover-community/mathlib"@"9264b15ee696b7ca83f13c8ad67c83d6eb70b730"

/-!
# The universal property of the even subalgebra

## Main definitions

* `CliffordAlgebra.even Q`: The even subalgebra of `CliffordAlgebra Q`.
* `CliffordAlgebra.EvenHom`: The type of bilinear maps that satisfy the universal property of the
  even subalgebra
* `CliffordAlgebra.even.lift`: The universal property of the even subalgebra, which states
  that every bilinear map `f` with `f v v = Q v` and `f u v * f v w = Q v • f u w` is in unique
  correspondence with an algebra morphism from `CliffordAlgebra.even Q`.

## Implementation notes

The approach here is outlined in "Computing with the universal properties of the Clifford algebra
and the even subalgebra" (to appear).

The broad summary is that we have two tricks available to us for implementing complex recursors on
top of `CliffordAlgebra.lift`: the first is to use morphisms as the output type, such as
`A = Module.End R N` which is how we obtained `CliffordAlgebra.foldr`; and the second is to use
`N = (N', S)` where `N'` is the value we wish to compute, and `S` is some auxiliary state passed
between one recursor invocation and the next.
For the universal property of the even subalgebra, we apply a variant of the first trick again by
choosing `S` to itself be a submodule of morphisms.
-/


namespace CliffordAlgebra

-- porting note: explicit universes
universe uR uM uA uB

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

-- put this after `Q` since we want to talk about morphisms from `CliffordAlgebra Q` to `A` and
-- that order is more natural
variable {A : Type uA} {B : Type uB} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

open scoped DirectSum

variable (Q)

/-- The even submodule `CliffordAlgebra.evenOdd Q 0` is also a subalgebra. -/
def even : Subalgebra R (CliffordAlgebra Q) :=
  (evenOdd Q 0).toSubalgebra (SetLike.one_mem_graded _) fun _x _y hx hy =>
    add_zero (0 : ZMod 2) ▸ SetLike.mul_mem_graded hx hy
#align clifford_algebra.even CliffordAlgebra.even

-- porting note: added, otherwise Lean can't find this when it needs it
instance : AddCommMonoid (even Q) := AddSubmonoidClass.toAddCommMonoid _
@[simp]
theorem even_toSubmodule : Subalgebra.toSubmodule (even Q) = evenOdd Q 0 :=
  rfl
#align clifford_algebra.even_to_submodule CliffordAlgebra.even_toSubmodule

variable (A)

/-- The type of bilinear maps which are accepted by `CliffordAlgebra.even.lift`. -/
@[ext]
structure EvenHom : Type max uA uM where
  bilin : M →ₗ[R] M →ₗ[R] A
  contract (m : M) : bilin m m = algebraMap R A (Q m)
  contract_mid (m₁ m₂ m₃ : M) : bilin m₁ m₂ * bilin m₂ m₃ = Q m₂ • bilin m₁ m₃
#align clifford_algebra.even_hom CliffordAlgebra.EvenHom

variable {A Q}

/-- Compose an `EvenHom` with an `AlgHom` on the output. -/
@[simps]
def EvenHom.compr₂ (g : EvenHom Q A) (f : A →ₐ[R] B) : EvenHom Q B where
  bilin := g.bilin.compr₂ f.toLinearMap
  contract _m := (f.congr_arg <| g.contract _).trans <| f.commutes _
  contract_mid _m₁ _m₂ _m₃ :=
    (f.map_mul _ _).symm.trans <| (f.congr_arg <| g.contract_mid _ _ _).trans <| f.map_smul _ _
#align clifford_algebra.even_hom.compr₂ CliffordAlgebra.EvenHom.compr₂

variable (Q)

/-- The embedding of pairs of vectors into the even subalgebra, as a bilinear map. -/
@[simps! bilin_apply_apply_coe]
nonrec def even.ι : EvenHom Q (even Q) where
  bilin :=
    LinearMap.mk₂ R (fun m₁ m₂ => ⟨ι Q m₁ * ι Q m₂, ι_mul_ι_mem_evenOdd_zero Q _ _⟩)
      (fun _ _ _ => by simp only [LinearMap.map_add, add_mul]; rfl)
                       -- ⊢ { val := ↑(CliffordAlgebra.ι Q) x✝² * ↑(CliffordAlgebra.ι Q) x✝ + ↑(Clifford …
                                                               -- 🎉 no goals
      (fun _ _ _ => by simp only [LinearMap.map_smul, smul_mul_assoc]; rfl)
                       -- ⊢ { val := x✝² • (↑(CliffordAlgebra.ι Q) x✝¹ * ↑(CliffordAlgebra.ι Q) x✝), pro …
                                                                       -- 🎉 no goals
      (fun _ _ _ => by simp only [LinearMap.map_add, mul_add]; rfl) fun _ _ _ => by
                       -- ⊢ { val := ↑(CliffordAlgebra.ι Q) x✝² * ↑(CliffordAlgebra.ι Q) x✝¹ + ↑(Cliffor …
                                                               -- 🎉 no goals
      simp only [LinearMap.map_smul, mul_smul_comm]; rfl
      -- ⊢ { val := x✝² • (↑(CliffordAlgebra.ι Q) x✝¹ * ↑(CliffordAlgebra.ι Q) x✝), pro …
                                                     -- 🎉 no goals
  contract m := Subtype.ext <| ι_sq_scalar Q m
  contract_mid m₁ m₂ m₃ :=
    Subtype.ext <|
      calc
        ι Q m₁ * ι Q m₂ * (ι Q m₂ * ι Q m₃) = ι Q m₁ * (ι Q m₂ * ι Q m₂ * ι Q m₃) := by
          simp only [mul_assoc]
          -- 🎉 no goals
        _ = Q m₂ • (ι Q m₁ * ι Q m₃) := by rw [Algebra.smul_def, ι_sq_scalar, Algebra.left_comm]
                                           -- 🎉 no goals
#align clifford_algebra.even.ι CliffordAlgebra.even.ι

instance : Inhabited (EvenHom Q (even Q)) :=
  ⟨even.ι Q⟩

variable (f : EvenHom Q A)

/-- Two algebra morphisms from the even subalgebra are equal if they agree on pairs of generators.

See note [partially-applied ext lemmas]. -/
@[ext high]
theorem even.algHom_ext ⦃f g : even Q →ₐ[R] A⦄ (h : (even.ι Q).compr₂ f = (even.ι Q).compr₂ g) :
    f = g := by
  rw [EvenHom.ext_iff] at h
  -- ⊢ f = g
  ext ⟨x, hx⟩
  -- ⊢ ↑f { val := x, property := hx } = ↑g { val := x, property := hx }
  refine' even_induction _ _ _ _ _ hx
  · intro r
    -- ⊢ ↑f { val := ↑(algebraMap R (CliffordAlgebra ?m.107570)) r, property := (_ :  …
    exact (f.commutes r).trans (g.commutes r).symm
    -- 🎉 no goals
  · intro x y hx hy ihx ihy
    -- ⊢ ↑f { val := x + y, property := (_ : x + y ∈ evenOdd Q 0) } = ↑g { val := x + …
    have := congr_arg₂ (· + ·) ihx ihy
    -- ⊢ ↑f { val := x + y, property := (_ : x + y ∈ evenOdd Q 0) } = ↑g { val := x + …
    exact (f.map_add _ _).trans (this.trans <| (g.map_add _ _).symm)
    -- 🎉 no goals
  · intro m₁ m₂ x hx ih
    -- ⊢ ↑f { val := ↑(CliffordAlgebra.ι Q) m₁ * ↑(CliffordAlgebra.ι Q) m₂ * x, prope …
    have := congr_arg₂ (· * ·) (LinearMap.congr_fun (LinearMap.congr_fun h m₁) m₂) ih
    -- ⊢ ↑f { val := ↑(CliffordAlgebra.ι Q) m₁ * ↑(CliffordAlgebra.ι Q) m₂ * x, prope …
    exact (f.map_mul _ _).trans (this.trans <| (g.map_mul _ _).symm)
    -- 🎉 no goals
#align clifford_algebra.even.alg_hom_ext CliffordAlgebra.even.algHom_ext

variable {Q}

namespace even.lift

/-- An auxiliary submodule used to store the half-applied values of `f`.
This is the span of elements `f'` such that `∃ x m₂, ∀ m₁, f' m₁ = f m₁ m₂ * x`.  -/
private def S : Submodule R (M →ₗ[R] A) :=
  Submodule.span R
    {f' | ∃ x m₂, f' = LinearMap.lcomp R _ (f.bilin.flip m₂) (LinearMap.mulRight R x)}

/-- An auxiliary bilinear map that is later passed into `CliffordAlgebra.foldr`. Our desired result
is stored in the `A` part of the accumulator, while auxiliary recursion state is stored in the `S f`
part. -/
private def fFold : M →ₗ[R] A × S f →ₗ[R] A × S f :=
  LinearMap.mk₂ R
    (fun m acc =>
      /- We could write this `snd` term in a point-free style as follows, but it wouldn't help as we
        don't have any prod or subtype combinators to deal with n-linear maps of this degree.
        ```lean
        (LinearMap.lcomp R _ (Algebra.lmul R A).to_linear_map.flip).comp $
          (LinearMap.llcomp R M A A).flip.comp f.flip : M →ₗ[R] A →ₗ[R] M →ₗ[R] A)
        ```
        -/
      (acc.2.val m,
        ⟨(LinearMap.mulRight R acc.1).comp (f.bilin.flip m), Submodule.subset_span <| ⟨_, _, rfl⟩⟩))
    (fun m₁ m₂ a =>
      Prod.ext (LinearMap.map_add _ m₁ m₂)
        (Subtype.ext <|
          LinearMap.ext fun m₃ =>
            show f.bilin m₃ (m₁ + m₂) * a.1 = f.bilin m₃ m₁ * a.1 + f.bilin m₃ m₂ * a.1 by
              rw [map_add, add_mul]))
              -- 🎉 no goals
    (fun c m a =>
      Prod.ext (LinearMap.map_smul _ c m)
        (Subtype.ext <|
          LinearMap.ext fun m₃ =>
            show f.bilin m₃ (c • m) * a.1 = c • (f.bilin m₃ m * a.1) by
              rw [LinearMap.map_smul, smul_mul_assoc]))
              -- 🎉 no goals
    (fun m a₁ a₂ => Prod.ext rfl (Subtype.ext <| LinearMap.ext fun m₃ => mul_add _ _ _))
    fun c m a => Prod.ext rfl (Subtype.ext <| LinearMap.ext fun m₃ => mul_smul_comm _ _ _)

@[simp]
private theorem fst_fFold_fFold (m₁ m₂ : M) (x : A × S f) :
    (fFold f m₁ (fFold f m₂ x)).fst = f.bilin m₁ m₂ * x.fst :=
  rfl

@[simp]
private theorem snd_fFold_fFold (m₁ m₂ m₃ : M) (x : A × S f) :
    ((fFold f m₁ (fFold f m₂ x)).snd : M →ₗ[R] A) m₃ = f.bilin m₃ m₁ * (x.snd : M →ₗ[R] A) m₂ :=
  rfl

private theorem fFold_fFold (m : M) (x : A × S f) : fFold f m (fFold f m x) = Q m • x := by
  obtain ⟨a, ⟨g, hg⟩⟩ := x
  -- ⊢ ↑(↑(CliffordAlgebra.even.lift.fFold f) m) (↑(↑(CliffordAlgebra.even.lift.fFo …
  ext : 2
  -- ⊢ (↑(↑(CliffordAlgebra.even.lift.fFold f) m) (↑(↑(CliffordAlgebra.even.lift.fF …
  · change f.bilin m m * a = Q m • a
    -- ⊢ ↑(↑f.bilin m) m * a = ↑Q m • a
    rw [Algebra.smul_def, f.contract]
    -- 🎉 no goals
  · ext m₁
    -- ⊢ ↑↑(↑(↑(CliffordAlgebra.even.lift.fFold f) m) (↑(↑(CliffordAlgebra.even.lift. …
    change f.bilin _ _ * g m = Q m • g m₁
    -- ⊢ ↑(↑f.bilin m₁) m * ↑g m = ↑Q m • ↑g m₁
    apply Submodule.span_induction' _ _ _ _ hg
    · rintro _ ⟨b, m₃, rfl⟩
      -- ⊢ ↑(↑f.bilin m₁) m * ↑(↑(LinearMap.lcomp R A (↑(LinearMap.flip f.bilin) m₃)) ( …
      change f.bilin _ _ * (f.bilin _ _ * b) = Q m • (f.bilin _ _ * b)
      -- ⊢ ↑(↑f.bilin m₁) m * (↑(↑f.bilin m) m₃ * b) = ↑Q m • (↑(↑f.bilin m₁) m₃ * b)
      rw [← smul_mul_assoc, ← mul_assoc, f.contract_mid]
      -- 🎉 no goals
    · change f.bilin m₁ m * 0 = Q m • (0 : A)  -- porting note: `•` now needs the type of `0`
      -- ⊢ ↑(↑f.bilin m₁) m * 0 = ↑Q m • 0
      rw [mul_zero, smul_zero]
      -- 🎉 no goals
    · rintro x hx y hy ihx ihy
      -- ⊢ ↑(↑f.bilin m₁) m * ↑(x + y) m = ↑Q m • ↑(x + y) m₁
      rw [LinearMap.add_apply, LinearMap.add_apply, mul_add, smul_add, ihx, ihy]
      -- 🎉 no goals
    · rintro x hx c ihx
      -- ⊢ ↑(↑f.bilin m₁) m * ↑(x • hx) m = ↑Q m • ↑(x • hx) m₁
      rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul_comm, ihx, smul_comm]
      -- 🎉 no goals

-- Porting note: In Lean 3, `aux_apply` isn't a simp lemma. I changed `{ attrs := [] }` to
-- `{ isSimp := false }`, so that `aux_apply` isn't a simp lemma.
/-- The final auxiliary construction for `CliffordAlgebra.even.lift`. This map is the forwards
direction of that equivalence, but not in the fully-bundled form. -/
@[simps! (config := { isSimp := false }) apply]
def aux (f : EvenHom Q A) : CliffordAlgebra.even Q →ₗ[R] A := by
  refine ?_ ∘ₗ (even Q).val.toLinearMap
  -- ⊢ CliffordAlgebra Q →ₗ[R] A
  -- porting note: added, can't be found otherwise
  letI : AddCommGroup (S f) := AddSubgroupClass.toAddCommGroup _
  -- ⊢ CliffordAlgebra Q →ₗ[R] A
  exact LinearMap.fst R _ _ ∘ₗ foldr Q (fFold f) (fFold_fFold f) (1, 0)
  -- 🎉 no goals
#align clifford_algebra.even.lift.aux CliffordAlgebra.even.lift.aux

@[simp]
theorem aux_one : aux f 1 = 1 :=
  congr_arg Prod.fst (foldr_one _ _ _ _)
#align clifford_algebra.even.lift.aux_one CliffordAlgebra.even.lift.aux_one

@[simp]
theorem aux_ι (m₁ m₂ : M) : aux f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ :=
  (congr_arg Prod.fst (foldr_mul _ _ _ _ _ _)).trans
    (by
      rw [foldr_ι, foldr_ι]
      -- ⊢ (↑(↑(CliffordAlgebra.even.lift.fFold f) m₁) (↑(↑(CliffordAlgebra.even.lift.f …
      exact mul_one _)
      -- 🎉 no goals
#align clifford_algebra.even.lift.aux_ι CliffordAlgebra.even.lift.aux_ι

@[simp]
theorem aux_algebraMap (r) (hr) : aux f ⟨algebraMap R _ r, hr⟩ = algebraMap R _ r :=
  (congr_arg Prod.fst (foldr_algebraMap _ _ _ _ _)).trans (Algebra.algebraMap_eq_smul_one r).symm
#align clifford_algebra.even.lift.aux_algebra_map CliffordAlgebra.even.lift.aux_algebraMap

@[simp]
theorem aux_mul (x y : even Q) : aux f (x * y) = aux f x * aux f y := by
  cases' x with x x_property
  -- ⊢ ↑(aux f) ({ val := x, property := x_property } * y) = ↑(aux f) { val := x, p …
  cases y
  -- ⊢ ↑(aux f) ({ val := x, property := x_property } * { val := val✝, property :=  …
  refine' (congr_arg Prod.fst (foldr_mul _ _ _ _ _ _)).trans _
  -- ⊢ (↑(↑(foldr Q (CliffordAlgebra.even.lift.fFold f) (_ : ∀ (m : M) (x : A × { x …
  dsimp only
  -- ⊢ (↑(↑(foldr Q (CliffordAlgebra.even.lift.fFold f) (_ : ∀ (m : M) (x : A × { x …
  refine' even_induction Q _ _ _ _ x_property
  · intro r
    -- ⊢ (↑(↑(foldr Q (CliffordAlgebra.even.lift.fFold f) (_ : ∀ (m : M) (x : A × { x …
    rw [foldr_algebraMap, aux_algebraMap]
    -- ⊢ (r • ↑(↑(foldr Q (CliffordAlgebra.even.lift.fFold f) (_ : ∀ (m : M) (x : A × …
    exact Algebra.smul_def r _
    -- 🎉 no goals
  · intro x y hx hy ihx ihy
    -- ⊢ (↑(↑(foldr Q (CliffordAlgebra.even.lift.fFold f) (_ : ∀ (m : M) (x : A × { x …
    rw [LinearMap.map_add, Prod.fst_add, ihx, ihy, ← add_mul, ← LinearMap.map_add]
    -- ⊢ ↑(aux f) ({ val := x, property := hx } + { val := y, property := hy }) * ↑(a …
    rfl
    -- 🎉 no goals
  · rintro m₁ m₂ x (hx : x ∈ even Q) ih
    -- ⊢ (↑(↑(foldr Q (CliffordAlgebra.even.lift.fFold f) (_ : ∀ (m : M) (x : A × { x …
    rw [aux_apply, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_fFold_fFold, ih, ← mul_assoc,
      Subtype.coe_mk, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_fFold_fFold]
    rfl
    -- 🎉 no goals
#align clifford_algebra.even.lift.aux_mul CliffordAlgebra.even.lift.aux_mul

end even.lift

open even.lift

variable (Q)

/-- Every algebra morphism from the even subalgebra is in one-to-one correspondence with a
bilinear map that sends duplicate arguments to the quadratic form, and contracts across
multiplication. -/
@[simps! symm_apply_bilin]
def even.lift : EvenHom Q A ≃ (CliffordAlgebra.even Q →ₐ[R] A) where
  toFun f := AlgHom.ofLinearMap (aux f) (aux_one f) (aux_mul f)
  invFun F := (even.ι Q).compr₂ F
  left_inv f := EvenHom.ext _ _ <| LinearMap.ext₂ <| even.lift.aux_ι f
  right_inv _ := even.algHom_ext Q <| EvenHom.ext _ _ <| LinearMap.ext₂ <| even.lift.aux_ι _
#align clifford_algebra.even.lift CliffordAlgebra.even.lift

-- @[simp] -- Porting note: simpNF linter times out on this one
theorem even.lift_ι (f : EvenHom Q A) (m₁ m₂ : M) :
    even.lift Q f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ :=
  even.lift.aux_ι _ _ _
#align clifford_algebra.even.lift_ι CliffordAlgebra.even.lift_ι

end CliffordAlgebra
