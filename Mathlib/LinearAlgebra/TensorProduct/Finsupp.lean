import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.GroupTheory.QuotientGroup

set_option autoImplicit false

noncomputable section
suppress_compilation

open TensorProduct AddSubgroup Submodule

variable (R : Type*) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable (N : Type*) [AddCommGroup N] [Module R N]
variable (P : Type*) [AddCommGroup P] [Module R P]
variable (Q : Type*) [AddCommGroup Q] [Module R Q]

def TensorProductFinsupp.NullGen : Set (M × N →₀ ℤ) :=
  { p : M × N →₀ ℤ |
    (∃ (m₁ m₂ : M) (n : N), p = .single (m₁ + m₂, n) 1 - .single (m₁, n) 1 - .single (m₂, n) 1) ∨
    (∃ (m : M) (n₁ n₂ : N), p = .single (m, n₁ + n₂) 1 - .single (m, n₁) 1 - .single (m, n₂) 1) ∨
    (∃ (r : R) (m : M) (n : N), p = .single (m, r • n) 1 - .single (r • m, n) 1) }

def TensorProductFinsupp.Null : AddSubgroup (M × N →₀ ℤ) := closure <| NullGen R M N

def TensorProductFinsupp := (M × N →₀ ℤ) ⧸ TensorProductFinsupp.Null R M N

namespace TensorProductFinsupp

variable {M} {N} in
def tmul (m : M) (n : N) : TensorProductFinsupp R M N :=
  (QuotientAddGroup.mk (fun₀ | (m, n) => 1 : M × N →₀ ℤ))

instance addCommGroup : AddCommGroup (TensorProductFinsupp R M N) :=
  QuotientAddGroup.Quotient.addCommGroup (Null R M N)

-- Note: has an extra hypothesis `neg` compared to the FreeAddMonoid/AddCon version
protected theorem induction_on' {motive : TensorProductFinsupp R M N → Prop}
    (z : TensorProductFinsupp R M N)
    (zero : motive 0)
    (tmul : ∀ m n, motive <| tmul R m n)
    (neg : ∀ x, motive x → motive (-x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  QuotientAddGroup.induction_on z fun x =>
    Finsupp.induction x zero fun a b f _ _ ih => by
      have hb : motive ((fun₀ | a => b) : (M × N →₀ ℤ) ⧸ Null R M N) := by
        have hk (k : ℕ) : motive ((fun₀ | a => (k : ℤ)) : (M × N →₀ ℤ) ⧸ Null R M N) := by
          induction k with
          | zero => rewrite [Nat.cast_zero, Finsupp.single_zero] ; exact zero
          | succ k ih =>
            rewrite [Nat.cast_succ, Finsupp.single_add, QuotientAddGroup.mk_add]
            exact add _ _ ih (tmul a.1 a.2)
        induction b with
        | ofNat k => exact hk k
        | negSucc k =>
          rewrite [Int.negSucc_eq, Finsupp.single_neg, QuotientAddGroup.mk_neg]
          exact neg _ (hk (k + 1))
      rewrite [QuotientAddGroup.mk_add]
      exact add _ _ hb ih

variable {M} {N} {P} {Q} {R}

/-- Scalar multiplication can be moved from one side of the tensor product to the other .-/
theorem smul_tmul (r : R) (m : M) (n : N) : tmul R (r • m) n = tmul R m (r • n) :=
  Quotient.sound' <| QuotientAddGroup.leftRel_apply.mpr <| AddSubgroup.subset_closure <|
    Or.inr <| Or.inr <| ⟨r, m, n, neg_add_eq_sub _ _⟩

@[simp]
theorem tmul_smul (r : R) (m : M) (n : N) : tmul R m (r • n) = tmul R (r • m) n :=
  (smul_tmul _ _ _).symm

variable (M) in
@[simp]
theorem zero_tmul (n : N) : tmul R (0 : M) n = 0 :=
  Quotient.sound' <| QuotientAddGroup.leftRel_apply.mpr <| AddSubgroup.subset_closure <|
    Or.inl <| ⟨0, 0, n, by rw [add_zero, add_zero, sub_self, zero_sub]⟩

variable (N) in
@[simp]
theorem tmul_zero (m : M) : tmul R m (0 : N) = 0 :=
  Quotient.sound' <| QuotientAddGroup.leftRel_apply.mpr <| AddSubgroup.subset_closure <|
    Or.inr <| Or.inl <| ⟨m, 0, 0, by rw [add_zero, add_zero, sub_self, zero_sub]⟩

theorem add_tmul (m₁ m₂ : M) (n : N) : tmul R (m₁ + m₂) n = tmul R m₁ n + tmul R m₂ n :=
  Eq.symm <| Quotient.sound' <| QuotientAddGroup.leftRel_apply.mpr <| AddSubgroup.subset_closure <|
    Or.inl <| ⟨m₁, m₂, n, by rw [neg_add_eq_sub, sub_add_eq_sub_sub]⟩

theorem tmul_add (m : M) (n₁ n₂ : N) : tmul R m (n₁ + n₂) = tmul R m n₁ + tmul R m n₂ :=
  Eq.symm <| Quotient.sound' <| QuotientAddGroup.leftRel_apply.mpr <| AddSubgroup.subset_closure <|
    Or.inr <| Or.inl <| ⟨m, n₁, n₂, by rw [neg_add_eq_sub, sub_add_eq_sub_sub]⟩

namespace Balanced

variable (f : M →+ N →+ P) (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n))

protected theorem _root_.Finsupp.lift.single_one (N S M : Type*) [Semiring S] [AddCommGroup N]
    [Module S N] [AddCommGroup M] [Module S M] (f : M → N) (i : M) :
      Finsupp.lift N S M f (fun₀ | i => 1 : M →₀ S) = f i := by
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (zero_smul S (f i)), one_smul]

/-- Lift an `R`-balanced map to the tensor product. -/
def lift : TensorProductFinsupp R M N →+ P :=
  QuotientAddGroup.lift (Null R M N) (Finsupp.lift P ℤ (M × N) fun mn => f mn.1 mn.2) <|
    (AddSubgroup.closure_le _).mpr <| by
      rintro x (⟨m₁, m₂, n, rfl⟩ | ⟨m, n₁, n₂, rfl⟩ | ⟨s, m, n, rfl⟩)
      . rw [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.map_sub, AddMonoidHom.map_sub,
          AddMonoidHom.coe_coe, Finsupp.lift.single_one, Finsupp.lift.single_one,
          Finsupp.lift.single_one, AddMonoidHom.map_add, AddMonoidHom.add_apply, add_sub_cancel',
          sub_self]
      . rw [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.map_sub, AddMonoidHom.map_sub,
          AddMonoidHom.coe_coe, Finsupp.lift.single_one, Finsupp.lift.single_one,
          Finsupp.lift.single_one, AddMonoidHom.map_add, add_sub_cancel', sub_self]
      . rw [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.map_sub, AddMonoidHom.coe_coe,
          Finsupp.lift.single_one, Finsupp.lift.single_one, hf, sub_self]

@[simp]
theorem lift_tmul (m : M) (n : N) :
    lift f hf (tmul R m n) = f m n := by
  rewrite [← Finsupp.lift.single_one P ℤ (M × N) (fun mn => f mn.1 mn.2) (m, n)]
  rfl

theorem ext' {g h : TensorProductFinsupp R M N →+ P} (H : ∀ x y, g (tmul R x y) = h (tmul R x y)) :
    g = h := by
  refine AddMonoidHom.ext fun z => TensorProductFinsupp.induction_on'
    (motive := fun z => g z = h z) z ?_ H (fun x ihx => ?_) (fun x y ihx ihy => ?_)
  . beta_reduce ; rw [AddMonoidHom.map_zero, AddMonoidHom.map_zero]
  . beta_reduce ; rw [AddMonoidHom.map_neg, AddMonoidHom.map_neg, ihx]
  . beta_reduce ; rw [AddMonoidHom.map_add, AddMonoidHom.map_add, ihx, ihy]

theorem lift.unique {g : TensorProductFinsupp R M N →+ P} (H : ∀ x y, g (tmul R x y) = f x y) :
    g = lift f hf :=
  ext' fun y x => by rw [lift_tmul, H]

variable (R) (M) (N) in
def mk : M →+ N →+ TensorProductFinsupp R M N := {
  toFun := fun m => {
    toFun := tmul R m
    map_zero' := by beta_reduce ; rw [tmul_zero]
    map_add' := fun x y => by dsimp ; rw [tmul_add]
  }
  map_zero' := by ext n ; dsimp; rw [zero_tmul]
  map_add' := fun m₁ m₂ => by ext n; dsimp; rw [add_tmul]
}

@[simp]
theorem mk_apply (m : M) (n : N) : mk R M N m n = tmul R m n := rfl

variable (R) (M) (N) in
theorem mk.balanced (r : R) (m : M) (n : N) : mk R M N (r • m) n = mk R M N m (r • n) :=
  smul_tmul r m n

theorem lift_mk : lift (mk R M N) (mk.balanced R M N) = AddMonoidHom.id _ :=
  Eq.symm <| lift.unique (mk R M N) (mk.balanced R M N)
    (fun x y => by rw [AddMonoidHom.id_apply, mk_apply])

theorem compr₂_balanced (g : P →+ Q) (r : R) (m : M) (n : N) :
    f.compr₂ g (r • m) n = f.compr₂ g m (r • n) := by
  rw [AddMonoidHom.compr₂_apply, AddMonoidHom.compr₂_apply, hf]

theorem lift_compr₂ (g : P →+ Q) :
    lift (f.compr₂ g) (compr₂_balanced f hf g) = g.comp (lift f hf) :=
  Eq.symm <| lift.unique (f.compr₂ g) (compr₂_balanced f hf g) fun x y => by
    rw [AddMonoidHom.compr₂_apply, AddMonoidHom.comp_apply, lift_tmul]

theorem lift_mk_compr₂ (f : TensorProductFinsupp R M N →+ P) :
    lift ((mk R M N).compr₂ f) (compr₂_balanced (mk R M N) (mk.balanced R M N) f) = f := by
  rw [lift_compr₂ (mk R M N) (mk.balanced R M N), lift_mk, AddMonoidHom.comp_id]

end Balanced

instance leftHasSmul : SMul R (TensorProductFinsupp R M N) :=
  ⟨fun r => Balanced.lift ((Balanced.mk R M N).comp (AddMonoidHom.smulLeft r)) fun r₁ m n => by
    dsimp
    rw [← smul_tmul, smul_comm]⟩

example (r : R) (m : M) (n : N) : r • tmul R m n = tmul R (r • m) n := by
  rewrite [← Finsupp.lift.single_one _ ℤ (M × N) (fun mn => tmul R (r •  mn.1) mn.2) (m, n)]
  rfl

protected theorem smul_zero (r : R) : r • (0 : TensorProductFinsupp R M N) = 0 :=
  AddMonoidHom.map_zero _

protected theorem smul_add (r : R) (x y : TensorProductFinsupp R M N) :
    r • (x + y) = r • x + r • y :=
  AddMonoidHom.map_add _ _ _

protected theorem smul_neg (r : R) (x : TensorProductFinsupp R M N) : r • -x = -(r • x) :=
  AddMonoidHom.map_neg _ _

theorem smul_tmul' (r : R) (m : M) (n : N) : r • tmul R m n = tmul R (r • m) n := by
  show (Balanced.lift (AddMonoidHom.comp (Balanced.mk R M N) (AddMonoidHom.smulLeft r)) _)
      (tmul R m n) = tmul R (r • m) n
  rewrite [← Finsupp.lift.single_one _ ℤ (M × N) (fun mn => tmul R (r •  mn.1) mn.2) (m, n)]
  rfl

protected theorem zero_smul (x : TensorProductFinsupp R M N) : (0 : R) • x = 0 :=
  TensorProductFinsupp.induction_on' (motive := fun x => 0 • x = 0) x
    (by beta_reduce; rw [TensorProductFinsupp.smul_zero])
    (fun m n => by beta_reduce; rw [smul_tmul', zero_smul, zero_tmul])
    (fun x ih => by beta_reduce; rw [TensorProductFinsupp.smul_neg, neg_eq_zero, ih])
    (fun x y ihx ihy => by beta_reduce; rw [TensorProductFinsupp.smul_add, ihx, ihy, add_zero])

protected theorem one_smul (x : TensorProductFinsupp R M N) : (1 : R) • x = x :=
  TensorProductFinsupp.induction_on' (motive := fun x => (1 : R) • x = x) x
    (by beta_reduce; rw [TensorProductFinsupp.smul_zero])
    (fun m n => by beta_reduce; rw [smul_tmul', one_smul])
    (fun x ih => by beta_reduce; rw [TensorProductFinsupp.smul_neg, ih])
    (fun x y ihx ihy => by beta_reduce; rw [TensorProductFinsupp.smul_add, ihx, ihy])

protected theorem add_smul (r₁ r₂ : R) (x : TensorProductFinsupp R M N) :
    (r₁ + r₂) • x = r₁ • x + r₂ • x :=
  TensorProductFinsupp.induction_on' (motive := fun x => (r₁ + r₂) • x = r₁ • x + r₂ • x) x
    (by beta_reduce; rw [TensorProductFinsupp.smul_zero, TensorProductFinsupp.smul_zero,
      TensorProductFinsupp.smul_zero, add_zero])
    (fun m n => by beta_reduce; rw [smul_tmul', smul_tmul', smul_tmul', add_smul, add_tmul])
    (fun x ih => by beta_reduce at ih ⊢; rw [TensorProductFinsupp.smul_neg, ih, neg_add,
      TensorProductFinsupp.smul_neg, TensorProductFinsupp.smul_neg])
    (fun x y ihx ihy => by beta_reduce at ihx ihy ⊢; rw [TensorProductFinsupp.smul_add, ihx, ihy,
      TensorProductFinsupp.smul_add, TensorProductFinsupp.smul_add, add_add_add_comm])

protected theorem neg_smul (r : R) (x : TensorProductFinsupp R M N) : (-r) • x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← TensorProductFinsupp.add_smul, add_left_neg, TensorProductFinsupp.zero_smul]

instance leftDistribMulAction : DistribMulAction R (TensorProductFinsupp R M N) :=
  { smul_add := fun r x y => TensorProductFinsupp.smul_add r x y
    mul_smul := fun r s x =>
      TensorProductFinsupp.induction_on' (motive := fun x => (r * s) • x = r • (s • x)) x
        (by beta_reduce; (iterate 3 rewrite [TensorProductFinsupp.smul_zero]); with_reducible rfl)
        (fun m n => by beta_reduce; rw [smul_tmul', smul_tmul', smul_tmul', mul_smul])
        (fun x ih => by
          beta_reduce at ih ⊢
          iterate 3 rewrite [TensorProductFinsupp.smul_neg]
          rw [ih])
        (fun x y ihx ihy => by
          beta_reduce at ihx ihy ⊢
          iterate 3 rewrite [TensorProductFinsupp.smul_add]
          rw [ihx, ihy])
    one_smul := TensorProductFinsupp.one_smul
    smul_zero := TensorProductFinsupp.smul_zero }

instance leftModule : Module R (TensorProductFinsupp R M N) where
  add_smul := TensorProductFinsupp.add_smul
  zero_smul := TensorProductFinsupp.zero_smul

namespace BilinearMap

variable (f : M →ₗ[R] N →ₗ[R] P)

def toAddMonoidHom : M →+ N →+ P where
  toFun m := (f m).toAddMonoidHom
  map_zero' := by beta_reduce; rewrite [f.map_zero]; rfl
  map_add' x y := by rewrite [ZeroHom.toFun_eq_coe, ZeroHom.coe_mk, f.map_add]; rfl

def balanced (f : M →ₗ[R] N →ₗ[R] P) (r : R) (m : M) (n : N) :
    f (r • m) n = f m (r • n) := by
  rw [map_smul, map_smul, LinearMap.smul_apply]

end BilinearMap

open BilinearMap in
def lift (f : M →ₗ[R] N →ₗ[R] P) : TensorProductFinsupp R M N →ₗ[R] P := {
  Balanced.lift (toAddMonoidHom f) (balanced f) with
  map_add' := fun x y => by rw [AddMonoidHom.map_add']
  map_smul' := fun r x => by
    dsimp
    refine TensorProductFinsupp.induction_on' (motive := fun x =>
        Balanced.lift (toAddMonoidHom f) (balanced f) (r • x) =
          r • Balanced.lift (toAddMonoidHom f) (balanced f) x)
        x ?_ (fun m n => ?_) (fun x ih => ?_) (fun x y ihx ihy => ?_)
    . beta_reduce
      rw [smul_zero, AddMonoidHom.map_zero, smul_zero]
    . beta_reduce
      rewrite [Balanced.lift_tmul (toAddMonoidHom f) (balanced f),
        smul_tmul', Balanced.lift_tmul (toAddMonoidHom f) (balanced f)]
      exact LinearMap.map_smul₂ f r m n
    . beta_reduce
      rw [smul_neg, AddMonoidHom.map_neg, AddMonoidHom.map_neg, smul_neg, ih]
    . beta_reduce
      rw [smul_add, AddMonoidHom.map_add, AddMonoidHom.map_add, smul_add, ihx, ihy]
}

@[simp]
theorem lift_tmul {f : M →ₗ[R] N →ₗ[R] P} (m : M) (n : N) :
    lift f (tmul R m n) = f m n := by
  rewrite [← Finsupp.lift.single_one _ ℤ (M × N) (fun mn => f mn.1 mn.2) (m, n)]
  rfl

variable (R) (M) (N) in
def mk : M →ₗ[R] N →ₗ[R] TensorProductFinsupp R M N := LinearMap.mk₂ R
  (fun m => Balanced.mk R M N m)
  (fun m₁ m₂ n => AddMonoidHom.map_mul₂ (Balanced.mk R M N) m₁ m₂ n)
  (fun r m n => by dsimp; rw [smul_tmul'])
  (fun r m n => by dsimp; rw [tmul_add])
  (fun r m n => by dsimp; rw [smul_tmul', tmul_smul])

theorem mk_apply (m : M) (n : N) : mk R M N m n = tmul R m n := rfl

def ext' {g h : TensorProductFinsupp R M N →ₗ[R] P}
    (H : ∀ (x : M) (y : N), g (tmul R x y) = h (tmul R x y)) : g = h :=
  have : g.toAddMonoidHom = h.toAddMonoidHom := TensorProductFinsupp.Balanced.ext' H
  LinearMap.ext fun x => FunLike.ext_iff.mp this x

theorem lift.unique {f : M →ₗ[R] N →ₗ[R] P} {g : TensorProductFinsupp R M N →ₗ[R] P}
    (H : ∀ x y, g (tmul R x y) = f x y) : g = lift f :=
  ext' fun m n => by rw [H, lift_tmul]

theorem lift_mk : lift (mk R M N) = LinearMap.id :=
  Eq.symm <| lift.unique fun _ _ => rfl

theorem lift_compr₂ {f : M →ₗ[R] N →ₗ[R] P} (g : P →ₗ[R] Q) : lift (f.compr₂ g) = g.comp (lift f) :=
  Eq.symm <| lift.unique fun _ _ => by simp [lift_tmul]

theorem lift_mk_compr₂ (f : TensorProductFinsupp R M N →ₗ[R] P) :
    lift ((mk R M N).compr₂ f) = f := by
  rw [lift_compr₂ f, lift_mk, LinearMap.comp_id]

theorem lift_eq_mk' :
    (Finsupp.lift _ ℤ (M × N) (fun x => tmul R x.fst x.snd) :
        (M × N →₀ ℤ) →+ TensorProductFinsupp R M N) =
      (QuotientAddGroup.mk' (Null R M N)) := by
  ext
  rewrite [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, AddMonoidHom.coe_coe,
    Finsupp.lift.single_one]
  rfl

theorem lift_eq_mk'' (x : M × N →₀ ℤ) :
    Finsupp.lift _ ℤ (M × N) (fun x => tmul R x.fst x.snd) x =
      QuotientAddGroup.mk' (Null R M N) x := by
  rewrite [← lift_eq_mk']
  rfl

variable (R) (M) (N) in
protected def Equiv : TensorProductFinsupp R M N ≃ₗ[R] TensorProduct R M N :=
  LinearEquiv.ofLinear
    (TensorProductFinsupp.lift <| TensorProduct.mk R M N)
    (TensorProduct.lift <| TensorProductFinsupp.mk R M N)
    (TensorProduct.ext' fun m n => by
      rw [LinearMap.id_apply, LinearMap.comp_apply, TensorProduct.lift.tmul,
        mk_apply, lift_tmul, TensorProduct.mk_apply])
    (TensorProductFinsupp.ext' fun m n => by
      rw [LinearMap.id_apply, LinearMap.comp_apply, TensorProductFinsupp.lift_tmul,
        TensorProduct.mk_apply, TensorProduct.lift.tmul, mk_apply])

@[simp]
protected def Equiv_apply (x : TensorProductFinsupp R M N) :
    TensorProductFinsupp.Equiv R M N x =
      TensorProductFinsupp.lift (TensorProduct.mk R M N) x := rfl

@[simp]
protected def Equiv_symm_apply (x : TensorProduct R M N) :
    (TensorProductFinsupp.Equiv R M N).symm x =
      TensorProduct.lift (TensorProductFinsupp.mk R M N) x := rfl

variable (R) in
theorem tmul_equiv_tmul (m : M) (n : N) :
    m ⊗ₜ[R] n = TensorProductFinsupp.Equiv R M N (TensorProductFinsupp.tmul R m n) := by
  rw [TensorProductFinsupp.Equiv_apply, lift_tmul, TensorProduct.mk_apply]

variable (R) in
theorem mk_equiv_mk : TensorProduct.mk R M N =
    (TensorProductFinsupp.mk R M N).compr₂ (TensorProductFinsupp.Equiv R M N) := by
  ext
  rw [LinearMap.compr₂_apply, LinearEquiv.coe_coe, TensorProductFinsupp.Equiv_apply, mk_apply,
    lift_tmul]

variable (M) in
def lTensor (f : N →ₗ[R] P) : TensorProductFinsupp R M N →ₗ[R] TensorProductFinsupp R M P :=
  lift ((TensorProductFinsupp.mk R M P).compl₂ f)

@[simp]
theorem lTensor_tmul (f : N →ₗ[R] P) (m : M) (n : N) :
    lTensor M f (TensorProductFinsupp.tmul R m n) = TensorProductFinsupp.tmul R m (f n) := by
  unfold lTensor
  rewrite [lift_tmul]
  rfl

theorem lTensor_mk' (x : M × N →₀ ℤ) (f : N →ₗ[R] P) :
    lTensor M f (QuotientAddGroup.mk' _ x) =
      Finsupp.lift (TensorProductFinsupp R M P) ℤ (M × N)
        (fun x : M × N => tmul R x.fst (f x.snd)) x := by
  rewrite [Finsupp.lift_apply]
  rfl

theorem lTensor_equiv (f : N →ₗ[R] P) : (f.lTensor M) ∘ₗ TensorProductFinsupp.Equiv R M N =
    TensorProductFinsupp.Equiv R M P ∘ₗ (lTensor M f) := by
  refine TensorProductFinsupp.ext' fun m n => ?_
  simp? says simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      TensorProductFinsupp.Equiv_apply, lift_tmul, TensorProduct.mk_apply, LinearMap.lTensor_tmul,
      lTensor_tmul]

theorem lTensor_equiv' (f : N →ₗ[R] P) (x : TensorProductFinsupp R M N) :
    (f.lTensor M) (TensorProductFinsupp.Equiv R M N x) =
      TensorProductFinsupp.Equiv R M P (lTensor M f x) := by
  rw [← LinearEquiv.coe_coe, ← LinearMap.comp_apply, ← LinearEquiv.coe_coe,
    ← LinearMap.comp_apply, lTensor_equiv]

variable (M)

/-- `lEmbed M h`, where `h` is a proof that the `R`-linear map `f : N → P` is injective,
is the function on the free abelian group that lifts to `lTensor M f`. -/
def lEmbed {f : N →ₗ[R] P} (h : Function.Injective f) : (M × N →₀ ℤ) → M × P →₀ ℤ :=
  Finsupp.embDomain ⟨_, Function.Injective.Prod_map Function.injective_id h⟩

theorem mk'_lEmbed {f : N →ₗ[R] P} (h : Function.Injective f) (x : M × N →₀ ℤ) :
    QuotientAddGroup.mk' (TensorProductFinsupp.Null R M P) (lEmbed M h x) =
      TensorProductFinsupp.lTensor M f (QuotientAddGroup.mk' _ x) := by
  unfold lEmbed
  rw [TensorProductFinsupp.lTensor_mk', ← TensorProductFinsupp.lift_eq_mk'', Finsupp.lift_apply,
    ← Finsupp.total_apply, Finsupp.total_embDomain]
  rfl

def lEmbed_comap {f : N →ₗ[R] P} (h : Function.Injective f) (x : M × P →₀ ℤ) : M × N →₀ ℤ :=
  Finsupp.comapDomain _ x ((Function.Injective.Prod_map Function.injective_id h).injOn _)

theorem lEmbed_comp {g : P →ₗ[R] Q} {f : M →ₗ[R] P}
    (hg : Function.Injective g) (hf : Function.Injective f) :
      lEmbed N (id (hg.comp hf) : Function.Injective (g ∘ₗ f)) = lEmbed N hg ∘ lEmbed N hf := by
  unfold lEmbed
  ext x a
  rw [Finsupp.embDomain_eq_mapDomain, Function.comp_apply, Finsupp.embDomain_eq_mapDomain,
    Finsupp.embDomain_eq_mapDomain]
  erw [← Finsupp.mapDomain_comp]
  rfl

variable {M}

variable (N) in
def rTensor (f : M →ₗ[R] P) :
    TensorProductFinsupp R M N →ₗ[R] TensorProductFinsupp R P N :=
  lift ((TensorProductFinsupp.mk R P N).comp f)

@[simp]
theorem rTensor_tmul (f : M →ₗ[R] P) (m : M) (n : N) :
    rTensor N f (TensorProductFinsupp.tmul R m n) = TensorProductFinsupp.tmul R (f m) n := by
  unfold rTensor
  rewrite [lift_tmul]
  rfl

theorem rTensor_mk' (x : M × N →₀ ℤ) (f : M →ₗ[R] P) :
    rTensor N f (QuotientAddGroup.mk' _ x) =
      Finsupp.lift (TensorProductFinsupp R P N) ℤ (M × N)
        (fun x : M × N => tmul R (f x.fst) x.snd) x := by
  rewrite [Finsupp.lift_apply]
  rfl

theorem rTensor_equiv (f : M →ₗ[R] P) : (f.rTensor N) ∘ₗ TensorProductFinsupp.Equiv R M N =
    TensorProductFinsupp.Equiv R P N ∘ₗ (rTensor N f) := by
  refine TensorProductFinsupp.ext' fun m n => ?_
  simp? says simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      TensorProductFinsupp.Equiv_apply, lift_tmul, TensorProduct.mk_apply, LinearMap.rTensor_tmul,
      rTensor_tmul]

theorem rTensor_equiv' (f : M →ₗ[R] P) (x : TensorProductFinsupp R M N) :
    (f.rTensor N) (TensorProductFinsupp.Equiv R M N x) =
      TensorProductFinsupp.Equiv R P N (rTensor N f x) := by
  rw [← LinearEquiv.coe_coe, ← LinearMap.comp_apply, ← LinearEquiv.coe_coe,
    ← LinearMap.comp_apply, rTensor_equiv]

variable (N)

/-- `rEmbed N h`, where `h` is a proof that the `R`-linear map `f : M → P` is injective,
is the function on the free abelian group that lifts to `rTensor N f`. -/
def rEmbed {f : M →ₗ[R] P} (h : Function.Injective f) : (M × N →₀ ℤ) → P × N →₀ ℤ :=
  Finsupp.embDomain ⟨_, Function.Injective.Prod_map h Function.injective_id⟩

theorem mk'_rEmbed {f : M →ₗ[R] P} (h : Function.Injective f) (x : M × N →₀ ℤ) :
    QuotientAddGroup.mk' (TensorProductFinsupp.Null R P N) (rEmbed N h x)
      = TensorProductFinsupp.rTensor N f (QuotientAddGroup.mk' _ x) := by
  unfold rEmbed
  rw [TensorProductFinsupp.rTensor_mk', ← TensorProductFinsupp.lift_eq_mk'', Finsupp.lift_apply,
    ← Finsupp.total_apply, Finsupp.total_embDomain]
  rfl

def rEmbed_comap {f : M →ₗ[R] P} (h : Function.Injective f) (x : P × N →₀ ℤ) : M × N →₀ ℤ :=
  Finsupp.comapDomain _ x ((Function.Injective.Prod_map h Function.injective_id).injOn _)

theorem rEmbed_comp {g : P →ₗ[R] Q} {f : M →ₗ[R] P}
    (hg : Function.Injective g) (hf : Function.Injective f) :
      rEmbed N (id (hg.comp hf) : Function.Injective (g ∘ₗ f)) = rEmbed N hg ∘ rEmbed N hf := by
  unfold rEmbed
  ext x a
  rw [Finsupp.embDomain_eq_mapDomain, Function.comp_apply, Finsupp.embDomain_eq_mapDomain,
    Finsupp.embDomain_eq_mapDomain]
  erw [← Finsupp.mapDomain_comp]
  rfl

theorem rEmbed_comap_map {ψ : M →ₗ[R] P} (hψ : Function.Injective ψ) (x : M × N →₀ ℤ) :
      TensorProductFinsupp.rEmbed_comap N hψ
        (TensorProductFinsupp.rEmbed N hψ x) = x := by
  ext p
  unfold TensorProductFinsupp.rEmbed TensorProductFinsupp.rEmbed_comap
  rw [Finsupp.comapDomain_apply, Finsupp.embDomain_eq_mapDomain, Function.Embedding.coeFn_mk,
    Finsupp.mapDomain_apply (hψ.Prod_map Function.injective_id)]

theorem rEmbed_map_comap {L : Submodule R M} {x : M × N →₀ ℤ}
    (hmem : ∀ y, y ∈ x.support → y.fst ∈ L) :
      TensorProductFinsupp.rEmbed N L.injective_subtype
        (TensorProductFinsupp.rEmbed_comap N L.injective_subtype x) = x := by
  unfold TensorProductFinsupp.rEmbed TensorProductFinsupp.rEmbed_comap
  rewrite [Finsupp.embDomain_eq_mapDomain]
  have hSurjOn : Set.SurjOn (Prod.map L.subtype id)
      ((Prod.map L.subtype id) ⁻¹' x.support) (x.support : Set (M × N)) :=
    fun y hy => ⟨(⟨y.fst, hmem y hy⟩, y.snd), by exact hy, rfl⟩
  erw [Finsupp.mapDomain_comapDomain _ (L.injective_subtype.Prod_map Function.injective_id) x
    hSurjOn.subset_range]

theorem rEmbed_map_comap' {J K : Submodule R M} (hJK : J ≤ K) {x : K × N →₀ ℤ}
    (hmem : ∀ y, y ∈ x.support → y.fst.val ∈ J) :
      rEmbed N (J.inclusion_injective hJK)
        (rEmbed_comap N (J.inclusion_injective hJK) x) = x := by
  unfold rEmbed TensorProductFinsupp.rEmbed_comap
  rewrite [Finsupp.embDomain_eq_mapDomain]
  have hSurjOn : Set.SurjOn (Prod.map (J.inclusion hJK) id)
      ((Prod.map (J.inclusion hJK) id) ⁻¹' (x.support : Set (K × N)))
        (x.support : Set (K × N)) :=
    fun y hy => ⟨(⟨y.fst.val, hmem y hy⟩, y.snd), by exact hy, rfl⟩
  erw [Finsupp.mapDomain_comapDomain _
    ((J.inclusion_injective hJK).Prod_map Function.injective_id) x hSurjOn.subset_range]

variable {N}

theorem _root_.Finsupp.lift_comp (S : Type*) [Semiring S] (M : Type*) [AddCommGroup M] [Module S M]
    (N : Type*) [AddCommGroup N] [Module S N] (P : Type*) [AddCommGroup P] [Module S P]
      (f : M → N) (g : N → P) (x : M →₀ S) :
        Finsupp.lift P S M (g ∘ f) x = Finsupp.lift P S N g (Finsupp.mapDomain f x) := by
  simp_rw [Finsupp.lift_apply, ← Finsupp.total_apply, Finsupp.total_mapDomain]

theorem total_eq_mk' :
    (Finsupp.total (M × N) _ ℤ (fun x => tmul R x.fst x.snd) :
        (M × N →₀ ℤ) →+ TensorProductFinsupp R M N) =
      QuotientAddGroup.mk' (Null R M N) := by
  ext
  rewrite [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, AddMonoidHom.coe_coe,
    Finsupp.total_single, one_smul]
  rfl

theorem ker_eq : Null R M N =
    (AddMonoidHom.ker <| AddMonoidHomClass.toAddMonoidHom <|
      Finsupp.lift _ ℤ _ fun x : M × N => tmul R x.fst x.snd) := by
  rewrite [lift_eq_mk']
  exact AddSubgroup.ext fun x => (QuotientAddGroup.eq_zero_iff x).symm

theorem tmul_null (x : M × N →₀ ℤ) :
    x ∈ Null R M N ↔ Finsupp.lift _ ℤ (M × N) (fun x => tmul R x.fst x.snd) x = 0 := by
  rw [ker_eq]
  exact Iff.rfl

end TensorProductFinsupp
end
