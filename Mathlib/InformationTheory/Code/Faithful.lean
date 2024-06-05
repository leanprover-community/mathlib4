import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Ring.BooleanRing


-- instance {G α β : Type*} [Monoid G] [Monoid β] [MulAction G α] :
--     MulDistribMulAction (Gᵈᵐᵃ) (α → β) where
--   smul_mul _ _ _ := funext fun _ => rfl
--   smul_one _ := funext fun _ => rfl

-- variable {K:Type*} {ι:Type*} [Monoid K]

-- def f : (ι ≃ ι)ᵐᵒᵖ →* MulAut (ι → Kˣ) := MulDistribMulAction.toMulAut (ι ≃ ι)ᵈᵐᵃ (ι → Kˣ)
section
variable {K M :Type*} [Ring K] [AddCommMonoid M] [Module K M] [Nontrivial M]
  [NoZeroSMulDivisors K M]


instance instFaithfulVectorspace : FaithfulSMul K M where
  eq_of_smul_eq_smul{m1 m2} := fun h => by
    obtain ⟨x,hx⟩ := exists_ne (0: M)
    specialize h x
    have foo : (m1 - m2) • x = 0 := calc
      (m1 - m2) • x
        = (m1 + -m2) • x := by
        rw [sub_eq_add_neg]
      _ = m1 • x + (-m2) • x := by rw [add_smul]
      _ = m2 • x + (-m2) • x := by rw [h]
      _ = (m2 + - m2) • x := by rw [add_smul]
      _ = (m2 - m2) • x:= by rw [sub_eq_add_neg]
      _ = 0 := by rw [sub_self, zero_smul]
    rw [smul_eq_zero] at foo
    rw [← sub_eq_zero]
    exact foo.resolve_right hx

end

section
variable {G M K:Type*} [Semiring K]

-- #synth IsScalarTower (RingAut K) K K
-- #synth SMulCommClass (RingAut K) K K

instance Units.instMulDistribMulAction' [Monoid G] [Monoid M] [MulDistribMulAction G M] : MulDistribMulAction G Mˣ where
  smul g u := ⟨g • u, g • u⁻¹,
    by rw [← smul_mul', Units.mul_inv, smul_one],
    by rw [← smul_mul', Units.inv_mul, smul_one]⟩
  one_smul u := Units.ext <| one_smul _ _
  mul_smul g₁ g₂ u := Units.ext <| mul_smul _ _ _
  smul_mul g u₁ u₂ := Units.ext <| smul_mul' _ _ _
  smul_one g := Units.ext <| smul_one _

@[simp]
lemma Units.smul_val_eq_val_smul [Monoid G] [Monoid M] [MulDistribMulAction G M] (g : G) (u : Mˣ):
  g • (u : M) = (g • u : Mˣ) := rfl

end
section
variable {K : Type*} [Field K] {I:Type*}

end

section

class SMulDistribSMulClass (A B C:Type*) [SMul A B] [SMul A C] [SMul B C] : Prop where
  smul_distrib (a:A) (b:B) (c:C) : a • (b • c) = (a • b) • (a • c)

instance MulDistribMulAction.instSMulDistribSmulClass (A B : Type*)
    [Monoid A] [Monoid B] [MulDistribMulAction A B] :
    SMulDistribSMulClass A B B where
  smul_distrib a b₁ b₂ := by
    simp only [smul_eq_mul, smul_mul']

def DistribMulAction.toSemilinearAut (R:Type*) [Semiring R] (M:Type*) [AddCommMonoid M] [Module R M]
    {S:Type*} [Group S] [DistribMulAction S M] [MulSemiringAction S R]
    [SMulDistribSMulClass S R M] (s:S) :
    letI inst := RingHomInvPair.of_ringEquiv (MulSemiringAction.toRingEquiv S R s);
    letI := inst.symm;
    M ≃ₛₗ[(MulSemiringAction.toRingEquiv S R s : R →+* R)] M :=
    letI inst := RingHomInvPair.of_ringEquiv (MulSemiringAction.toRingEquiv S R s);
    letI := inst.symm;
    {
      DistribMulAction.toAddEquiv M s with
      map_smul' := fun r x => by
        simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          DistribMulAction.toAddEquiv_apply, RingHom.coe_coe, MulSemiringAction.toRingEquiv_apply]
        exact SMulDistribSMulClass.smul_distrib s r x
    }

instance Pi.instSMulDistribSMulClass (I A B : Type*) (C:I → Type*) [SMul A B]
    [∀ i, SMul A (C i)] [∀ i, SMul B (C i)] [∀ i,SMulDistribSMulClass A B (C i)]:
    SMulDistribSMulClass A B ((i:I) → C i) where
  smul_distrib a b c := by
    ext i
    simp only [Pi.smul_apply]
    rw [SMulDistribSMulClass.smul_distrib]

instance Pi.instSMulDistribSMulClass' (I A : Type*) (B C: I → Type*)
    [∀ i, SMul A (B i)] [∀ i, SMul A (C i)] [∀ i, SMul (B i) (C i)]
    [∀ i, SMulDistribSMulClass A (B i) (C i)] :
    SMulDistribSMulClass A ((i:I) → B i) ((i:I) → C i) where
  smul_distrib a b c := by
    ext i
    simp only [Pi.smul_apply, Pi.smul_apply']
    rw [SMulDistribSMulClass.smul_distrib]

instance Pi.instSMulDistribSMulClass'' (I : Type*) (A B C: I → Type*)
    [∀ i, SMul (A i) (B i)] [∀ i, SMul (A i) (C i)] [∀ i, SMul (B i) (C i)]
    [∀ i, SMulDistribSMulClass (A i) (B i) (C i)] :
    SMulDistribSMulClass ((i:I) → A i) ((i:I) → B i) ((i:I) → C i) where
  smul_distrib a b c := by
    ext i
    simp only [Pi.smul_apply']
    rw [SMulDistribSMulClass.smul_distrib]

end

section
variable {A B C: Type*} [Monoid A] [Monoid B] [SMul A C] [SMul B C] [SMulCommClass A B C]
instance Prod.smul': SMul (A × B) C where
  smul x c := x.fst • x.snd • c

@[simp]
lemma Prod.smul_def' (x:A × B) (c:C) : x • c = x.fst • x.snd • c := rfl

end

section
variable {A B C: Type*} [Monoid A] [Monoid B] [MulAction A C] [MulAction B C]
  [SMulCommClass A B C]

instance Prod.mulAction': MulAction (A × B) C where
  one_smul := fun b => by
    simp only [Prod.smul_def', fst_one, snd_one, one_smul]
  mul_smul := fun x y b => by
    simp only [Prod.smul_def', fst_mul, snd_mul, mul_smul]
    rw [smul_comm y.1]

end


section
variable {A B C:Type*} [Monoid A] [Monoid B] [Monoid C]
  [MulDistribMulAction A C] [MulDistribMulAction B C]
  [SMulCommClass A B C]

instance Prod.mulDistribMulAction' : MulDistribMulAction (A × B) C where
  smul_mul := fun r x y => by
    simp_rw [HSMul.hSMul]
    suffices hsuf : (r.1 • r.2 • (x * y)) = r.1 • r.2 • x * (r.1 • r.2 • y) by
      exact hsuf
    simp only [smul_mul']
  smul_one := fun r => by
    simp_rw [HSMul.hSMul]
    suffices hsuf : r.1 • r.2 • (1:C) = 1 by
      exact hsuf
    simp only [smul_one]

end

section
variable {A B C:Type*} [Monoid A] [Monoid B] [AddMonoid C]
  [DistribMulAction A C] [DistribMulAction B C]
  [SMulCommClass A B C]

instance Prod.distribMulAction' : DistribMulAction (A × B) C where
  smul_add := fun r x y => by
    simp_rw [HSMul.hSMul]
    suffices hsuf : (r.1 • r.2 • (x + y)) = r.1 • r.2 • x + (r.1 • r.2 • y) by
      exact hsuf
    simp only [smul_add]
  smul_zero := fun r => by
    simp_rw [HSMul.hSMul]
    suffices hsuf : r.1 • r.2 • (0:C) = 0 by
      exact hsuf
    simp only [smul_zero]
end

section
variable {A B C D:Type*} [Monoid A] [Monoid B] [Monoid C] [AddMonoid C]
  [SMul A C] [SMul B C] [SMul A D] [SMul B D] [SMul C D]
  [SMulDistribSMulClass A C D]
  [SMulDistribSMulClass B C D]
  -- [SMulCommClass A B C]

instance Prod.smulDistribSMulClass : SMulDistribSMulClass (A × B) C D where
  smul_distrib := fun x b c => by
    calc
      x • b • c
        = x.fst • x.snd • b • c := by rw [Prod.smul_def']
      _ = x.fst • (x.snd • b) • (x.snd • c) := by
        rw [SMulDistribSMulClass.smul_distrib x.snd]
      _ = (x.fst • x.snd • b) • (x.fst • x.snd • c) := by
        rw [SMulDistribSMulClass.smul_distrib x.fst]
      _ = (x • b) • (x • c) := by rw [Prod.smul_def',Prod.smul_def']
end

section
variable {A B C :Type*}
  [Group A]
  [CommGroup B]
  [AddMonoid C]
  [MulDistribMulAction A B] [DistribMulAction B C]
  [DistribMulAction A C]

  [SMulDistribSMulClass A B C]

example : Type _ := B ⋊[MulDistribMulAction.toMulAut A B] A

abbrev invsmulMulHom : Aᵐᵒᵖ →* (MulAut B) where
  toFun := fun a => MulDistribMulAction.toMulAut A B (MulOpposite.unop a)⁻¹
  map_one' := by
    simp only [MulOpposite.unop_one, inv_one, map_one]
  map_mul' := fun x y => by
    simp only
    rw [MulOpposite.unop_mul,mul_inv_rev,map_mul]


instance semiproductmulaction: MulAction (B ⋊[invsmulMulHom] Aᵐᵒᵖ)ᵐᵒᵖ C where
  smul := fun x c => x.unop.right.unop • x.unop.left • c
  one_smul := fun c => by
    simp_rw [HSMul.hSMul]
    simp only [MulOpposite.unop_one, SemidirectProduct.one_right, SemidirectProduct.one_left]
    suffices hsuf : (1:A) • (1:B) • c = c by
      exact hsuf
    simp only [one_smul]
  mul_smul := fun x₁ x₂ c => by
    simp_rw [HMul.hMul,Mul.mul,HMul.hMul,Mul.mul,HSMul.hSMul]
    simp only [MulDistribMulAction.toMulAut_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      SemidirectProduct.mk_eq_inl_mul_inr, map_mul, MulOpposite.op_mul, MulOpposite.unop_mul,
      MulOpposite.unop_op, SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one,
      SemidirectProduct.right_inr, one_mul, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      map_one, MulAut.one_apply, SemidirectProduct.left_inr]
    obtain a₁ := x₁.unop.right.unop
    obtain a₂ := x₂.unop.right.unop
    obtain b₁ := x₁.unop.left
    obtain b₂ := x₂.unop.left
    calc
      (a₁ * a₂) • (b₂ * a₂⁻¹ • b₁) • c
      _ = a₁ • a₂ • (b₂ * a₂⁻¹ • b₁) • c := by rw [mul_smul]
      _ = a₁ • a₂ • (a₂⁻¹ • b₁ * b₂) • c := by rw [mul_comm]
      _ = a₁ • a₂ • (a₂⁻¹ • b₁) • b₂ • c := by rw [mul_smul]
      _ = a₁ • (a₂ • a₂⁻¹ • b₁) • a₂ • b₂ • c := by rw [← SMulDistribSMulClass.smul_distrib]
      _ = a₁ • ((a₂ * a₂⁻¹) • b₁) • a₂ • b₂ • c := by rw [mul_smul]
      _ = a₁ • b₁ • a₂ • b₂ • c := by rw [mul_right_inv, one_smul]

@[simp]
lemma semiprod_mulact_apply (x:(B ⋊[invsmulMulHom] Aᵐᵒᵖ)ᵐᵒᵖ) (c:C) :
    x • c = x.unop.right.unop • x.unop.left • c := rfl


end


section
variable {N G H : Type*} [Group N] [Group G] [Group H] {φ : G →* MulAut N}
namespace SemidirectProduct
protected lemma induction {motive : N ⋊[φ] G → Prop} (x : N ⋊[φ] G)
    (left : ∀ n, motive (inl n))
    (right : ∀ g, motive (inr g))
    (mul : ∀ (n : N) (g : G), motive (inl n) → motive (inr g) → motive (inl n * inr g)) :
    motive x := by
  obtain ⟨x₁,x₂⟩ := x
  simp only [mk_eq_inl_mul_inr]
  exact mul _ _ (left x₁) (right x₂)

variable {f₁ : N →* H} {f₂ : G →* H}
  {h:∀ (g : G),
    f₁.comp (MulEquiv.toMonoidHom (φ g)) = (MulEquiv.toMonoidHom (MulAut.conj (f₂ g))).comp f₁}

lemma lift_inj
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂)
    (hindep : f₁.range ⊓ f₂.range = ⊥):
    Function.Injective (lift f₁ f₂ h) := by
  rw [← MonoidHom.ker_eq_bot_iff] at hf₁ hf₂ ⊢
  rw [Subgroup.eq_bot_iff_forall] at hf₁ hf₂ ⊢
  rw [Subgroup.eq_bot_iff_forall] at hindep
  simp only [MonoidHom.mem_ker] at hf₁ hf₂ ⊢
  intro x
  induction x using SemidirectProduct.induction
  . simp only [lift_inl]
    intro h
    specialize hf₁ _ h
    rw [hf₁]
    simp only [map_one]
  . simp only [lift_inr]
    intro h
    specialize hf₂ _ h
    rw [hf₂]
    simp only [map_one]
  . rename_i n g hn hg
    simp only [lift_inl, lift_inr, map_mul] at hn hg ⊢
    intro hmul_one
    rw [← eq_inv_iff_mul_eq_one,← map_inv] at hmul_one ⊢
    have hn_one: f₁ n = 1 := by
      apply hindep (f₁ n)
      simp only [Subgroup.mem_inf, MonoidHom.mem_range, exists_apply_eq_apply, true_and]
      use g⁻¹
      exact hmul_one.symm
    have hg_one : f₂ g = 1 := by
      rw [hn_one,map_inv,← inv_eq_iff_eq_inv,inv_one] at hmul_one
      exact hmul_one.symm
    specialize hf₁ n hn_one
    specialize hf₂ g hg_one
    rw [hf₁,hf₂,inv_one,map_one,map_one]


lemma eq_closure_of_orbit_closure {sg : Set G} (n : N)
    (hsg_gen : ⊤ ≤ Subgroup.closure sg)
    (horbit_gen : ⊤ ≤ Subgroup.closure ((φ . n) '' ⊤)) :
    (⊤  : Subgroup (N ⋊[φ] G)) ≤ Subgroup.closure ({inl n} ∪ inr '' sg) := by
  intro i
  simp only [Subgroup.mem_top, Set.singleton_union, true_implies]
  have right_subgroup : Subgroup.closure (inr '' sg : Set (N ⋊[φ] G)) ≤ Subgroup.closure ({inl n} ∪ inr '' sg) := by
    apply Subgroup.closure_mono
    exact Set.subset_union_right {inl n} (⇑inr '' sg)
  have right_subgroup_eq : Subgroup.closure (inr '' sg : Set (N ⋊[φ] G)) = inr.range := by
    apply le_antisymm
    . intro i hi
      simp only [MonoidHom.mem_range]
      refine Subgroup.closure_induction hi ?_ ?_ ?_ ?_
      . rintro _ ⟨g,_,rfl⟩
        use g
      . use 1
        rw [map_one]
      . rintro _ _ ⟨g1,rfl⟩ ⟨g2,rfl⟩
        use g1 * g2
        rw [map_mul]
      . rintro _ ⟨g,rfl⟩
        use g⁻¹
        rw [map_inv]
    . rintro _ ⟨g,_,rfl⟩
      have g_mem_clos : g ∈ Subgroup.closure sg := by exact hsg_gen trivial
      refine Subgroup.closure_induction g_mem_clos ?_ ?_ ?_ ?_
      . intro g hg
        apply Subgroup.subset_closure
        simp only [Set.mem_image, inr_inj, exists_eq_right]
        exact hg
      . rw [map_one]
        exact Subgroup.one_mem (Subgroup.closure (⇑inr '' sg))
      . intro x y hx hy
        rw [map_mul]
        exact Subgroup.mul_mem _ hx hy
      . intro x hx
        rw [map_inv]
        exact Subgroup.inv_mem _ hx
  apply SemidirectProduct.induction i
  . intro n'
    have hmem_orbit : n' ∈ Subgroup.closure ((φ . n) '' ⊤) := horbit_gen trivial
    refine Subgroup.closure_induction hmem_orbit ?_ ?_ ?_ ?_
    . intro x hx
      simp only [Set.top_eq_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨g,rfl⟩ := hx
      rw [inl_aut]
      apply Subgroup.mul_mem _
      apply Subgroup.mul_mem _
      . apply right_subgroup
        rw [right_subgroup_eq]
        simp only [MonoidHom.mem_range, inr_inj, exists_eq]
      . apply Subgroup.subset_closure
        simp only [Set.mem_insert_iff, Set.mem_image, true_or]
      . apply right_subgroup
        rw [right_subgroup_eq]
        simp only [map_inv, inv_mem_iff, MonoidHom.mem_range, inr_inj, exists_eq]
    . rw [map_one]
      apply Subgroup.one_mem
    . intro x y hx hy
      rw [map_mul]
      exact Subgroup.mul_mem _ hx hy
    . intro x hx
      rw [map_inv]
      exact Subgroup.inv_mem _ hx
  . intro g
    apply right_subgroup
    rw [right_subgroup_eq]
    simp only [MonoidHom.mem_range, inr_inj, exists_eq]
  . intro n g hn hg
    apply Subgroup.mul_mem _ hn hg


end SemidirectProduct
end

section
variable {ι : Type*} {R : ι → Type*} [∀ i, BooleanRing (R i)]

instance Pi.booleanRing: BooleanRing ((i : ι) → R i) where
  mul_self := fun v => by
    ext i
    simp only [Pi.mul_apply, mul_self]

end


section
variable {G α: Type*} [Group G] [MulAction G α]

lemma MulAction.isPretransitive_of_top_le_orbit (a : α) (hletop : ⊤ ≤ MulAction.orbit G a):
    MulAction.IsPretransitive G α where
  exists_smul_eq := fun x y => by
    have hx : x ∈ MulAction.orbit G a := by
      exact hletop trivial
    have hy : y ∈ MulAction.orbit G a := by
      exact hletop trivial
    obtain ⟨gx,hgx⟩ := hx
    obtain ⟨gy,hgy⟩ := hy
    use gy * gx⁻¹
    rw [← hgx]
    simp only
    rw [← mul_smul,mul_assoc,inv_mul_self,mul_one]
    rw [← hgy]

end
