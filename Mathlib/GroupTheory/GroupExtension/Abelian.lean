/-
Copyright (c) 2024 Yudai Yamazaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yudai Yamazaki
-/
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

set_option linter.style.header false in
set_option linter.directoryDependency false in
/-!
# Lemmas about extensions by Abelian groups

This file gives lemmas about group extensions `1 → N → E → G → 1` that hold when `N` is Abelian.

For the main definitions, see `Mathlib/GroupTheory/GroupExtension/Defs.lean`. For basic lemmas about
group extensions in general, see `Mathlib/GroupTheory/GroupExtension/Basic.lean`.

## Main definition

- `SemidirectProduct.conjClassesEquivH1 (φ : G →* MulAut N)`: the bijection between the
  `N`-conjugacy classes of splittings associated to the semidirect product `G ⋊[φ] N` and
  $H^1 (G, N)$

## References

* [Kenneth S. Brown, *Cohomology of groups*][brown1982]

-/

suppress_compilation

namespace SemidirectProduct

variable {N G : Type} [CommGroup N] [Group G] (φ : G →* MulAut N)

/-- The `ℤ`-linear `G`-representation associated to a multiplicative action -/
noncomputable def toRep : Rep ℤ G :=
  @Rep.ofMulDistribMulAction G N _ _ (MulDistribMulAction.compHom N φ)

theorem toRep_ρ_apply_apply (g : G) (n : Additive N) :
    ((toRep φ).ρ g) n = Additive.ofMul (φ g (Additive.toMul n)) := rfl

/-- Returns the 1-cocycle corresponding to a splitting. -/
def splittingToOneCocycle (s : (toGroupExtension φ).Splitting) :
    groupCohomology.oneCocycles (toRep φ) where
  val g := Additive.ofMul (α := N) (s g).left
  property := by
    rw [groupCohomology.mem_oneCocycles_iff]
    intro g₁ g₂
    rw [toRep_ρ_apply_apply, toMul_ofMul, map_mul, mul_left, mul_comm, ← ofMul_mul, right_splitting]

/-- Returns the splitting corresponding to a 1-cocycle. -/
def splittingOfOneCocycle (f : groupCohomology.oneCocycles (toRep φ)) :
    (toGroupExtension φ).Splitting where
  toFun g := ⟨Additive.toMul (f g), g⟩
  map_one' := by
    ext
    · simp only [one_left, groupCohomology.oneCocycles_map_one, toMul_zero]
    · simp only [one_right]
  map_mul' g₁ g₂ := by
    ext
    · simp only [mul_left]
      rw [(groupCohomology.mem_oneCocycles_iff f).mp f.property g₁ g₂, toMul_add, mul_comm,
        toRep_ρ_apply_apply, toMul_ofMul]
    · simp only [mul_right]
  rightInverse_rightHom g := by simp only [toGroupExtension_rightHom, rightHom_eq_right]

/-- The bijection between the splittings of the group extension associated to a semidirect product
  and the 1-cocycles -/
def splittingEquivOneCocycles :
    (toGroupExtension φ).Splitting ≃ groupCohomology.oneCocycles (toRep φ) where
  toFun := splittingToOneCocycle φ
  invFun := splittingOfOneCocycle φ
  left_inv s := by
    unfold splittingToOneCocycle splittingOfOneCocycle
    congr
    ext g
    <;> congr
    <;> exact (s.rightHom_splitting g).symm
  right_inv f := by
    unfold splittingToOneCocycle splittingOfOneCocycle
    ext g
    simp only [mk_eq_inl_mul_inr, GroupExtension.Splitting.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      mul_left, left_inl, right_inl, map_one, left_inr, MulAut.one_apply, mul_one, ofMul_toMul,
      groupCohomology.oneCocycles.coe_mk]

/-- Two splittings are `N`-conjugates iff the difference of the corresponding 1-cocycles is a
  1-coboundary. -/
theorem isConj_iff_sub_mem_oneCoboundaries (s₁ s₂ : (toGroupExtension φ).Splitting) :
    (toGroupExtension φ).IsConj s₁ s₂ ↔
    ⇑(splittingToOneCocycle φ s₁) - splittingToOneCocycle φ s₂ ∈
    groupCohomology.oneCoboundaries (toRep φ) := by
  rw [sub_mem_comm_iff]
  apply Additive.ofMul.exists_congr
  intro n
  rw [funext_iff, funext_iff]
  apply forall_congr'
  intro g
  simp only [toGroupExtension_inl, SemidirectProduct.ext_iff, mul_left, mul_right, inv_left,
    inv_right, right_splitting, left_inl, right_inl, inv_one, map_one, map_inv, MulAut.one_apply,
    one_mul, mul_one, and_true]
  rw [eq_mul_inv_iff_mul_eq, mul_comm, ← eq_mul_inv_iff_mul_eq, mul_assoc, mul_comm,
    ← mul_inv_eq_iff_eq_mul]
  simp only [← div_eq_mul_inv, groupCohomology.dZero_hom_apply, toRep_ρ_apply_apply, toMul_ofMul,
    splittingToOneCocycle, Pi.sub_apply]
  rfl

-- /-- The bijection between the `N`-conjugacy classes of splittings and the first cohomology group
-- -/
-- def conjClassesEquivH1 : (toGroupExtension φ).ConjClasses ≃ groupCohomology.H1 (toRep φ) :=
--   Quotient.congr (splittingEquivOneCocycles φ) (by
--     intro s₁ s₂
--     rw [Submodule.quotientRel_def]
--     exact isConj_iff_sub_mem_oneCoboundaries φ s₁ s₂
--   )

end SemidirectProduct

namespace GroupExtension

section

variable {N E G : Type*} [CommGroup N] [Group E] [Group G] (S : GroupExtension N E G)

/-- A conjugation by `inl n` is trivial for all `n : N`. -/
theorem conjAct_inl (n : N) : S.conjAct (S.inl n) = 1 := by
  ext _
  apply S.inl_injective
  rw [MulAut.one_apply, inl_conjAct_comm]
  simp only [← map_inv, ← map_mul, mul_inv_cancel_comm]

namespace Section

variable {S}
variable (σ : S.Section)

/-- The action of `G` on `N` by conjugation, defined using a section. -/
noncomputable def conjAct : G →* MulAut N where
  toFun g := S.conjAct (σ g)
  map_one' := by
    obtain ⟨n, hn⟩ : σ 1 ∈ S.inl.range := by
      rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, rightHom_section]
    simp only [← hn, conjAct_inl]
  map_mul' g₁ g₂ := by
    ext n
    apply S.inl_injective
    simp only [MulAut.mul_apply, inl_conjAct_comm]
    obtain ⟨n', hn'⟩ := exists_mul_eq_mul_mul_inl σ g₁ g₂
    rw [hn', mul_assoc _ (S.inl n'), ← S.inl.map_mul, mul_comm, map_mul]
    group

/-- The action of `G` on `N` is independent of the choice of section. -/
theorem conjAct_eq (σ' : S.Section) : σ.conjAct = σ'.conjAct := by
  ext1 g
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk]
  obtain ⟨n, hn⟩ := σ.exists_eq_inl_mul σ' g
  simp only [hn, map_mul, conjAct_inl, one_mul]

/-- The inclusion and a conjugation commute. -/
theorem inl_conjAct_comm {g : G} {n : N} :
    S.inl (σ.conjAct g n) = σ g * S.inl n * (σ g)⁻¹ := S.inl_conjAct_comm

theorem conj_eq_of_rightHom_eq_one (σ' : S.Section) (g : G) {e : E} (he : S.rightHom e = 1) :
    σ g * e * (σ g)⁻¹ = (σ' g) * e * (σ' g)⁻¹ := by
  rw [← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom] at he
  obtain ⟨n, rfl⟩ := he
  simpa only [inl_conjAct_comm] using
    DFunLike.congr_arg S.inl <| DFunLike.congr_fun (DFunLike.congr_fun (σ.conjAct_eq σ') g) n

end Section

end

section

variable (N G : Type) [CommGroup N] [Group G] [MulDistribMulAction G N]

/-- Group extensions of `G` by `N` such that the action of `G` on `N` is a conjugation -/
structure ofMulDistribMulAction where
  /-- The type with a group structure associated to the extension -/
  E : Type*
  /-- The group structure associated to the extension -/
  GroupE : Group E
  /-- The group extension -/
  extension : GroupExtension N E G
  /-- `G` acts on `N` by conjugation. -/
  smul_eq_conjAct {g : G} {n : N} (σ : extension.Section) : g • n = σ.conjAct g n

/-- Group extensions with specific choices of sections -/
structure ofMulDistribMulActionWithSection extends ofMulDistribMulAction N G where
  /-- A right inverse to `rightHom` -/
  σ : extension.Section

variable {N G}

namespace ofMulDistribMulAction

variable (S S' : ofMulDistribMulAction N G)
instance : Group S.E := S.GroupE
instance : Group S'.E := S'.GroupE

/-- Two terms of `GroupExtension.ofMulDistribMulAction` are equivalent iff their extensions are. -/
def Equiv := S.extension.Equiv S'.extension

variable (N G)

/-- The setoid on the equivalence of extensions -/
def setoid : Setoid (ofMulDistribMulAction N G) where
  r S S' := Nonempty (S.Equiv S')
  iseqv :=
  { refl := fun S ↦ ⟨GroupExtension.Equiv.refl S.extension⟩
    symm := fun ⟨equiv⟩ ↦ ⟨GroupExtension.Equiv.symm equiv⟩
    trans := fun ⟨equiv⟩ ⟨equiv'⟩ ↦ ⟨GroupExtension.Equiv.trans equiv equiv'⟩ }

/-- The equivalence classes of group extensions -/
def EquivClasses := Quotient <| setoid N G

end ofMulDistribMulAction

namespace ofMulDistribMulActionWithSection

variable (S S' : ofMulDistribMulActionWithSection N G)
instance : Group S.E := S.GroupE
instance : Group S'.E := S'.GroupE

/-- Two terms of `GroupExtension.ofMulDistribMulActionWithSection` are equivalent iff their
  extensions are equivalent and the sections commute with the isomorphism. -/
structure Equiv extends S.extension.Equiv S'.extension where
  section_comm : toMulEquiv ∘ S.σ = S'.σ

variable (N G)

/-- The setoid on equivalence of group extensions with sections -/
instance setoid : Setoid (ofMulDistribMulActionWithSection N G) where
  r S S' := Nonempty (S.Equiv S')
  iseqv :=
  { refl := fun S ↦ ⟨{
      __ := GroupExtension.Equiv.refl S.extension
      section_comm := by
        ext g
        simp only [GroupExtension.Equiv.refl, Function.comp_apply, MulEquiv.refl_apply]
    }⟩
    symm := fun ⟨equiv⟩ ↦ ⟨{
      __ := equiv.toEquiv_1.symm
      section_comm := by
        simp only [GroupExtension.Equiv.symm, MulEquiv.symm_comp_eq]
        exact equiv.section_comm.symm
    }⟩
    trans := fun ⟨equiv⟩ ⟨equiv'⟩ ↦ ⟨{
      __ := equiv.toEquiv_1.trans equiv'.toEquiv_1
      section_comm := by
        simp only [GroupExtension.Equiv.trans, MulEquiv.trans, MulEquiv.toEquiv_eq_coe,
          MulEquiv.coe_mk, Equiv.coe_trans, EquivLike.coe_coe, Function.comp_assoc,
          equiv.section_comm, equiv'.section_comm]
    }⟩ }

/-- The equivalence classes of group extensions with sections -/
def EquivClasses := Quotient <| setoid N G

variable {N G}

/-- Returns the 2-cocycle corresponding to a group extension with a section -/
noncomputable def toTwoCocycle :
    groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N) where
  val := fun (g₁, g₂) ↦ Additive.ofMul (α := N) <|
    Function.invFun S.extension.inl <| S.σ g₁ * S.σ g₂ * (S.σ (g₁ * g₂))⁻¹
  property := by
    rw [groupCohomology.mem_twoCocycles_iff]
    intro g₁ g₂ g₃
    dsimp
    repeat rw [← ofMul_mul]
    rw [Equiv.apply_eq_iff_eq Additive.ofMul]
    apply S.extension.inl_injective
    rw [S.smul_eq_conjAct S.σ]
    simp only [map_mul, Section.inl_conjAct_comm,
      Function.invFun_eq <| Section.mul_mul_mul_inv_mem_range_inl _ _ _]
    rw [Subgroup.mul_comm_of_mem_isCommutative _ (Section.mul_mul_mul_inv_mem_range_inl _ _ _)
      (Section.mul_mul_mul_inv_mem_range_inl _ _ _)]
    group

theorem toTwoCocycle_apply (g₁ g₂ : G) : S.toTwoCocycle (g₁, g₂) =
    Additive.ofMul (Function.invFun S.extension.inl <| S.σ g₁ * S.σ g₂ * (S.σ (g₁ * g₂))⁻¹) := rfl

theorem inl_toTwoCocycle (g₁ g₂ : G) :
    S.extension.inl (Additive.toMul (α := N) (S.toTwoCocycle (g₁, g₂))) =
    S.σ g₁ * S.σ g₂ * (S.σ (g₁ * g₂))⁻¹ := by
  simp only [toTwoCocycle_apply, toMul_ofMul,
    Function.invFun_eq <| Section.mul_mul_mul_inv_mem_range_inl S.σ g₁ g₂]

end ofMulDistribMulActionWithSection

/-- The type with a group structure associated to an extension corresponding to a 2-cocycle -/
@[ext]
structure middleOfTwoCocycle (f : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N)) where
  /-- The term of `N` -/
  left : N
  /-- The term of `G` -/
  right : G

variable (f : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N))

namespace middleOfTwoCocycle

variable {f}

instance : Mul (middleOfTwoCocycle f) where
  mul e₁ e₂ := ⟨e₁.left * e₁.right • e₂.left * Additive.toMul (α := N) (f (e₁.right, e₂.right)),
    e₁.right * e₂.right⟩

theorem mul_def (e₁ e₂ : middleOfTwoCocycle f) :
    e₁ * e₂ = ⟨e₁.left * e₁.right • e₂.left * Additive.toMul (α := N) (f (e₁.right, e₂.right)),
    e₁.right * e₂.right⟩ := rfl

@[simp]
theorem mul_left (e₁ e₂ : middleOfTwoCocycle f) : (e₁ * e₂).left =
  e₁.left * e₁.right • e₂.left * Additive.toMul (α := N) (f (e₁.right, e₂.right)) := rfl

@[simp]
theorem mul_right (e₁ e₂ : middleOfTwoCocycle f) : (e₁ * e₂).right = e₁.right * e₂.right := rfl

instance : One (middleOfTwoCocycle f) where
  one := ⟨(Additive.toMul <| f (1, 1))⁻¹, 1⟩

theorem one_def : (1 : middleOfTwoCocycle f) = ⟨(Additive.toMul <| f (1, 1))⁻¹, 1⟩ := rfl

@[simp]
theorem one_left : (1 : middleOfTwoCocycle f).left = (Additive.toMul <| f (1, 1) : N)⁻¹ := rfl

@[simp]
theorem one_right : (1 : middleOfTwoCocycle f).right = 1 := rfl

instance : Inv (middleOfTwoCocycle f) where
  inv e := ⟨(e.right⁻¹ • e.left * Additive.toMul (α := N) (f (e.right⁻¹, e.right)) *
    (Additive.toMul (α := N) (f (1, 1))))⁻¹, e.right⁻¹⟩

theorem inv_def (e : middleOfTwoCocycle f) :
    e⁻¹ = ⟨(e.right⁻¹ • e.left * Additive.toMul (α := N) (f (e.right⁻¹, e.right)) *
    (Additive.toMul (α := N) (f (1, 1))))⁻¹, e.right⁻¹⟩ := rfl

@[simp]
theorem inv_left (e : middleOfTwoCocycle f) :
    e⁻¹.left = (e.right⁻¹ • e.left * Additive.toMul (α := N) (f (e.right⁻¹, e.right)) *
    (Additive.toMul (α := N) (f (1, 1))))⁻¹ := rfl

@[simp]
theorem inv_right (e : middleOfTwoCocycle f) : e⁻¹.right = e.right⁻¹ := rfl

/-- The group structure associated to an extension corresponding to a 2-cocycle -/
instance : Group (middleOfTwoCocycle f) where
  mul_assoc := by
    intro ⟨n₁, g₁⟩ ⟨n₂, g₂⟩ ⟨n₃, g₃⟩
    ext
    · simp only [mul_left, mul_right, smul_mul', mul_smul]
      rw [mul_assoc _ _ (g₁ • g₂ • n₃), mul_comm _ (g₁ • g₂ • n₃)]
      repeat rw [mul_assoc]
      rw [← toMul_add, add_comm, (groupCohomology.mem_twoCocycles_iff f).mp f.property g₁ g₂ g₃,
        toMul_add, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
    · simp only [mul_right, mul_assoc]
  one_mul e := by
    simp only [mul_def, one_left, one_right, one_smul, one_mul,
      groupCohomology.twoCocycles_map_one_fst f e.right, inv_mul_cancel_comm]
  mul_one e := by
    simp only [mul_def, one_left, one_right, mul_one, smul_inv', toMul_ofMul, inv_mul_cancel_right,
      groupCohomology.twoCocycles_map_one_snd f e.right, Rep.ofMulDistribMulAction_ρ_apply_apply]
  inv_mul_cancel := by
    intro ⟨n, g⟩
    ext
    · simp only [mul_left, inv_left, inv_right, one_left]
      group
    · simp only [mul_right, inv_right, inv_mul_cancel, one_right]

/-- The inclusion homomorphism -/
def inl : N →* middleOfTwoCocycle f where
  toFun n := ⟨n * (Additive.toMul (α := N) (f (1, 1)))⁻¹, 1⟩
  map_one' := by
    simp only [one_mul, one_def]
  map_mul' n₁ n₂ := by
    ext
    · simp only [mul_left, one_smul, mul_assoc, inv_mul_cancel, mul_one]
      rw [mul_comm n₂]
    · simp only [one_left, mul_right, mul_one]

@[simp]
theorem left_inl (n : N) :
    (inl n : middleOfTwoCocycle f).left = n * (Additive.toMul (α := N) (f (1, 1)))⁻¹ := rfl

@[simp]
theorem right_inl (n : N) : (inl n : middleOfTwoCocycle f).right = 1 := rfl

theorem mem_range_inl (e : middleOfTwoCocycle f) : e ∈ inl.range ↔ e.right = 1 :=
  ⟨fun ⟨n, hn⟩ ↦ hn ▸ right_inl n, fun h ↦ ⟨e.left * Additive.toMul (α := N) (f (1, 1)),
    middleOfTwoCocycle.ext (by rw [left_inl, mul_inv_cancel_right]) (by rw [right_inl, h])⟩⟩

theorem inl_injective : Function.Injective (inl (f := f)) := fun _ _ h ↦ by
  simpa only [inl, MonoidHom.coe_mk, OneHom.coe_mk, mk.injEq, mul_left_inj, and_true] using h

/-- The canonical projection homomorphism -/
def rightHom : middleOfTwoCocycle f →* G where
  toFun := right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem rightHom_eq_right : (rightHom : middleOfTwoCocycle f → G) = right := rfl

theorem rightHom_surjective : Function.Surjective (rightHom (f := f)) := fun g ↦ ⟨⟨1, g⟩, rfl⟩

theorem range_inl_eq_ker_rightHom : (inl (f := f)).range = (rightHom (f := f)).ker := by
  ext e
  rw [mem_range_inl, MonoidHom.mem_ker, rightHom_eq_right]

theorem smul_map_inv_eq (g : G) : g • Additive.toMul (α := N) (f (g⁻¹, g)) =
    Additive.toMul (α := N) (f (1, 1)) * (Additive.toMul (α := N) (f (g, 1)))⁻¹ *
    Additive.toMul (α := N) (f (g, g⁻¹)) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_toMul, ← Rep.ofMulDistribMulAction_ρ_apply_apply]
  rw [← sub_eq_iff_eq_add, ← sub_eq_add_neg]
  exact groupCohomology.twoCocycles_ρ_map_inv_sub_map_inv f g

theorem map_one_snd (g : G) : Additive.toMul (α := N) (f (g, 1)) =
    g • Additive.toMul (α := N) (f (1, 1)) := by
  apply Additive.ofMul.injective
  rw [ofMul_toMul, ← Rep.ofMulDistribMulAction_ρ_apply_apply]
  exact groupCohomology.twoCocycles_map_one_snd f g

theorem inl_smul_eq_conj_inl (g : G) (n n' : N) :
    (inl (g • n) : middleOfTwoCocycle f) = ⟨n', g⟩ * inl n * ⟨n', g⟩⁻¹ := by
  simp only [mul_def, left_inl, right_inl, inv_def, mul_one, smul_mul', smul_inv', smul_inv_smul,
    mul_inv_rev, smul_map_inv_eq, inv_inv, groupCohomology.twoCocycles_map_one_snd f g,
    Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
  ext
  · simp only [left_inl]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · simp only [right_inl, mul_inv_cancel]

end middleOfTwoCocycle

/-- The group extension corresponding to a 2-cocycle -/
def extensionOfTwoCocycle : GroupExtension N (middleOfTwoCocycle f) G where
  inl := middleOfTwoCocycle.inl
  rightHom := middleOfTwoCocycle.rightHom
  inl_injective := middleOfTwoCocycle.inl_injective
  range_inl_eq_ker_rightHom := middleOfTwoCocycle.range_inl_eq_ker_rightHom
  rightHom_surjective := middleOfTwoCocycle.rightHom_surjective

theorem extensionOfTwoCocycle_inl :
    (extensionOfTwoCocycle f).inl = middleOfTwoCocycle.inl := rfl

theorem extensionOfTwoCocycle_rightHom :
    (extensionOfTwoCocycle f).rightHom = middleOfTwoCocycle.rightHom := rfl

/-- The canonical section corresponding to a 2-cocycle -/
def sectionOfTwoCocycle : (extensionOfTwoCocycle f).Section where
  toFun := fun g ↦ ⟨1, g⟩
  rightInverse_rightHom := by
      intro _
      simp only [extensionOfTwoCocycle_rightHom, middleOfTwoCocycle.rightHom_eq_right]

namespace ofMulDistribMulActionWithSection

/-- Returns the group extension with a section corresponding to a 2-cocycle -/
def ofTwoCocycle : ofMulDistribMulActionWithSection N G where
  E := middleOfTwoCocycle f
  GroupE := inferInstance
  extension := extensionOfTwoCocycle f
  σ := sectionOfTwoCocycle f
  smul_eq_conjAct := by
    intro g n σ
    rw [σ.conjAct_eq (sectionOfTwoCocycle f)]
    simp only [Section.conjAct, MonoidHom.coe_mk, OneHom.coe_mk, sectionOfTwoCocycle]
    apply (extensionOfTwoCocycle f).inl_injective
    rw [inl_conjAct_comm, extensionOfTwoCocycle_inl, ← middleOfTwoCocycle.inl_smul_eq_conj_inl,
      Section.coe_mk]

/-- `toTwoCocycle` is a left inverse of `ofTwoCocycle`. -/
theorem toTwoCocycle_ofTwoCocycle :
    toTwoCocycle (ofTwoCocycle f) = f := by
  ext g₁ g₂
  simp only [toTwoCocycle_apply, ofTwoCocycle]
  apply Additive.toMul.injective
  apply (extensionOfTwoCocycle f).inl_injective
  rw [toMul_ofMul,
    Function.invFun_eq <|
      Section.mul_mul_mul_inv_mem_range_inl _ g₁ g₂,
    extensionOfTwoCocycle_inl]
  simp only [sectionOfTwoCocycle, middleOfTwoCocycle.mul_def, middleOfTwoCocycle.inv_left,
    middleOfTwoCocycle.inv_right, mul_inv, smul_mul', smul_inv', Section.coe_mk, smul_one, mul_one,
    one_mul, inv_one, mul_inv_cancel, middleOfTwoCocycle.smul_map_inv_eq, inv_inv,
    middleOfTwoCocycle.map_one_snd (g₁ * g₂)]
  rw [mul_right_comm _ _ ((g₁ * g₂) • Additive.toMul (α := N) (f (1, 1)))⁻¹,
    mul_inv_cancel_right, mul_assoc, inv_mul_cancel_right]
  ext <;> simp only [middleOfTwoCocycle.left_inl, middleOfTwoCocycle.right_inl]

/-- Two equivalent group extensions with sections correspond to the same 2-cocycle. -/
theorem toTwoCocycle_eq_of_equiv
    {S S' : ofMulDistribMulActionWithSection N G} (equiv : S.Equiv S') :
    toTwoCocycle S = toTwoCocycle S' := by
  ext g₁ g₂
  apply (Additive.toMul (α := N)).injective
  apply S'.extension.inl_injective
  rw [inl_toTwoCocycle, ← equiv.inl_comm, Function.comp_apply, inl_toTwoCocycle]
  simp only [map_mul, map_inv, ← equiv.section_comm, Function.comp_apply]

example {G : Type*} [Group G] {a b : G} (h : a * b * a⁻¹ = b) : a * b = b * a :=
  eq_mul_of_mul_inv_eq h

/-- `ofTwoCocycle` is a left inverse of `toTwoCocycle` up to equivalence of group extensions with
  sections-/
noncomputable def ofTwoCocycleToTwoCocycleEquiv (S : ofMulDistribMulActionWithSection N G) :
    (ofTwoCocycle (toTwoCocycle S)).Equiv S where
  toFun := fun ⟨n, g⟩ ↦ S.extension.inl n * S.σ g
  invFun := fun e ↦ ⟨Function.invFun S.extension.inl (e * (S.σ (S.extension.rightHom e))⁻¹),
    S.extension.rightHom e⟩
  left_inv := fun ⟨n, g⟩ ↦ by
    simp only [map_mul, rightHom_inl, Section.rightHom_section, one_mul, mul_inv_cancel_right,
      Function.leftInverse_invFun S.extension.inl_injective n]
  right_inv e := by
    simp only [← eq_mul_inv_iff_mul_eq]
    apply Function.invFun_eq
    rw [← MonoidHom.mem_range, S.extension.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul,
      map_inv, Section.rightHom_section, mul_inv_cancel]
  map_mul' := by
    intro ⟨n₁, g₁⟩ ⟨n₂, g₂⟩
    unfold ofTwoCocycle
    simp only [map_mul, inl_toTwoCocycle]
    rw [S.smul_eq_conjAct S.σ, Section.inl_conjAct_comm]
    simp only [← mul_assoc, inv_mul_cancel_right]
  inl_comm := by
    unfold ofTwoCocycle extensionOfTwoCocycle
    ext n
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, middleOfTwoCocycle.left_inl,
      map_mul, map_inv, inl_toTwoCocycle, mul_one, mul_inv_cancel_right,
      middleOfTwoCocycle.right_inl, inv_mul_cancel_right]
  rightHom_comm := by
    unfold ofTwoCocycle extensionOfTwoCocycle
    ext ⟨n, g⟩
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, map_mul, rightHom_inl,
      Section.rightHom_section, one_mul, middleOfTwoCocycle.rightHom_eq_right]
  section_comm := by
    unfold ofTwoCocycle sectionOfTwoCocycle
    ext g
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, Section.coe_mk, Function.comp_apply, map_one,
      one_mul]

/-- The bijection between the equivalence classes of group extensions with sections and 2-cocycles.
  -/
noncomputable def equivTwoCocycles :
    EquivClasses N G ≃ groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N) where
  toFun := Quotient.lift toTwoCocycle fun _ _ ⟨equiv⟩ ↦ toTwoCocycle_eq_of_equiv equiv
  invFun f := Quotient.mk (setoid N G) (ofTwoCocycle f)
  left_inv := by
    rintro ⟨S⟩
    rw [← Quotient.mk, Quotient.lift_mk (s := setoid N G), Quotient.eq (r := setoid N G)]
    exact ⟨ofTwoCocycleToTwoCocycleEquiv S⟩
  right_inv f := by rw [Quotient.lift_mk (s := setoid N G), toTwoCocycle_ofTwoCocycle]

/-- The difference of two 2-cocycles corresponding to equivalent group extensions
  (forgetting sections) is a 2-coboundary. -/
theorem sub_mem_twoCoboundaries_of_toofMulDistribMulAction_equiv
    {S S' : ofMulDistribMulActionWithSection N G}
    (equiv : S.toofMulDistribMulAction.Equiv S'.toofMulDistribMulAction) :
    S.toTwoCocycle - S'.toTwoCocycle ∈
    groupCohomology.twoCoboundaries (Rep.ofMulDistribMulAction G N) := by
  rw [groupCohomology.mem_twoCoboundaries_iff]
  use fun g ↦ Additive.ofMul (α := N) <| Function.invFun S'.extension.inl <|
    S.σ.equivComp equiv g * (S'.σ g)⁻¹
  intro g₁ g₂
  apply (Additive.toMul (α := N)).injective
  apply S'.extension.inl_injective
  simp only [Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
  rw [← groupCohomology.twoCocycles.val_eq_coe, AddSubgroupClass.coe_sub, Pi.sub_apply, toMul_add,
    toMul_sub, toMul_sub]
  simp only [groupCohomology.twoCocycles.val_eq_coe, div_eq_mul_inv, toMul_ofMul, map_mul, map_inv,
    inl_toTwoCocycle, Function.invFun_eq ((S.σ.equivComp equiv).mul_inv_mem_range_inl S'.σ _),
    S'.smul_eq_conjAct S'.σ, Section.inl_conjAct_comm]
  calc
    _ = S'.σ g₁ * ((S.σ.equivComp equiv) g₂ * (S'.σ g₂)⁻¹ * (S'.σ g₁)⁻¹ * S'.σ (g₁ * g₂) *
        ((S.σ.equivComp equiv) (g₁ * g₂))⁻¹ * (S.σ.equivComp equiv) g₁) * (S'.σ g₁)⁻¹ := by
      simp only [mul_assoc, mul_inv_rev, inv_inv]
    _ = (S.σ.equivComp equiv) g₁ * ((S.σ.equivComp equiv) g₂ * (S'.σ g₂)⁻¹ * (S'.σ g₁)⁻¹ *
        S'.σ (g₁ * g₂) * ((S.σ.equivComp equiv) (g₁ * g₂))⁻¹ * (S.σ.equivComp equiv) g₁) *
        ((S.σ.equivComp equiv) g₁)⁻¹ :=
      S'.σ.conj_eq_of_rightHom_eq_one (S.σ.equivComp equiv) g₁ <| by
        simp only [map_mul, map_inv, Section.rightHom_section, mul_inv_cancel_right,
          inv_mul_cancel_right, mul_inv_cancel]
    _ = (S.σ.equivComp equiv) g₁ * (S.σ.equivComp equiv) g₂ * ((S.σ.equivComp equiv) (g₁ * g₂))⁻¹ *
        ((S.σ.equivComp equiv) (g₁ * g₂) * ((S'.σ g₂)⁻¹ * (S'.σ g₁)⁻¹ * S'.σ (g₁ * g₂)) *
        ((S.σ.equivComp equiv) (g₁ * g₂))⁻¹) := by
      simp only [← mul_assoc, mul_inv_cancel_right, inv_mul_cancel_right]
    _ = (S.σ.equivComp equiv) g₁ * (S.σ.equivComp equiv) g₂ * ((S.σ.equivComp equiv) (g₁ * g₂))⁻¹ *
        (S'.σ (g₁ * g₂) * ((S'.σ g₂)⁻¹ * (S'.σ g₁)⁻¹ * S'.σ (g₁ * g₂)) * (S'.σ (g₁ * g₂))⁻¹) := by
      rw [(S.σ.equivComp equiv).conj_eq_of_rightHom_eq_one S'.σ (g₁ * g₂) <| by
        simp only [map_mul, map_inv, Section.rightHom_section, ← mul_inv_rev, inv_mul_cancel]]
    _ = _ := by
      simp only [← equiv.inl_comm, Function.comp_apply, inl_toTwoCocycle, map_mul, map_inv,
        mul_inv_rev, inv_inv, Section.equivComp_apply, ← mul_assoc, mul_inv_cancel_right,
        equiv.toMulEquiv_eq_coe, equiv.coe_toMulEquiv]

/-- If the difference of two 2-cocycles is a 2-coboundary, then forgetting sections, the
  corresponding group extensions are equivalent. -/
noncomputable def toofMulDistribMulActionEquivOfCochain
    {f f' : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N)} {x : G → N}
    (h : ∀ g₁ g₂ : G, Additive.toMul (α := N) (f (g₁, g₂)) *
      (Additive.toMul (α := N) (f' (g₁, g₂)))⁻¹ = g₁ • x g₂ * (x (g₁ * g₂))⁻¹ * x g₁) :
    (ofTwoCocycle f).toofMulDistribMulAction.Equiv (ofTwoCocycle f').toofMulDistribMulAction where
  toFun := fun ⟨n, g⟩ ↦ ⟨n * x g, g⟩
  invFun := fun ⟨n, g⟩ ↦ ⟨n * (x g)⁻¹, g⟩
  left_inv := fun ⟨n, g⟩ ↦ by simp only [mul_inv_cancel_right]
  right_inv := fun ⟨n, g⟩ ↦ by simp only [inv_mul_cancel_right]
  map_mul' := by
    intro ⟨n₁, g₁⟩ ⟨n₂, g₂⟩
    simp only [ofTwoCocycle, middleOfTwoCocycle.mul_def]
    ext
    · rw [mul_right_comm, ← mul_inv_eq_iff_eq_mul]
      simp only [mul_assoc]
      rw [h, mul_comm _ (x g₁), mul_comm (x (g₁ * g₂)), mul_assoc, inv_mul_cancel_right,
        mul_comm (g₁ • n₂), mul_assoc, mul_comm n₂, smul_mul']
    · rfl
  inl_comm := by
    ext n
    specialize h 1 1
    rw [one_smul, one_mul, inv_mul_cancel_right] at h
    simp only [ofTwoCocycle, extensionOfTwoCocycle, middleOfTwoCocycle.inl, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply, ← h, mul_assoc,
      inv_mul_cancel_left]
  rightHom_comm := by
    ext ⟨_, g⟩
    simp only [ofTwoCocycle, extensionOfTwoCocycle_rightHom, middleOfTwoCocycle.rightHom,
      MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply]

end ofMulDistribMulActionWithSection

namespace ofMulDistribMulAction

/-- The difference of two 2-cocycles corresponding to equivalent group extensions with arbitrary
  sections is a 2-coboundary. -/
theorem sub_mem_twoCoboundaries_of_equiv {S S' : ofMulDistribMulAction N G} (equiv : S.Equiv S')
    (σ : S.extension.Section) (σ' : S'.extension.Section) :
    ({ S with σ := σ } : ofMulDistribMulActionWithSection N G).toTwoCocycle -
    ({ S' with σ := σ' } : ofMulDistribMulActionWithSection N G).toTwoCocycle ∈
    groupCohomology.twoCoboundaries (Rep.ofMulDistribMulAction G N) :=
  ofMulDistribMulActionWithSection.sub_mem_twoCoboundaries_of_toofMulDistribMulAction_equiv equiv

/-- Returns the element of $H^2 (G, N)$ corresponding to an equivalence class of group extensions.
  -/
noncomputable def toH2 (S : ofMulDistribMulAction N G) :
    groupCohomology.H2 (Rep.ofMulDistribMulAction G N) :=
  Quotient.mk _ <| ofMulDistribMulActionWithSection.toTwoCocycle {
    S with σ := S.extension.surjInvRightHom
  }

/-- Returns the equivalence class of group extensions corresponding to an element of $H^2 (G, N)$.
  -/
def ofH2 (f : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N)) :
    EquivClasses N G :=
  Quotient.mk _ (ofMulDistribMulActionWithSection.ofTwoCocycle f).toofMulDistribMulAction

/-- The property of 2-coboundary specialized for `MulDistribMulAction` -/
theorem exists_cochain_of_sub_mem_twoCoboundaries
    {f f' : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N)}
    (h : f - f' ∈ groupCohomology.twoCoboundaries (Rep.ofMulDistribMulAction G N)) :
    ∃ x : G → N, ∀ g₁ g₂ : G, Additive.toMul (α := N) (f (g₁, g₂)) *
    (Additive.toMul (α := N) (f' (g₁, g₂)))⁻¹ = g₁ • x g₂ * (x (g₁ * g₂))⁻¹ * x g₁ := by
  rw [groupCohomology.mem_twoCoboundaries_iff] at h
  obtain ⟨x, hx⟩ := h
  use fun g ↦ Additive.toMul (α := N) (x g)
  intro g₁ g₂
  calc
    _ = Additive.toMul (α := N) ((f - f') (g₁, g₂)) := by
      simp only [← groupCohomology.twoCocycles.val_eq_coe, AddSubgroupClass.coe_sub, Pi.sub_apply,
        ← div_eq_mul_inv, ← toMul_sub]
    _ = _ := by
      rw [← hx g₁ g₂, toMul_add, toMul_sub, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul,
        div_eq_mul_inv]

variable (N G)

/-- The bijection between the equivalence classes of group extensions and `groupCohomology.H2` -/
noncomputable def equivH2 :
    EquivClasses N G ≃ groupCohomology.H2 (Rep.ofMulDistribMulAction G N) where
  toFun := Quotient.lift toH2 fun _ _ ⟨equiv⟩ ↦ (Quotient.eq (r := Submodule.quotientRel _)).mpr <|
    (Submodule.quotientRel_def _).mpr <| sub_mem_twoCoboundaries_of_equiv equiv _ _
  invFun := Quotient.lift ofH2 fun _ _ h ↦ (Quotient.eq (r := setoid N G)).mpr
    ⟨ofMulDistribMulActionWithSection.toofMulDistribMulActionEquivOfCochain
      (exists_cochain_of_sub_mem_twoCoboundaries <|
        (Submodule.quotientRel_def _).mp h).choose_spec⟩
  left_inv := by
    rintro ⟨S⟩
    unfold ofH2 toH2
    rw [← Quotient.mk, Quotient.lift_mk (s := setoid N G)]
    simp only [Quotient.lift_mk, Quotient.eq (r := setoid N G)]
    exact ⟨(ofMulDistribMulActionWithSection.ofTwoCocycleToTwoCocycleEquiv {
      toofMulDistribMulAction := S,
      σ := S.extension.surjInvRightHom
    }).toEquiv_1⟩
  right_inv := by
    rintro ⟨f⟩
    unfold ofH2 toH2
    rw [← Quotient.mk]
    simpa only [Quotient.lift_mk, Quotient.eq (r := Submodule.quotientRel _), HasEquiv.Equiv,
      instHasEquivOfSetoid, Submodule.quotientRel_def,
      ofMulDistribMulActionWithSection.toTwoCocycle_ofTwoCocycle] using
      ofMulDistribMulActionWithSection.sub_mem_twoCoboundaries_of_toofMulDistribMulAction_equiv
      (Equiv.refl
        (ofMulDistribMulActionWithSection.ofTwoCocycle f).toofMulDistribMulAction.extension)
      (S := {
        __ := (ofMulDistribMulActionWithSection.ofTwoCocycle f).toofMulDistribMulAction
        σ := (ofMulDistribMulActionWithSection.ofTwoCocycle f).extension.surjInvRightHom
      })
      (S' := ofMulDistribMulActionWithSection.ofTwoCocycle f)

end ofMulDistribMulAction

end

end GroupExtension
