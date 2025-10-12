/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Extension

/-!
# Central extensions of Lie algebras

Given a Lie algebra `L` over a commutative ring `R`, and an abelian Lie algebra `C` over `R`, a
central extension of `L` by `C` is a Lie algebra `M` over `R` equipped with a surjective
homomorphism `f : M →ₗ[R] L` and an `R`-isomorphism from `C` to the kernel of `f`. A central
extension is `R`-split if the structure maps on `M` induce an `R`-module decomposition into a direct
sum of `L` and `C`. In this case, we can describe `M` as a direct sum with bracket given by a
2-cocycle. Two `R`-split central extensions are isomorphic if and only if the 2-cocycles differ by
a coboundary.

A projective `R`-linear representation of a Lie algebra `L` over `R` is an `R`-module `M` with a
linear map `ρ : L → End R M` such that `ρ [x,y] = c(x,y) ρ x ρ y` or something.

## Main definitions

* `LieAlgebra.Extension.IsCentral` : A `Prop`-valued condition for an extension to be central.
* `LieAlgebra.Extension.ofTwoCocycle` : The construction of an extension from a 2-cocycle.
* `LieAlgebra.Extension.twoCocycleOfSplitting` : A 2-cocycle obtained from a module-splitting of an
  extension.
* `LieAlgebra.Extension.Equiv.ofCoboundary` : An equivalence of extensions induced by translation by
  a coboundary.

## Main results

* Going from a two-cocycle to an extension and back is identity.
* cohomological criterion for triviality

## TODO

* split
* projective representations

## References

* [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 1--3*][bourbaki1975]
-- extensions are chapter 1 section 7, cohomology is Exercises section 3 (p116, near end of book)


## Tags

lie ring, lie algebra, central extension
-/

suppress_compilation

variable {R L M N V : Type*} [CommRing R]

namespace LieAlgebra.Extension

section IsCentral

variable [LieRing N] [LieAlgebra R N] [LieRing M] [LieAlgebra R M] (S : Extension R N M)

/-- An extension is central if the kernel of projection lies in the center. -/
def IsCentral : Prop :=
  S.proj.ker ≤ LieAlgebra.center R S.L

lemma IsCentral_iff : S.IsCentral ↔ LieModule.IsTrivial S.L S.proj.ker :=
  (LieModule.trivial_iff_le_maximal_trivial R S.L S.L S.proj.ker).symm

lemma bracket_eq_zero_of_isCentral (h : S.IsCentral) (x y : S.L) (hy : y ∈ S.proj.ker) :
    ⁅x, y⁆ = 0 :=
  h hy x

lemma isAbelian_of_IsCentral (h : S.IsCentral) : IsLieAbelian N := by
  refine ⟨fun x y ↦ ?_⟩
  suffices S.incl ⁅x, y⁆ = 0 by
    exact (LinearMap.map_eq_zero_iff S.incl.toLinearMap S.incl_injective).mp this
  rw [LieHom.map_lie]
  exact bracket_eq_zero_of_isCentral S h (S.incl x) (S.incl y) <|
    LieHom.mem_ker.mpr <| proj_incl S y

lemma bracket_eq_of_sub_mem_kernel (h : S.IsCentral) (x y z : S.L) (hyz : y - z ∈ S.proj.ker) :
    ⁅x, y⁆ = ⁅x, z⁆ := by
  rw [← sub_eq_zero, ← lie_sub]
  exact S.bracket_eq_zero_of_isCentral h x (y - z) hyz

lemma isCentral_of_equiv (S' : Extension R N M) (h : S.IsCentral) (e : Equiv S S') :
    IsCentral S' := by
  refine (IsCentral_iff S').mpr ⟨fun x m ↦ ?_⟩
  suffices ⁅e.toLieEquiv.symm x, e.toLieEquiv.symm m⁆ = 0 by
    rw [← LieEquiv.map_lie] at this
    have : e.toLieEquiv.symm ⁅x, m.val⁆ = e.toLieEquiv.symm 0 := by
      rw [this]
      exact (ZeroHomClass.map_zero e.toLieEquiv.symm).symm
    rw [EquivLike.apply_eq_iff_eq] at this
    exact ZeroMemClass.coe_eq_zero.mp this
  refine bracket_eq_zero_of_isCentral S h (e.toLieEquiv.symm x) (e.toLieEquiv.symm ↑m) ?_
  rw [LieHom.mem_ker, ← e.proj_comm, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    LieEquiv.apply_symm_apply, ← LieHom.mem_ker] -- make this part a lemma?
  exact SetLike.coe_mem m

@[simp]
lemma comp_eq_id {s : M →ₗ[R] S.L} (hs : S.proj.toLinearMap ∘ₗ s = LinearMap.id)
    (x : M) :
    S.proj (s x) = x := by
  simp [show S.proj (s x) = S.proj.toLinearMap.comp s x by rfl, hs]

lemma bracket_sub_bracket_mem_kernel {s : M →ₗ[R] S.L} (hs : S.proj.toLinearMap ∘ₗ s = LinearMap.id)
    (x y : M) :
    ⁅s x, s y⁆ - s ⁅x, y⁆ ∈ LinearMap.ker S.proj.toLinearMap := by
  simp [hs]

end IsCentral

section ofTwoCocycle
open LieModule.Cohomology

variable [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N] [LieRingModule M N]
[LieModule R M N] [LieModule.IsTrivial M N] (h : IsLieAbelian N) (c : twoCocycle R M N)

/-- The Lie algebra map inclusion of a central extension derived from a 2-cocycle. -/
@[simps]
def twoCocycleIncl : N →ₗ⁅R⁆ (ofTwoCocycleAlg c) where
  toLinearMap := {
    toFun v := ofProd c (0, v)
    map_add' _ _ := by
      rw [← of_add, Prod.zero_mk_add_zero_mk]
    map_smul' _ _ := by rw [← of_smul, Equiv.apply_eq_iff_eq, RingHom.id_apply, Prod.smul_zero_mk]}
  map_lie' {x y} := by simp [bracket_ofTwoCocycleAlg]

/-- A Lie extension from a trivial 2-cocycle, but an extension of `L` by
`(twoCocycleProj c).ker` instead of `V`. They are equal but not definitionally so. -/
def ofTwoCocycle : Extension R N M where
  L := ofTwoCocycleAlg c
  instLieRing := inferInstance
  instLieAlgebra := inferInstance
  incl := twoCocycleIncl h c
  proj := twoCocycleProj c
  extension := by
    refine { ker_eq_bot := ?_, range_eq_top := ?_, exact := ?_ }
    · ext v
      simp [twoCocycleIncl, ← of_zero]
    · refine (LieHom.range_eq_top (twoCocycleProj c)).mpr ?_
      exact surjective_of_cocycle c
    · ext x
      constructor
      · intro h
        simp only [twoCocycleIncl, LieHom.mem_range, LieHom.coe_mk] at h
        obtain ⟨y, hy⟩ := h
        simp only [twoCocycleProj, ← hy]
        rfl
      · intro h
        use ((ofProd c).symm x).2
        have : ((ofProd c).symm x).1 = 0 := h
        simp [twoCocycleIncl, ← this]

/-- The Lie algebra isomorphism given by the type synonym. -/
def ofAlg : ofTwoCocycleAlg c ≃ₗ⁅R⁆ (ofTwoCocycle h c).L := LieEquiv.refl

@[simp]
lemma twoCocycleProj_ofAlg_symm :
    LieHom.comp (twoCocycleProj c) (ofAlg h c).symm = (ofTwoCocycle h c).proj := rfl

@[simp]
lemma ofToCocycle_ofAlg :
    LieHom.comp (ofTwoCocycle h c).proj (ofAlg h c) = (twoCocycleProj c) := rfl

@[simp]
lemma ofAlg_twoCocycleIncl :
    LieHom.comp (ofAlg h c) (twoCocycleIncl h c) = (ofTwoCocycle h c).incl := rfl

@[simp]
lemma ofAlg_symm_ofTwoCocycle :
    LieHom.comp (ofAlg h c).symm (ofTwoCocycle h c).incl = twoCocycleIncl h c := rfl

lemma bracket_ofTwoCocycle (x y : (ofTwoCocycle h c).L) :
    ⁅x, y⁆ = ofAlg h c ⁅(ofAlg h c).symm x, (ofAlg h c).symm y⁆ := rfl

/-- The canonical linear section of an extension attached to a 2-cocycle. -/
def sectionTwoCocycleRight : M →ₗ[R] (ofTwoCocycle h c).L where
  toFun x := ofAlg h c (ofProd c (x, 0))
  map_add' _ _ := by rw [← Prod.mk_zero_add_mk_zero, of_add, map_add]
  map_smul' _ _ := by rw [← map_smulₛₗ, ← Prod.smul_mk_zero, of_smul]

lemma sectionTwoCocycleRight_apply (x : M) :
    (sectionTwoCocycleRight h c) x = (ofAlg h c) ((ofProd c) (x, 0)) := by
  rfl

lemma ofAlg_symm_sectionTwoCocycleRight_apply (x : M) :
    (ofAlg h c).symm ((sectionTwoCocycleRight h c) x) = (ofProd c) (x, 0) := by
  rfl

/-- superfluous -/
lemma ofTwoCocycle_section_comp_proj :
    (ofTwoCocycle h c).proj.toLinearMap ∘ₗ (sectionTwoCocycleRight h c) = LinearMap.id := by
  rfl

@[simp]
lemma ofTwoCocycle_section_proj (x : M) :
    (ofTwoCocycle h c).proj (sectionTwoCocycleRight h c x) = x := by
  rfl

lemma bracket_sectionTwoCocycleRight (x y : M) :
    ⁅sectionTwoCocycleRight h c x, sectionTwoCocycleRight h c y⁆ =
      sectionTwoCocycleRight h c ⁅x, y⁆ + (ofTwoCocycle h c).incl (c.val x y) := by
  simp only [bracket_ofTwoCocycle, bracket_ofTwoCocycleAlg, twoCochain_val_apply]
  simp only [← ofAlg_twoCocycleIncl, ofAlg_symm_sectionTwoCocycleRight_apply h c,
    Equiv.symm_apply_apply]
  rw [sectionTwoCocycleRight_apply h c, LieHom.coe_comp,LieEquiv.coe_toLieHom, Function.comp_apply]
  have : (⁅x, y⁆, (c.val x) y) = (⁅x, y⁆, 0) + (0, (c.val x) y) := by simp
  rw [this, of_add, map_add, twoCocycleIncl_apply]

/-- The left section of an extension attached to a 2-cocycle. -/
def sectionTwoCocycleLeft : (ofTwoCocycle h c).L →ₗ[R] N where
  toFun x := ((ofProd c).symm ((ofAlg h c).symm x)).2
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

-- simpNF linter doesn't like this as a simp lemma.
lemma sectionTwoCocycleLeft_apply (x : (ofTwoCocycle h c).L) :
    sectionTwoCocycleLeft h c x = ((ofProd c).symm x).2 := by
  rfl

lemma isCentral_ofTwoCocycle : (ofTwoCocycle h c).IsCentral := by
  rw [IsCentral_iff, LieModule.trivial_iff_le_maximal_trivial]
  intro x hx
  simp only [ofTwoCocycle, twoCocycleProj, LieHom.mem_ker, LieHom.coe_mk] at hx
  intro y
  rw [bracket_ofTwoCocycleAlg, hx, lie_zero, map_zero, Prod.mk_zero_zero, of_zero]

/-- An equivalence of extensions induced by a coboundary translation. -/
@[simps]
def Equiv.ofCoboundary (c' : twoCocycle R M N) (x : oneCochain R M N)
    (hcc' : c' = c + d₁₂ R M N x) :
    Equiv (ofTwoCocycle h c) (ofTwoCocycle h c') where
  toLieEquiv := (ofAlg h c).symm.trans ((LieEquiv.ofCoboundary c c' x hcc').trans (ofAlg h c'))
  incl_comm := by
    ext
    simp only [LieHom.coe_comp, LieEquiv.coe_coe, Function.comp_apply, LieEquiv.trans_apply,
      LieEquiv.ofCoboundary_toFun]
    have (x : N) : (ofAlg h c).symm ((ofTwoCocycle h c).incl x) = twoCocycleIncl h c x := by
      rw [← ofAlg_symm_ofTwoCocycle, LieHom.comp_apply, LieEquiv.coe_toLieHom]
    rw [this, ← ofAlg_symm_ofTwoCocycle, ← ofAlg_twoCocycleIncl h c', LieHom.comp_apply,
      LieEquiv.coe_toLieHom, this, LieHom.comp_apply, LieEquiv.coe_toLieHom]
    simp
  proj_comm := by
    ext
    simp only [LieHom.coe_comp, LieEquiv.coe_coe, Function.comp_apply, LieEquiv.trans_apply,
      LieEquiv.ofCoboundary_toFun]
    exact rfl -- feels suspicious

end ofTwoCocycle

section TwoCocycle

open LieModule.Cohomology

variable [LieRing N] [LieAlgebra R N] [LieRing M] [LieAlgebra R M] (E : Extension R N M)
[LieRingModule M N] [LieModule R M N] [LieModule.IsTrivial M N]
    (hE : E.IsCentral) {s : M →ₗ[R] E.L}
    (hs : ∀ x, E.proj (s x) = x) (p : E.L →ₗ[R] N)

include hs in
omit [LieRingModule M N] [LieModule R M N] [LieModule.IsTrivial M N] in
lemma section_lie_sub_mem_ker (x y : M) : ⁅s x, s y⁆ - s ⁅x, y⁆ ∈ LieHom.ker E.proj := by
  rw [LieHom.mem_ker, LieHom.map_sub, sub_eq_zero, LieHom.map_lie, hs, hs, hs]

/-- An auxiliary function for defining the 2-cocycle attached to a section. -/
@[simps]
def twoCocycleOfSplittingAux : M →ₗ[R] M →ₗ[R] E.proj.ker where
  toFun a := {
    toFun b := ⟨⁅s a, s b⁆ - s ⁅a,b⁆, E.section_lie_sub_mem_ker hs a b⟩
    map_add' _ _ := by simp; abel
    map_smul' _ _ := by simp [smul_sub] }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

include E hE hs in
/-- Construct a cocycle from a module-split central extension. -/
def twoCocycleOfSplitting : twoCocycle R M N where
  val := {
    val := (E.twoCocycleOfSplittingAux hs).compr₂ (E.projInclEquiv ≪≫ₗ E.sectLeft).toLinearMap
    property _ := by
      simp only [LinearMap.compr₂_apply]
      refine (map_eq_zero_iff ↑(E.projInclEquiv ≪≫ₗ E.sectLeft)
        (LinearEquiv.injective (E.projInclEquiv ≪≫ₗ E.sectLeft))).mpr
        (Subtype.eq ?_)
      simp }
  property := by
    ext x y z
    simp only [d₂₃_apply, ← twoCochain_val_apply, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
      trivial_lie_zero, sub_self, add_zero, zero_sub, LinearMap.zero_apply]
    rw [← map_neg, ← map_add, ← map_sub]
    refine (LinearEquiv.map_eq_zero_iff (E.projInclEquiv ≪≫ₗ E.sectLeft)).mpr ?_
    simp only [twoCocycleOfSplittingAux, LinearMap.coe_mk, AddHom.coe_mk, lie_lie, map_sub]
    refine Subtype.eq ?_
    simp only [AddSubgroupClass.coe_sub, LieSubmodule.coe_add, NegMemClass.coe_neg, neg_sub,
      ZeroMemClass.coe_zero]
    have hjac := lie_jacobi (s x) (s y) (s z)
    rw [E.bracket_eq_of_sub_mem_kernel hE (s x) ⁅s y, s z⁆ (s ⁅y, z⁆)
      (section_lie_sub_mem_ker E hs y z), E.bracket_eq_of_sub_mem_kernel hE (s y) ⁅s z, s x⁆
      (s ⁅z, x⁆) (section_lie_sub_mem_ker E hs z x), E.bracket_eq_of_sub_mem_kernel hE (s z)
      ⁅s x, s y⁆ (s ⁅x, y⁆) (section_lie_sub_mem_ker E hs x y), ← lie_skew (s z),
      ← sub_eq_add_neg, sub_eq_zero] at hjac
    rw [← hjac, ← lie_skew (s x), ← lie_skew (s y), ← lie_skew x]
    have := congr_arg s (lie_lie y x z)
    rw [← lie_skew y x, neg_lie, ← lie_skew _ z, neg_neg] at this
    simp only [lie_lie, neg_sub, map_sub, lie_skew]
    abel_nf
    rw [this, ← lie_skew z x, ← lie_skew _ (s y), ← lie_skew _ (s x), ← lie_skew z y]
    simp only [map_sub, map_neg, lie_neg]
    abel

lemma twoCocycleOfSplitting_apply_apply (a b : M) :
    (E.twoCocycleOfSplitting hE hs).val a b =
      (E.projInclEquiv ≪≫ₗ E.sectLeft).toLinearMap
        ⟨⁅s a, s b⁆ - s ⁅a,b⁆, E.section_lie_sub_mem_ker hs a b⟩ := by
  rfl

@[simp]
lemma incl_twoCocycleOfSplitting_apply (a b : M) :
    E.incl ((E.twoCocycleOfSplitting hE hs).val a b) = ⁅s a, s b⁆ - s ⁅a, b⁆ := by
  simp only [twoCocycleOfSplitting_apply_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    incl_sectLeft]
  rfl

@[simp]
lemma twoCocycleOfSplitting_ofTwoCocycle (h : IsLieAbelian N) (c : twoCocycle R M N) :
    (ofTwoCocycle h c).twoCocycleOfSplitting (isCentral_ofTwoCocycle h c)
      (ofTwoCocycle_section_proj h c) = c := by
  ext x y
  apply (ofTwoCocycle h c).incl_injective
  rw [twoCochain_val_apply, (ofTwoCocycle h c).incl_twoCocycleOfSplitting_apply,
    twoCochain_val_apply]
  erw [bracket_sectionTwoCocycleRight h c]
  simp

lemma bracket_of_splitting (hp : p ∘ₗ E.incl = LinearMap.id) (x y : M) :
    ⁅s x, s y⁆ = s ⁅x, y⁆ + E.incl ((E.twoCocycleOfSplitting hE hs).val x y) := by
  refine E.eq_of_proj_eq ?_ hp ?_
  · rw [incl_twoCocycleOfSplitting_apply, map_add, map_sub]
    abel
  · rw [incl_twoCocycleOfSplitting_apply, map_add, map_sub]
    abel

omit [LieRingModule M N] [LieModule R M N] [LieModule.IsTrivial M N] in
lemma proj_comp_equiv_comp_section (E E' : Extension R N M) (e : Equiv E E') {s : M →ₗ[R] E.L}
    (hs : ∀ x, E.proj (s x) = x) :
    E'.proj.toLinearMap ∘ₗ (e.toLieEquiv ∘ₗ s) = LinearMap.id := by
  ext
  simp only [LinearMap.coe_comp, LieHom.coe_toLinearMap, LinearEquiv.coe_coe,
    LieEquiv.coe_toLinearEquiv, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [← LieEquiv.coe_toLieHom, ← LieHom.comp_apply, Equiv.proj_comm, hs]
/-!
/-- An equivalence of central extensions induced by an equality of 2-cocycles. -/
def Equiv.ofTwoCocycleOfSplitting [LieRingModule M N] [LieModule R M N] [LieModule.IsTrivial M N]
    (h : IsLieAbelian N) (c : twoCocycle R M N) (E : Extension R N M) (hE : E.IsCentral)
    {s : M →ₗ[R] E.L} (hs : ∀ (x : M), E.proj (s x) = x) {p : E.L →ₗ[R] N}
    (hp : p ∘ₗ E.incl.toLinearMap = LinearMap.id) (hc : E.twoCocycleOfSplitting hE hs = c) :
    Equiv (ofTwoCocycle h c) E where
  toLieEquiv := {
    toFun a := s ((ofProd c).symm ((ofAlg h c).symm a)).1 +
      E.incl ((ofProd c).symm ((ofAlg h c).symm a)).2
    map_add' _ _ := by simp; abel
    map_smul' r x := by simp
    map_lie' {x y} := by
      refine E.eq_of_proj_eq ?_ hp ?_
      · simp only [lie_add, add_lie]
        have zero_left (z : N) (w : E.L) : ⁅w, E.incl z⁆ = 0 := by
          refine bracket_eq_zero_of_isCentral E hE w (E.incl z) ?_
          rw [LieHom.mem_ker, proj_incl]
        have zero_right (z : N) (w : E.L) : ⁅E.incl z, w⁆ = 0 := by
          rw [← lie_skew, zero_left, neg_eq_zero]
        simp only [zero_right, add_zero, zero_left]
        rw [bracket_ofTwoCocycle, LieEquiv.map_lie, LieEquiv.apply_symm_apply,
          LieEquiv.apply_symm_apply, bracket_ofTwoCocycleAlg]
        rw [map_add, bracket_of_splitting E hE hs p hp, map_add, hc, ← twoCochain_val_apply]
        simp
      · simp only [LieHom.map_add, proj_incl, add_zero, lie_add, add_lie,
          LieHom.map_lie, zero_lie, lie_zero, lie_self, hs]
        rw [bracket_ofTwoCocycle, LieEquiv.map_lie, LieEquiv.apply_symm_apply,
          LieEquiv.apply_symm_apply, bracket_ofTwoCocycleAlg, Equiv.symm_apply_apply]
    invFun x := ofProd c (E.proj x, p x) --change this!
    left_inv x := by
      simp only [map_add, proj_incl, add_zero]
      rw [comp_eq_id E _ ((ofProd c).symm x).1]
      · refine (Equiv.apply_eq_iff_eq_symm_apply (ofProd c)).mpr ?_
        refine Prod.ext rfl ?_
        simp only
        have (z : N) : p (E.incl z) = z := by
          rw [← LieHom.coe_toLinearMap, ← LinearMap.comp_apply, hp, LinearMap.id_apply]
        rw [this]
        sorry
      · exact LinearMap.ext_iff.mpr hs
    right_inv x := by
      simp only
      rw [Equiv.symm_apply_apply]
      sorry
    }
  incl_comm := sorry
  proj_comm := sorry

/-- The 2-coboundary corresponding to an equivalence of module-split extensions. -/
def Equiv.coboundaryOf (E E' : Extension R N M) (e : Equiv E E') (hE : E.IsCentral)
    {s : M →ₗ[R] E.L} (hs : ∀ x, E.proj (s x) = x) (p : E.L →ₗ[R] N) :
    twoCoboundary R M N where
  val := {
    val := {
      toFun x := {
        toFun y :=
          (E.twoCocycleOfSplitting hE hs).val x y -
          (E'.twoCocycleOfSplitting (isCentral_of_equiv E E' hE e)
            (proj_comp_equiv_comp_section E E' e hs) (p ∘ₗ e.toLieEquiv.toLinearEquiv.symm)).val x y
        map_add' _ _ := by sorry
        map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
    property := sorry }
  property := sorry

/-- An isomorphism of extensions -/
def ofTwoCocycle_twoCocycleOfSplitting (E : Extension R N M) (hE : E.IsCentral) {s : M →ₗ[R] E.L}
    (hs : E.proj.toLinearMap ∘ₗ s = LinearMap.id) (p : E.L →ₗ[R] N) :
    Equiv (ofTwoCocycle (E.isAbelian_of_IsCentral hE) (twoCocycleOfSplitting E hE hs p)) E where
  toLieEquiv := by

    sorry
  incl_comm := sorry
  proj_comm := sorry

-- shearing a splitting by a translation yields a difference of coboundary?
-- make a correspondence with cohomology!!



/-- A Lie algebra homomorphism is a central extension if it is surjective and the kernel lies in the
center. The center condition is equivalent to the kernel being a trivial module for the adjoint
adjoint action. -/
class IsCentralExtension (f : M →ₗ⁅R⁆ L) : Prop where
  protected surjective : Function.Surjective f
  protected central : LieModule.IsTrivial M f.ker

lemma surjective_of_central_extension (f : M →ₗ⁅R⁆ L) [IsCentralExtension f] :
    Function.Surjective f := IsCentralExtension.surjective

lemma central_of_central_extension (f : M →ₗ⁅R⁆ L) [IsCentralExtension f] :
    LieModule.IsTrivial M f.ker := IsCentralExtension.central
-/
end TwoCocycle

end Extension

end LieAlgebra
