/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Abelian
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

## Main definitions (Todo for now)

* Central extension
* `R`-split
* split
* projective representations

## Main results

* cocycle description
* cohomological criterion for triviality

## References

* [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 1--3*][bourbaki1975]
-- extensions are chapter 1 section 7, cohomology is Exercises section 3 (p116, near end of book)


## Tags

lie ring, lie algebra, central extension
-/

suppress_compilation

namespace LieAlgebra.Extension

variable {R L M N V : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M] (S : Extension R N M)

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
/-!
lemma isCentral_of_equiv (S' : Extension R N M) (h : S.IsCentral) (e : Equiv S S') :
    IsCentral S' := by
  refine (IsCentral_iff S').mpr ⟨fun x m ↦ ?_⟩
  suffices ⁅e.toLieEquiv.symm x, e.toLieEquiv.symm m⁆ = 0 by
    rw [← LieEquiv.map_lie] at this
    have : e.toLieEquiv.symm ⁅x, m.val⁆ = e.toLieEquiv.symm 0 := by
      rw [this]

  sorry
-/
@[simp]
lemma comp_eq_id {s : M →ₗ[R] S.L} (hs : S.proj.toLinearMap ∘ₗ s = LinearMap.id)
    (x : M) :
    S.proj (s x) = x := by
  simp [show S.proj (s x) = S.proj.toLinearMap.comp s x by rfl, hs]

lemma bracket_sub_bracket_mem_kernel {s : M →ₗ[R] S.L} (hs : S.proj.toLinearMap ∘ₗ s = LinearMap.id)
    (x y : M) :
    ⁅s x, s y⁆ - s ⁅x, y⁆ ∈ LinearMap.ker S.proj.toLinearMap := by
  simp [hs]

section ofTwoCocycle

variable [LieRing V] [LieAlgebra R V] (h : IsLieAbelian V) (c : twoCocycle R L V)

/-- The Lie algebra map inclusion of a central extension derived from a 2-cocycle. -/
@[simps]
def twoCocycleIncl : V →ₗ⁅R⁆ (ofTwoCocycleAlg c) where
  toLinearMap := {
    toFun v := ofProd c (0, v)
    map_add' _ _ := by
      rw [← of_add, Prod.zero_mk_add_zero_mk]
    map_smul' _ _ := by rw [← of_smul, Equiv.apply_eq_iff_eq, RingHom.id_apply, Prod.smul_zero_mk]}
  map_lie' {x y} := by simp [bracket_ofTwoCocycleAlg]

/-- A Lie extension from a trivial 2-cocycle, but an extension of `L` by
`(twoCocycleProj c).ker` instead of `V`. They are equal but not definitionally so. -/
@[simps]
def ofTwoCocycle : Extension R V L where
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

lemma twoCocycleProj_eq : (twoCocycleProj c) = (ofTwoCocycle h c).proj := rfl

/-- The canonical linear section of an extension attached to a 2-cocycle. -/
@[simps]
def sectionTwoCocycleRight : L →ₗ[R] (ofTwoCocycleAlg c) where
  toFun x := ofProd c (x, 0)
  map_add' _ _ := by rw [← of_add, Prod.mk_zero_add_mk_zero]
  map_smul' _ _ := by rw [← of_smul, Equiv.apply_eq_iff_eq, RingHom.id_apply, Prod.smul_mk_zero]

/-- superfluous -/
lemma ofTwoCocycle_section_comp_proj :
    (ofTwoCocycle h c).proj.toLinearMap ∘ₗ (sectionTwoCocycleRight c) = LinearMap.id := by
  rfl

/-- The left section of an extension attached to a 2-cocycle. -/
def sectionTwoCocycleLeft : (ofTwoCocycle h c).L →ₗ[R] V where
  toFun x := ((ofProd c).symm x).2
  map_add' _ _ := by rw [of_symm_add, Prod.snd_add]
  map_smul' _ _ := by rw [of_symm_smul, Prod.smul_snd, RingHom.id_apply]

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
def Equiv.ofCoboundary (c' : twoCocycle R L V) (x : oneCochain R L V)
    (hcc' : c' = c + d₁₂ R L V x) :
    Equiv (ofTwoCocycle h c) (ofTwoCocycle h c') where
  toLieEquiv := LieEquiv.ofCoboundary c c' x hcc'
  incl_comm := by ext; simp
  proj_comm := by ext; simp

/-- Construct a cocycle from a module-split central extension. -/
@[simps]
def twoCocycleOfSplitting (E : Extension R N M) (hE : E.IsCentral) {s : M →ₗ[R] E.L}
    (hs : E.proj.toLinearMap ∘ₗ s = LinearMap.id) (p : E.L →ₗ[R] N) :
    twoCocycle R M N where
  val := {
    val := {
      toFun a := {
          toFun b := p ⁅s a, s b⁆
          map_add' _ _ := by simp
          map_smul' _ _ := by simp }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    property _ := by simp }
  property := by
    ext x y z
    simp only [d₂₃_apply_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
      Pi.ofNat_apply]
    have := lie_jacobi (s x) (s y) (s z)
    rw [E.bracket_eq_of_sub_mem_kernel hE (s x) ⁅s y, s z⁆ (s ⁅y, z⁆),
      E.bracket_eq_of_sub_mem_kernel hE (s y) ⁅s z, s x⁆ (s ⁅z, x⁆),
      E.bracket_eq_of_sub_mem_kernel hE (s z) ⁅s x, s y⁆ (s ⁅x, y⁆)] at this
    · simp [← map_add, this]
    · exact E.bracket_sub_bracket_mem_kernel hs x y
    · exact E.bracket_sub_bracket_mem_kernel hs z x
    · exact E.bracket_sub_bracket_mem_kernel hs y z

@[simp]
lemma twoCocycleOfSplitting_ofTwoCocycle :
    (ofTwoCocycle h c).twoCocycleOfSplitting (isCentral_ofTwoCocycle h c)
      (ofTwoCocycle_section_comp_proj h c) (sectionTwoCocycleLeft h c) = c := by
  ext x y
  simp [sectionTwoCocycleLeft, bracket_ofTwoCocycleAlg]

lemma proj_comp_equiv_comp_section (E E' : Extension R N M) (e : Equiv E E') {s : M →ₗ[R] E.L}
    (hs : E.proj.toLinearMap ∘ₗ s = LinearMap.id) :
    E'.proj.toLinearMap ∘ₗ (e.toLieEquiv ∘ₗ s) = LinearMap.id := by
  ext
  simp [← hs, ← e.proj_comm]
/-!
/-- The 2-coboundary corresponding to an equivalence of module-split extensions. -/
def Equiv.coboundaryOf (E E' : Extension R N M) (e : Equiv E E') (hE : E.IsCentral)
    {s : M →ₗ[R] E.L} (hs : E.proj.toLinearMap ∘ₗ s = LinearMap.id) (p : E.L →ₗ[R] N) :
    twoCoboundary R M N where
  val := {
    val := {
      toFun x := {
        toFun y :=
          (E.twoCocycleOfSplitting hE hs p).val x y -
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
-/
-- shearing a splitting by a translation yields a difference of coboundary?
-- make a correspondence with cohomology!!

end ofTwoCocycle

/-!
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

end Extension

end LieAlgebra
