import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.DFinsupp

set_option autoImplicit false

noncomputable section

suppress_compilation
open Submodule TensorProduct Function
open LinearMap (lTensor rTensor)

variable (R : Type*) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable (N : Type*) [AddCommGroup N] [Module R N]
variable (P : Type*) [AddCommGroup P] [Module R P]

-- Note : we mostly use `ι →₀ M` to represent the direct sum of `ι.card` copies of `M`, since
-- it is faster and easier to use when the flexibility of `DFinsupp`/`DirectSum` is not needed.

variable {M N} in
/-- The linear map on direct sums induced by an injective linear map is injective. -/
theorem Finsupp.mapRange_injective (ι : Type*) {ψ : M →ₗ[R] N}
    (hinjective : Function.Injective ψ) :
      Function.Injective (Finsupp.mapRange.linearMap ψ : (ι →₀ M) →ₗ[R] ι →₀ N) :=
  fun _ _ h => Finsupp.ext fun i => hinjective <| FunLike.congr_fun h i

open DirectSum in
/-- If `N` is an `R`-module then `Rⁿ ⊗ N ≃ Nⁿ`. -/
@[simps! apply]
def TensorProduct.lid_Finsupp (ι : Type*) [DecidableEq ι] : (ι →₀ R) ⊗[R] N ≃ₗ[R] ι →₀ N := by
  exact TensorProduct.congr (finsuppLEquivDirectSum R R ι) (LinearEquiv.refl R N) ≪≫ₗ
    TensorProduct.directSumLeft R (fun _ : ι => R) N ≪≫ₗ
      (finsuppLEquivDirectSum R (R ⊗[R] N) ι).symm ≪≫ₗ
        Finsupp.mapRange.linearEquiv (TensorProduct.lid R N)

open DirectSum LinearMap in
/-- Applying the linear equivalence `rid_Finsupp` to a simple element `r ⊗ x` of `Rⁿ ⊗ N`. -/
theorem TensorProduct.lid_Finsupp_tmul (ι : Type*) [DecidableEq ι]
    (x : N) (r : ι →₀ R) (i : ι) : lid_Finsupp R N ι (r ⊗ₜ[R] x) i = r i • x := by
  -- It suffices to show the equality holds when `r` is a Kronecker delta.
  -- To show this we recast as an equality of linear maps ...
  suffices ((lid_Finsupp R N ι).toLinearMap ∘ₗ (LinearMap.flip (mk R (ι →₀ R) N) x)) r i =
      Finsupp.mapRange.linearMap (LinearMap.flip (lsmul R N) x) r i by
    rewrite [LinearMap.comp_apply, LinearEquiv.coe_coe, flip_apply, mk_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, flip_apply, lsmul_apply] at this
    exact this
  congr 2
  -- ... and apply the default extensionality theorems (explicit here for clarity).
  refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, flip_apply,
    lid_Finsupp_apply, mk_apply, congr_tmul, LinearEquiv.refl_apply, Finsupp.lsingle_apply,
    finsuppLEquivDirectSum_single, directSumLeft_tmul_lof, finsuppLEquivDirectSum_symm_lof,
    Finsupp.mapRange_single, lid_tmul, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.lsingle_apply, Finsupp.mapRange_single, flip_apply, lsmul_apply]

open DirectSum in
/-- The linear equivalences `lid_Finsupp R - ι` are the components of a natural isomorphism
from the functor `((ι →₀ R) ⊗ -)` to the functor `(ι →₀ -)` in the category of `R`-modules. -/
theorem lTensor_Finsupp_equiv_mapRange (ι : Type*) [DecidableEq ι] (f : M →ₗ[R] N) :
    (lid_Finsupp R N ι).toLinearMap ∘ₗ f.lTensor (ι →₀ R) =
      Finsupp.mapRange.linearMap f ∘ₗ (lid_Finsupp R M ι).toLinearMap := by
  refine TensorProduct.ext' fun x r => Finsupp.ext fun i => ?_
  rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, lid_Finsupp_tmul,
    LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    LinearEquiv.coe_coe, lid_Finsupp_tmul R M ι r x i, LinearMap.map_smul]

open Module.Free DirectSum in
/-- If `M` and `N` are `R`-modules and `M` is finite and free, of rank `n`, then the tensor
product of `M` and `N` is equivalent to a finite direct sum, `M ⊗ N ≃ ⨁ⁿ N`. -/
def lid_finite_free [Module.Finite R M] [Module.Free R M] :
    M ⊗[R] N ≃ₗ[R] ChooseBasisIndex R M →₀ N :=
  TensorProduct.congr (chooseBasis R M).repr (LinearEquiv.refl R N) ≪≫ₗ
    lid_Finsupp R N (ChooseBasisIndex R M)

open Module.Free DirectSum BigOperators Classical in
def lid_finite_free_tmul [Module.Free R M] [Module.Finite R M] (m : M) (n : N)
    (i : ChooseBasisIndex R M) :
      lid_finite_free R M N (m ⊗ₜ[R] n) i = (chooseBasis R M).repr m i • n := by
  unfold lid_finite_free
  rw [LinearEquiv.trans_apply, congr_tmul, LinearEquiv.refl_apply, lid_Finsupp_tmul]

open DirectSum Module.Free in
/-- If `M` is a free and finite `R`-module then the linear equivalences `lid_finite_free R M -`
are the components of a natural isomorphism from `M ⊗ -` to `ChooseBasisIndex R M →₀ -`. -/
theorem lTensor_finite_free_equiv_mapRange [Module.Finite R M] [Module.Free R M]
    (f : N →ₗ[R] P) :
    (lid_finite_free R M P).toLinearMap ∘ₗ f.lTensor M =
      Finsupp.mapRange.linearMap f ∘ₗ (lid_finite_free R M N).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  unfold lid_finite_free
  have : TensorProduct.congr (chooseBasis R M).repr (LinearEquiv.refl R P) ∘ₗ f.lTensor M =
      f.lTensor ((ChooseBasisIndex R M) →₀ R) ∘ₗ
        TensorProduct.congr (chooseBasis R M).repr (LinearEquiv.refl R N) :=
    TensorProduct.ext' fun _ _ => rfl
  rw [LinearEquiv.coe_trans, LinearMap.comp_assoc, this, LinearEquiv.coe_trans,
    ← LinearMap.comp_assoc, lTensor_Finsupp_equiv_mapRange R N P _ f, LinearMap.comp_assoc]

variable {R M N P}

variable (R M) in
open DirectSum Module.Free in
/-- If `M`, `N` and `P` are `R`-modules, `M` is finite and free, and `f : N → P` is an injective
linear map, the tensor product `f.lTensor M` of the identity `M → M` with `f` is also injective. -/
theorem lTensor_finite_free_injective_of_injective [Module.Free R M] [Module.Finite R M]
    (f : N →ₗ[R] P) (hf : Function.Injective f) : Function.Injective (f.lTensor M) := by
  rewrite [← (f.lTensor M).id_comp, ← LinearEquiv.refl_toLinearMap,
      ← (lid_finite_free R M P).self_trans_symm, LinearEquiv.coe_trans, LinearMap.comp_assoc,
      lTensor_finite_free_equiv_mapRange, LinearMap.coe_comp, LinearEquiv.coe_coe,
      EmbeddingLike.comp_injective, LinearMap.coe_comp, LinearEquiv.coe_coe,
      EquivLike.injective_comp]
  exact Finsupp.mapRange_injective R _ hf

/-- If `y : M × N →₀ ℤ` (representing an element of the free abelian group on `M × N`) is in the
subgroup `TensorProductFinsupp.Null R M N`, return a finite subset `t` of `M × N →₀ ℤ` and a
finite subset `s` of `M` such that each member of `t` may be expressed in the form of a member
of `TensorProductFinsupp.NullGen R M N` whose first coordinate belongs to `s` (or is the sum of
two members of `s`, or the scalar product of some `r : R` and `m ∈ s`). -/
theorem mem_kernel_witness_left [DecidableEq M] [DecidableEq (M × N →₀ ℤ)] {x : M × N →₀ ℤ}
    (H : x ∈ TensorProductFinsupp.Null R M N) :
      ∃ (t : Finset (M × N →₀ ℤ)), x ∈ span ℤ t ∧ ∃ (s : Finset M), ∀ p ∈ t,
        (∃ (m₁ m₂ : M) (n : N), p = .single (m₁ + m₂, n) 1 - .single (m₁, n) 1 - .single (m₂, n) 1
          ∧ m₁ ∈ s ∧ m₂ ∈ s) ∨
        (∃ (m : M) (n₁ n₂ : N), p = .single (m, n₁ + n₂) 1 - .single (m, n₁) 1 - .single (m, n₂) 1
          ∧ m ∈ s) ∨
        (∃ (r : R) (m : M) (n : N), p = .single (m, r • n) 1 - .single (r • m, n) 1
          ∧ m ∈ s) := by
  unfold TensorProductFinsupp.Null at H
  rewrite [← span_int_eq_addSubgroup_closure, mem_toAddSubgroup] at H
  have ⟨t, ht, hyt⟩ := mem_span_finite_of_mem_span H
  refine ⟨t, hyt, ?_⟩
  revert ht
  refine Finset.induction_on t (fun _ => ⟨∅, fun.⟩) fun {p'} {t'} hp' ih hpt' => ?_
  have ⟨s, hs⟩ := ih <| subset_trans (Finset.coe_subset.mpr <| Finset.subset_insert p' ↑t') hpt'
  obtain (⟨m₁', m₂', n', rfl⟩ | ⟨m', n₁', n₂', rfl⟩ | ⟨r', m', n', rfl⟩) :=
      hpt' <| Finset.mem_insert_self p' t'
  . refine ⟨insert m₂' (insert m₁' s), fun p => ?_⟩
    rewrite [Finset.mem_insert]
    rintro (rfl | hpt)
    . left; exact ⟨m₁', m₂', n', rfl, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
        Finset.mem_insert_self _ _⟩
    . obtain (⟨m₁, m₂, n, rfl, hm₁, hm₂⟩ | ⟨m, n₁, n₂, rfl, hm⟩ | ⟨r, m, n, rfl, hm⟩) := hs p hpt
      . left; exact ⟨m₁, m₂, n, rfl, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm₁),
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm₂)⟩
      . right; left; exact ⟨m, n₁, n₂, rfl, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)⟩
      . right; right; exact ⟨r, m, n, rfl, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)⟩
  . refine ⟨insert m' s, fun p => ?_⟩
    rewrite [Finset.mem_insert]
    rintro (rfl | hpt)
    . right; left
      exact ⟨m', n₁', n₂', rfl, Finset.mem_insert_self _ _⟩
    . obtain (⟨m₁, m₂, n, rfl, hm₁, hm₂⟩ | ⟨m, n₁, n₂, rfl, hm⟩ | ⟨r, m, n, rfl, hm⟩) := hs p hpt
      . left; exact ⟨m₁, m₂, n, rfl, Finset.mem_insert_of_mem hm₁, Finset.mem_insert_of_mem hm₂⟩
      . right; left; exact ⟨m, n₁, n₂, rfl, Finset.mem_insert_of_mem hm⟩
      . right; right; exact ⟨r, m, n, rfl, Finset.mem_insert_of_mem hm⟩
  . refine ⟨insert m' s, fun p => ?_⟩
    rewrite [Finset.mem_insert]
    rintro (rfl | hpt)
    . right; right
      exact ⟨r', m', n', rfl, Finset.mem_insert_self _ _⟩
    . obtain (⟨m₁, m₂, n, rfl, hm₁, hm₂⟩ | ⟨m, n₁, n₂, rfl, hm⟩ | ⟨r, m, n, rfl, hm⟩) := hs p hpt
      . left; exact ⟨m₁, m₂, n, rfl, Finset.mem_insert_of_mem hm₁, Finset.mem_insert_of_mem hm₂⟩
      . right; left; exact ⟨m, n₁, n₂, rfl, Finset.mem_insert_of_mem hm⟩
      . right; right; exact ⟨r, m, n, rfl, Finset.mem_insert_of_mem hm⟩

open TensorProductFinsupp in
/-- If `M` and `N` are `R`-modules, `M` has a basis `ℰ`, and `x : M × N →₀ ℤ` (representing an
element of the free abelian group on `M × N`), if `ψ : N → P` is an injective linear map,
and if the image `y` of `x` in `M × P →₀ ℤ` is in the subgroup `TensorProductFinsupp.Null R M P`,
then there is a finite subfamily `κ` of `ℰ` with span `L` and an element `w : L × N →₀ ℤ`
for which the image `z` of `w` in `L × P →₀ ℤ` is in `TensorProductFinsupp.Null R L P`
and the image of `w` in `M × N →₀ ℤ` is equal to `x`.

                                   (1 × ψ)
            w : L × N →₀ ℤ    -----------------→    z : L × P →₀ ℤ
                  |                                       |
                  | (L.subtype × 1)                       | (L.subtype × 1)
                  |                                       |
                  ↓                (1 × ψ)                ↓
            x : M × N →₀ ℤ    -----------------→    y : M × P →₀ ℤ

This lemma is auxiliary to `lTensor_free_injective_of_injective.aux`. -/
theorem lTensor_free_injective_of_injective.aux [DecidableEq M] [DecidableEq P] [Module.Free R M]
    {x : M × N →₀ ℤ} {ψ : N →ₗ[R] P} (hψ : Injective ψ) (hy : lEmbed M hψ x ∈ Null R M P) :
      ∃ (L : Submodule R M) (_ : Module.Free R L) (_ : L.FG) (w : L × N →₀ ℤ),
        rEmbed N L.injective_subtype w = x ∧ lEmbed L hψ w ∈ Null R L P := by
  -- Choose a basis for `M` and a finite subfamily `κ` whose span `L` is large enough
  -- to express the equation testifying that `y ∈ Null R M N`.
  have ⟨t, hyt, s, hts⟩ := mem_kernel_witness_left hy
  obtain ⟨f, hf⟩ := mem_span_finset.mp hyt
  let ⟨⟨ι, ℰ⟩⟩ := ‹Module.Free R M›
  haveI : DecidableEq ι := Classical.decEq ι
  let κ := (s ∪ (x.support.image Prod.fst)).sup fun m => (ℰ.repr m).support
  let L := span R (ℰ '' κ)
  let ℱ := Basis.span (ℰ.linearIndependent.comp ((↑) : κ → ι) Subtype.val_injective)
  rewrite [Set.range_comp, Subtype.range_val_subtype, Finset.setOf_mem] at ℱ
  -- By construction there exists `w : L × N →₀ ℤ` whose image in `M × N →₀ ℤ` is equal to `x`.
  have hw : rEmbed N _ (rEmbed_comap N _ x) = x :=
    rEmbed_map_comap_subtype (fun p hp => (Basis.mem_span_image _).mpr <|
      fun a ha => Finset.mem_sup.mpr ⟨p.fst, Finset.mem_union_right _ <|
        Finset.mem_image.mpr ⟨p, hp, rfl⟩, ha⟩ : ∀ p : M × N, p ∈ x.support → p.fst ∈ L)
  -- Furthermore, `L` contains every member of `s`.
  let stoL {m : M} (hm : m ∈ s) : L := ⟨m, by
    unfold_let L κ
    rewrite [Basis.mem_span_image, Finset.coe_subset]
    exact fun i hi => Finset.mem_sup.mpr ⟨m, Finset.mem_union.mpr (.inl hm), hi⟩⟩
  -- We claim that `L` is "large enough".
  refine ⟨L, ⟨⟨κ, ℱ⟩⟩, ⟨κ.image ℰ, by rw [Finset.coe_image]⟩, rEmbed_comap N _ x, hw, ?_⟩
  -- Chase the diagram from `x` to `z` in two different ways.
  let z := rEmbed_comap P L.injective_subtype (lEmbed M hψ x)
  have h₁ : lEmbed L hψ (rEmbed_comap N L.injective_subtype x) = z := by
    rw [← rEmbed_comap_map L.injective_subtype (lEmbed L hψ _), ← lEmbed_rEmbed, hw]
  -- The relation `hf` in `M × P →₀ ℤ` is reflected in `L × P →₀ ℤ'.
  have h₂ : z = t.attach.sum fun p => f p.val • rEmbed_comap P L.injective_subtype p := by
    unfold_let z
    unfold rEmbed_comap
    ext a
    rewrite [← hf, Finsupp.comapDomain_apply, ← Finset.sum_attach,
      Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
    exact Finset.sum_congr rfl fun p _ => by
      rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.comapDomain_apply]
  -- Verify that `z` is eligible for membership in `Null R L P`.
  rewrite [h₁, h₂]
  unfold TensorProductFinsupp.Null rEmbed_comap
  rewrite [← span_int_eq_addSubgroup_closure, mem_toAddSubgroup]
  apply sum_mem
  rintro p -
  refine zsmul_mem (subset_span ?_) _
  obtain (⟨m₁, m₂, n, hp, hm₁, hm₂⟩ | ⟨m, n₁, n₂, hp, hm⟩ | ⟨r, m, n, hp, hm⟩) :=
      hts p.val p.property
  . left
    refine ⟨stoL hm₁, stoL hm₂, n, Finsupp.ext fun (m', n') => ?_⟩
    simp? [hp, Finsupp.single_apply,
        Subtype.ext_iff] says simp only [coeSubtype, hp, Finsupp.comapDomain_apply, Prod_map,
        id_eq, Finsupp.coe_sub, Pi.sub_apply, ne_eq, Prod.mk.injEq, not_and,
        Finsupp.single_apply, AddSubmonoid.mk_add_mk, Subtype.ext_iff]
  . right; left
    refine ⟨stoL hm, n₁, n₂, Finsupp.ext fun (m', n') => ?_⟩
    simp? [hp, Finsupp.single_apply,
        Subtype.ext_iff] says simp only [coeSubtype, hp, Finsupp.comapDomain_apply, Prod_map,
        id_eq, Finsupp.coe_sub, Pi.sub_apply, ne_eq, Prod.mk.injEq, not_and,
        Finsupp.single_apply, Subtype.ext_iff]
  . right; right
    refine ⟨r, stoL hm, n, Finsupp.ext fun (m', n') => ?_⟩
    simp? [hp, Finsupp.single_apply,
        Subtype.ext_iff] says simp only [coeSubtype, hp, Finsupp.comapDomain_apply, Prod_map,
        id_eq, Finsupp.coe_sub, Pi.sub_apply, ne_eq, Prod.mk.injEq, not_and,
        Finsupp.single_apply, SetLike.mk_smul_mk, Subtype.ext_iff]

open TensorProductFinsupp in
theorem lTensor_eq_zero_iff {ψ : N →ₗ[R] P} (hψ : Injective ψ) {x : M ⊗[R] N} :
    ψ.lTensor M x = 0 ↔
      lEmbed M hψ (Quotient.out' <| (TensorProductFinsupp.Equiv R M N).symm x) ∈ Null R M P := by
  rw [← QuotientAddGroup.eq_zero_iff, ← QuotientAddGroup.mk'_apply, mk'_lEmbed,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.out_eq',
    ← (TensorProductFinsupp.Equiv R M P).map_eq_zero_iff, ← lTensor_equiv',
    LinearEquiv.apply_symm_apply]

variable (M) in
open TensorProductFinsupp in
/-- If `M`, `N` and `P` are `R`-modules, `M` is free, and `ψ` is an injective linear map `N → P`,
then `ψ.lTensor M`, the tensor product of the identity `M → M` with `ψ`, is also injective. -/
theorem lTensor_free_injective_of_injective [DecidableEq M] [DecidableEq P]
    [Module.Free R M]
    {ψ : N →ₗ[R] P} (hψ : Injective ψ) : Injective (ψ.lTensor M) := by
  -- Assuming `ψ.lTensor M x = 0`, show `x = 0`.
  rewrite [injective_iff_map_eq_zero]
  intro x hx₀
  -- Choose a representative `x'` of `x` in the free abelian group `M × N →₀ ℤ`.
  let x' := Quotient.out' <| (TensorProductFinsupp.Equiv R M N).symm x
  -- Then the image `y'` of `x'` in `M × P →₀ ℤ` is in `TensorProductFinsupp.Null R M P`.
  have hy' : lEmbed M hψ x' ∈ Null R M P := (lTensor_eq_zero_iff hψ).mp hx₀
  -- Apply the auxiliary lemma to obtain `ψ.lTensor L x = 0` where `L` is finite and free.
  have ⟨L, hfree, hfg, w', hx', hz'⟩ := lTensor_free_injective_of_injective.aux hψ hy'
  haveI : Module.Finite R L := ⟨(fg_top L).mpr hfg⟩
  -- Descend to the quotient and apply `lTensor_finite_free_injective_of_injective`.
  rewrite [show x = 0 ↔ (L.subtype.rTensor N <| TensorProductFinsupp.Equiv R L N <|
      QuotientAddGroup.mk' _ w') = L.subtype.rTensor N 0 by
    rw [(L.subtype.rTensor N).map_zero, rTensor_equiv', ← mk'_rEmbed, hx',
      QuotientAddGroup.mk'_apply, QuotientAddGroup.out_eq', LinearEquiv.apply_symm_apply]]
  apply congrArg (L.subtype.rTensor N)
  rewrite [← LinearMap.map_eq_zero_iff _ (lTensor_finite_free_injective_of_injective R L ψ hψ),
    lTensor_equiv', ← mk'_lEmbed L hψ, LinearEquiv.map_eq_zero_iff, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff]
  exact hz'
