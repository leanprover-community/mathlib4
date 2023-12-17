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

variable {M} {N} in
/-- The linear map on direct sums induced by an injective linear map is injective. -/
theorem DFinsupp.mapRange_injective (ι : Type*) {ψ : M →ₗ[R] N}
    (hinjective : Function.Injective ψ) :
      Function.Injective (DFinsupp.mapRange.linearMap (fun _ : ι => ψ)) :=
  fun _ _ h => DirectSum.ext R fun i => hinjective <| (DirectSum.ext_iff R).mp h i

open DirectSum in
/-- If `N` is an `R`-module then `Rⁿ ⊗ N ≃ Nⁿ`. -/
@[simps! apply]
def TensorProduct.rid_DirectSum (ι : Type*) [DecidableEq ι] :
    (N ⊗[R] ⨁ _ : ι, R) ≃ₗ[R] (⨁ _ : ι, N) :=
  TensorProduct.directSumRight R N (fun _ : ι => R) ≪≫ₗ
    DFinsupp.mapRange.linearEquiv (fun _ : ι => TensorProduct.rid R N)

open DirectSum LinearMap in
/-- Applying the linear equivalence `rid_DirectSum` to a simple element `x ⊗ r` of `N ⊗ Rⁿ`. -/
theorem TensorProduct.rid_DirectSum_tmul [DecidableEq R] (ι : Type*) [DecidableEq ι]
    (x : N) (r : ⨁ _ : ι, R) (i : ι) : rid_DirectSum R N ι (x ⊗ₜ[R] r) i = r i • x := by
  -- It suffices to show the equality holds when `r` is a Kronecker delta.
  -- To show this we recast as an equality of linear maps ...
  suffices ((rid_DirectSum R N ι : N ⊗[R] (⨁ _ : ι, R) →ₗ[R] (⨁ _ : ι, N)) ∘ₗ
        mk R N (⨁ _ : ι, R) x) r i =
      DFinsupp.mapRange.linearMap (fun _ => LinearMap.flip (lsmul R N) x) r i by
    rewrite [LinearMap.comp_apply, LinearEquiv.coe_coe, mk_apply,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, flip_apply, lsmul_apply] at this
    exact this
  congr 2
  -- ... and apply the default extensionality theorems (explicit here for clarity).
  refine DirectSum.linearMap_ext R fun i : ι => LinearMap.ext_ring ?_
  rewrite [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, rid_DirectSum_apply, mk_apply, directSumRight_tmul_lof]
  erw [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange.linearMap_apply]
  rw [← single_eq_lof, ← single_eq_lof, DFinsupp.mapRange_single, DFinsupp.mapRange_single,
    LinearEquiv.coe_coe, rid_tmul, flip_apply, lsmul_apply]

open DirectSum in
/-- If `N` is an `R`-module then `Rⁿ ⊗ N ≃ Nⁿ`. -/
@[simps! apply]
def TensorProduct.lid_DirectSum (ι : Type*) [DecidableEq ι] :
    (⨁ _ : ι, R) ⊗[R] N ≃ₗ[R] (⨁ _ : ι, N) :=
  TensorProduct.comm R (⨁ _ : ι, R) N ≪≫ₗ TensorProduct.rid_DirectSum R N ι

open DirectSum in
/-- Applying the linear equivalence `rid_Finprod` to a simple element `x ⊗ r` of `N ⊗ Rⁿ`. -/
theorem TensorProduct.lid_DirectSum_tmul [DecidableEq R] (ι : Type*) [DecidableEq ι]
    (x : N) (r : ⨁ _ : ι, R) (i : ι) :
      lid_DirectSum R N ι (r ⊗ₜ[R] x) i = r i • x := by
  unfold lid_DirectSum
  rw [LinearEquiv.trans_apply, comm_tmul, rid_DirectSum_tmul]

open Module.Free DirectSum in
/-- If `M` and `N` are `R`-modules and `N` is finite and free, of rank `n`, then the tensor
product of `M` and `N` is equivalent to a finite direct sum, `M ⊗ N ≃ ⨁ⁿ M`. -/
def rid_finite_free [Module.Finite R N] [Module.Free R N] :
    M ⊗[R] N ≃ₗ[R] ⨁ _ : Fin (Fintype.card (ChooseBasisIndex R N)), M :=
  TensorProduct.congr (LinearEquiv.refl R M)
    (((chooseBasis R N).reindex (Fintype.equivFin (ChooseBasisIndex R N))).equivFun ≪≫ₗ
      (linearEquivFunOnFintype R (Fin <| Fintype.card <| ChooseBasisIndex R N)
        (fun _ => R)).symm) ≪≫ₗ
    rid_DirectSum R M (Fin <| Fintype.card <| ChooseBasisIndex R N)

open Module.Free DirectSum in
/-- If `M` and `N` are `R`-modules and `M` is finite and free, of rank `n`, then the tensor
product of `M` and `N` is equivalent to a finite direct sum, `M ⊗ N ≃ ⨁ⁿ N`. -/
def lid_finite_free [Module.Finite R M] [Module.Free R M] :
    M ⊗[R] N ≃ₗ[R] ⨁ _ : Fin (Fintype.card (ChooseBasisIndex R M)), N :=
  TensorProduct.congr
    (((chooseBasis R M).reindex (Fintype.equivFin (ChooseBasisIndex R M))).equivFun ≪≫ₗ
      (linearEquivFunOnFintype R (Fin <| Fintype.card <| ChooseBasisIndex R M)
        (fun _ => R)).symm) (LinearEquiv.refl R N) ≪≫ₗ
    lid_DirectSum R N (Fin <| Fintype.card <| ChooseBasisIndex R M)

open DirectSum in
/-- If `M` and `N` are `R`-modules and `f : M → N` a linear map, the tensor product of `f` and the
identity `Rⁿ → Rⁿ` on a finite product is related by linear equivalences to the
natural linear map `⨁ⁿ M → ⨁ⁿ N` induced by `f`. -/
theorem rTensor_DirectSum_equiv_mapRange [DecidableEq R] (n : ℕ) (f : M →ₗ[R] N) :
    (rid_DirectSum R N (Fin n) : (N ⊗[R] ⨁ _ : Fin n, R) →ₗ[R] ⨁ _, N) ∘ₗ f.rTensor (⨁ _, R) =
      DFinsupp.mapRange.linearMap (fun _ : (Fin n) => f) ∘ₗ
        (rid_DirectSum R M (Fin n) : (M ⊗[R] ⨁ _, R) →ₗ[R] ⨁ _, M) := by
  refine TensorProduct.ext' fun x r => DFinsupp.ext fun i => ?_
  rewrite [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, rid_DirectSum_tmul]
  erw [LinearMap.comp_apply, rid_DirectSum_tmul]
  rw [LinearMap.map_smul]

open DirectSum Module.Free in
/-- If `M`, `N` and `P` are `R`-modules, `N` is finite and free of rank `n`, and `f : M → P` is
a linear map, the tensor product of `f` and the identity `N → N` is related by linear equivalences
given by `rid_finite_free` to the natural linear map `⨁ⁿ M → ⨁ⁿ P` induced by `f`.
(This establishes a natural isomorphism between the functors `(· ⊗ N)` and `(⨁ⁿ ·)` whose
component at `M` is `rid_finite_free R N M`.) -/
theorem rTensor_finite_free_equiv_mapRange [DecidableEq R] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] P) :
    (rid_finite_free R P N : P ⊗[R] N →ₗ[R] ⨁ _ : Fin _, P) ∘ₗ f.rTensor N =
      DFinsupp.mapRange.linearMap (fun _ : (Fin (Fintype.card (ChooseBasisIndex R N))) => f) ∘ₗ
        (rid_finite_free R M N : M ⊗[R] N →ₗ[R] ⨁ _ : Fin _, M) := by
  let ι := ChooseBasisIndex R N
  let n := Fintype.card ι
  let ℰ := chooseBasis R N
  let e₀ := TensorProduct.congr (LinearEquiv.refl R M) <|
    (ℰ.reindex (Fintype.equivFin ι)).equivFun ≪≫ₗ
      (linearEquivFunOnFintype R (Fin n) (fun _ => R)).symm
  let e₁ := rid_DirectSum R M (Fin n)
  let e₀' := TensorProduct.congr (LinearEquiv.refl R P) <|
    (ℰ.reindex (Fintype.equivFin ι)).equivFun ≪≫ₗ
      (linearEquivFunOnFintype R (Fin n) (fun _ => R)).symm
  let e₁' := rid_DirectSum R P (Fin n)
  let φ := f.rTensor N
  let φ' := f.rTensor (⨁ _ : Fin n, R)
  let ψ := DFinsupp.mapRange.linearMap (fun _ : (Fin (Fintype.card (ChooseBasisIndex R N))) => f)
  refine LinearMap.ext fun x => ?_
  change e₁' ((e₀' ∘ₗ φ) x) = (ψ ∘ₗ (e₁ : (M ⊗[R] ⨁ _, R) →ₗ[R] ⨁ _, M)) (e₀ x)
  rewrite [show e₀' ∘ₗ φ = φ' ∘ₗ e₀ from TensorProduct.ext' fun _ _ => rfl,
    LinearMap.comp_apply, LinearEquiv.coe_coe, ← LinearEquiv.coe_coe, ← LinearMap.comp_apply,
    rTensor_DirectSum_equiv_mapRange R M P n f]
  unfold_let e₀ e₁ ψ
  rfl

variable {M P} in
open DirectSum Module.Free in
/-- If `M`, `N` and `P` are `R`-modules, `N` is finite and free, and `f : M → P` is an injective
linear map, the tensor product `f.rTensor N` of `f` with the identity `N → N` is also injective. -/
theorem rTensor_finite_free_injective_of_injective [DecidableEq R] [Module.Free R N]
    [Module.Finite R N] (f : M →ₗ[R] P) (hf : Function.Injective f) :
      Function.Injective (f.rTensor N) := by
  rewrite [← (f.rTensor N).id_comp, ← LinearEquiv.refl_toLinearMap,
      ← (rid_finite_free R P N).self_trans_symm, LinearEquiv.coe_trans, LinearMap.comp_assoc,
      rTensor_finite_free_equiv_mapRange, LinearMap.coe_comp, LinearEquiv.coe_coe,
      EmbeddingLike.comp_injective]
  erw [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp]
  exact DFinsupp.mapRange_injective R (Fin (Fintype.card (ChooseBasisIndex R N))) hf

variable {N P} in
/-- If `M`, `N` and `P` are `R`-modules, `M` is finite and free, and `f : N → P` is an injective
linear map, the tensor product `f.lTensor M' of the identity `M → M` with `f` is also injective. -/
theorem lTensor_finite_free_injective_of_injective [DecidableEq R] [Module.Free R M]
    [Module.Finite R M] (f : N →ₗ[R] P) (hf : Function.Injective f) :
      Function.Injective (f.lTensor M) := by
  rw [← LinearMap.comm_comp_rTensor_comp_comm_eq]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.bijective_comp,
    EmbeddingLike.comp_injective, EquivLike.injective_comp]
  exact rTensor_finite_free_injective_of_injective R M f hf

variable {R} {M} {N} in
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

variable {R} {M} {N} {P} in
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
theorem lTensor_free_injective_of_injective.aux [DecidableEq M] [DecidableEq P]
    [DecidableEq (M × N →₀ ℤ)] [Module.Free R M] {x : M × N →₀ ℤ} {ψ : N →ₗ[R] P}
    (hψ : Injective ψ) (hy : lEmbed M hψ x ∈ TensorProductFinsupp.Null R M P) :
      ∃ (L : Submodule R M) (_ : Module.Free R L) (_ : L.FG) (w : L × N →₀ ℤ),
        rEmbed N L.injective_subtype w = x ∧ lEmbed L hψ w ∈ TensorProductFinsupp.Null R L P := by
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
/-- If `M`, `N` and `P` are `R`-modules, `M` is free, and `ψ` is an injective linear map `N → P`,
then `ψ.lTensor M`, the tensor product of the identity `M → M` with `ψ`, is also injective. -/
theorem lTensor_free_injective_of_injective [DecidableEq R] [DecidableEq M] [DecidableEq P]
    [DecidableEq (M × N →₀ ℤ)] [Module.Free R M]
    (ψ : N →ₗ[R] P) (hψ : Injective ψ) : Injective (ψ.lTensor M) := by
  -- Assuming `ψ.lTensor M x = 0`, show `x = 0`.
  rewrite [injective_iff_map_eq_zero]
  intro x hx₀
  -- Choose a representative `x'` of `x` in the free abelian group `M × N →₀ ℤ`.
  let x' := Quotient.out' <| (TensorProductFinsupp.Equiv R M N).symm x
  -- Then the image `y'` of `x'` in `M × P →₀ ℤ` is in `TensorProductFinsupp.Null R M P`.
  have hy' : lEmbed M hψ x' ∈ Null R M P := by
    have : lEmbed M hψ x' ∈ Null R M P ↔ QuotientAddGroup.mk' (Null R M P) (lEmbed M hψ x') =
        ((TensorProductFinsupp.Equiv R M P).symm <| ψ.lTensor M <|
          TensorProductFinsupp.Equiv R M N <| (TensorProductFinsupp.Equiv R M N).symm x) := by
      rw [LinearEquiv.apply_symm_apply, hx₀, LinearEquiv.map_zero,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [this, lTensor_equiv', LinearEquiv.symm_apply_apply, mk'_lEmbed,
      QuotientAddGroup.mk'_apply, QuotientAddGroup.out_eq']
  -- Apply the auxiliary lemma to reduce to `ψ.lTensor L x = 0` where `L` is finite and free.
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
