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
    (x : N) (r : ⨁ _ : ι, R) (i : ι) :
      rid_DirectSum R N ι (x ⊗ₜ[R] r) i = r i • x := by
  -- It suffices to show the equality holds when `r` is a Kronecker delta.
  -- To show this we recast as an equality of linear maps ...
  have h : r i • x = DFinsupp.mapRange.linearMap (fun _ => flip (lsmul R N) x) r i := by
    rw [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, flip_apply, lsmul_apply]
  rw [h, ← mk_apply, ← LinearEquiv.coe_coe, ← LinearMap.comp_apply]
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
/-- If `M` and `N` are `R`-modules and `M` is finite and free, of rank `n`, then the tensor
product of `M` and `N` is equivalent to a finite direct sum, `N ⊗ M ≃ ⨁ⁿ N`. -/
def rid_finite_free [Module.Finite R M] [Module.Free R M] :
    N ⊗[R] M ≃ₗ[R] ⨁ _ : Fin (Fintype.card (ChooseBasisIndex R M)), N :=
  TensorProduct.congr (LinearEquiv.refl R N)
    (((chooseBasis R M).reindex (Fintype.equivFin (ChooseBasisIndex R M))).equivFun ≪≫ₗ
      (linearEquivFunOnFintype R (Fin <| Fintype.card <| ChooseBasisIndex R M)
        (fun _ => R)).symm) ≪≫ₗ
    rid_DirectSum R N (Fin <| Fintype.card <| ChooseBasisIndex R M)

open Module.Free DirectSum in
/-- If `M` and `N` are `R`-modules and `M` is finite and free, of rank `n`, then the tensor
product of `M` and `N` is equivalent to a finite direct sum, `N ⊗ M ≃ ⨁ⁿ N`. -/
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
natural linear map `⨁ⁿ M → ⨁ⁿ N` induced by `f`.
 -/
theorem rTensor_DirectSum_equiv_mapRange [DecidableEq R] (n : ℕ) (f : M →ₗ[R] N) :
    (rid_DirectSum R N (Fin n) : (N ⊗[R] ⨁ _ : Fin n, R) →ₗ[R] ⨁ _, N) ∘ₗ f.rTensor (⨁ _, R) =
      DFinsupp.mapRange.linearMap (fun _ : (Fin n) => f) ∘ₗ
        (rid_DirectSum R M (Fin n) : (M ⊗[R] ⨁ _, R) →ₗ[R] ⨁ _, M) := by
  refine TensorProduct.ext' fun x r => DFinsupp.ext fun i => ?_
  rewrite [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, rid_DirectSum_tmul]
  erw [LinearMap.comp_apply, rid_DirectSum_tmul]
  rw [LinearMap.map_smul]

open DirectSum Module.Free in
/-- If `M`, `N` and `P` are `R`-modules, `M` is finite and free of rank `n`, and `f : N → P` is
a linear map, the tensor product of `f` and the identity `M → M` is related by linear equivalences
given by `rid_finite_free` to the natural linear map `⨁ⁿ N → ⨁ⁿ P` induced by `f`.
(This establishes a natural isomorphism between the functors `(· ⊗ M)` and `(⨁ⁿ ·)` whose
component at `N` is `rid_finite_free R M N`.) -/
theorem rTensor_finite_free_equiv_mapRange [DecidableEq R] [Module.Finite R M] [Module.Free R M]
    (f : N →ₗ[R] P) :
    (rid_finite_free R M P : P ⊗[R] M →ₗ[R] ⨁ _ : Fin _, P) ∘ₗ f.rTensor M =
      DFinsupp.mapRange.linearMap (fun _ : (Fin (Fintype.card (ChooseBasisIndex R M))) => f) ∘ₗ
        (rid_finite_free R M N : N ⊗[R] M →ₗ[R] ⨁ _ : Fin _, N) := by
  let ι := ChooseBasisIndex R M
  let n := Fintype.card ι
  let ℰ := chooseBasis R M
  let e₀ := TensorProduct.congr (LinearEquiv.refl R N) <|
    (ℰ.reindex (Fintype.equivFin ι)).equivFun ≪≫ₗ
      (linearEquivFunOnFintype R (Fin n) (fun _ => R)).symm
  let e₁ := rid_DirectSum R N (Fin n)
  let e₀' := TensorProduct.congr (LinearEquiv.refl R P) <|
    (ℰ.reindex (Fintype.equivFin ι)).equivFun ≪≫ₗ
      (linearEquivFunOnFintype R (Fin n) (fun _ => R)).symm
  let e₁' := rid_DirectSum R P (Fin n)
  let φ := f.rTensor M
  let φ' := f.rTensor (⨁ _ : Fin n, R)
  let ψ := DFinsupp.mapRange.linearMap (fun _ : (Fin (Fintype.card (ChooseBasisIndex R M))) => f)
  refine LinearMap.ext fun x => ?_
  change e₁' ((e₀' ∘ₗ φ) x) = (ψ ∘ₗ (e₁ : (N ⊗[R] ⨁ _, R) →ₗ[R] ⨁ _, N)) (e₀ x)
  rewrite [show e₀' ∘ₗ φ = φ' ∘ₗ e₀ from TensorProduct.ext' fun _ _ => rfl,
    LinearMap.comp_apply, LinearEquiv.coe_coe, ← LinearEquiv.coe_coe, ← LinearMap.comp_apply,
    rTensor_DirectSum_equiv_mapRange R N P n f]
  unfold_let e₀ e₁ ψ
  rfl

variable {N P} in
open DirectSum Module.Free in
/-- If `M`, `N` and `P` are `R`-modules, `M` is finite and free, and `f : N → P` is an injective
linear map, the tensor product of `f` and the identity `M → M` is also injective. -/
theorem rTensor_finite_free_injective_of_injective [DecidableEq R] [Module.Free R M]
    [Module.Finite R M] (f : N →ₗ[R] P) (hf : Function.Injective f) :
      Function.Injective (f.rTensor M) := by
  rewrite [← (f.rTensor M).id_comp, ← LinearEquiv.refl_toLinearMap,
      ← (rid_finite_free R M P).self_trans_symm, LinearEquiv.coe_trans, LinearMap.comp_assoc,
      rTensor_finite_free_equiv_mapRange, LinearMap.coe_comp, LinearEquiv.coe_coe,
      EmbeddingLike.comp_injective]
  erw [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp]
  exact DFinsupp.mapRange_injective R (Fin (Fintype.card (ChooseBasisIndex R M))) hf

variable {N P} in
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
open TensorProductFinsupp (lEmbed rEmbed rEmbed_comap rEmbed_map_comap) in
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
  -- Since `1 ⊗ ψ` maps `x` to 0, the element `∑(mᵢ, ψ(nᵢ))` in the free abelian group on
  -- `M × P` is equal to a sum `∑ᵢ∑ⱼ(lᵢⱼ, pᵢⱼ)` of elements in the equivalence class of 0.
  have ⟨t, hyt, s, hts⟩ := mem_kernel_witness_left hy
  obtain ⟨f, hf⟩ := mem_span_finset.mp hyt
  -- Choose a basis and take a finite subfamily `κ` whose span `L` contains `s` and each `mᵢ`.
  let ⟨⟨ι, ℰ⟩⟩ := ‹Module.Free R M›
  haveI : DecidableEq ι := Classical.decEq ι
  let κ := (s ∪ (x.support.image Prod.fst)).sup fun m => (ℰ.repr m).support
  let L := span R (ℰ '' κ)
  let ℱ := Basis.span (ℰ.linearIndependent.comp ((↑) : κ → ι) Subtype.val_injective)
  rewrite [Set.range_comp, Subtype.range_val_subtype, Finset.setOf_mem] at ℱ
  -- `L` is large enough that `∑(mᵢ, nᵢ)` lives in the free abelian group on `L × N`.
  have hmem₁ (p : M × N) (hp : p ∈ x.support) : p.fst ∈ L :=
    (Basis.mem_span_image _).mpr <| fun a ha => Finset.mem_sup.mpr
      ⟨p.fst, Finset.mem_union_right _ <| Finset.mem_image.mpr ⟨p, hp, rfl⟩, ha⟩
  let w : L × N →₀ ℤ := rEmbed_comap N L.injective_subtype x
  refine ⟨L, ⟨⟨κ, ℱ⟩⟩, ⟨κ.image ℰ, by rw [Finset.coe_image]⟩, w,
      by rw [rEmbed_map_comap N hmem₁], ?_⟩
  . have hmemL₁ {m : M} (hm : m ∈ s ∨ m ∈ x.support.image Prod.fst) : m ∈ L := by
      unfold_let L κ
      rewrite [Basis.mem_span_image, Finset.coe_subset]
      exact fun i hi => Finset.mem_sup.mpr ⟨m, Finset.mem_union.mpr hm, hi⟩
    -- `L` is large enough that the equation `∑(mᵢ, nᵢ) = ∑ᵢ∑ⱼ(lᵢⱼ, pᵢⱼ)` lives in `L × N →₀ ℤ`.
    let z : L × P →₀ ℤ := t.attach.sum fun p => f p.val • rEmbed_comap P L.injective_subtype p
    -- Prove `w` maps to `z`.
    rewrite [show lEmbed L hψ w = z by
      -- First show that `y` comaps to `z`.
      rewrite [← show rEmbed_comap P L.injective_subtype (lEmbed M hψ x) = z by
        unfold_let z
        rewrite [← hf]
        unfold rEmbed_comap
        ext a
        rewrite [Finsupp.comapDomain_apply, ← Finset.sum_attach, Finsupp.finset_sum_apply,
          Finsupp.finset_sum_apply]
        exact Finset.sum_congr rfl fun p _ => by
          rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.comapDomain_apply]]
      -- Show the diagram (with vertical arrows reversed) commutes.
      unfold_let w
      rewrite [Finsupp.ext_iff']
      refine ⟨Finset.ext fun a => ⟨?_, ?_⟩, fun a ha => ?_⟩
      . unfold lEmbed rEmbed_comap
        rewrite [Finsupp.support_embDomain, Finsupp.comapDomain_support, Finset.mem_map]
        rintro ⟨p, h, rfl⟩
        rewrite [Finset.mem_preimage] at h
        rewrite [Finsupp.comapDomain_support, Finset.mem_preimage, Finsupp.support_embDomain,
          Finset.mem_map]
        exact ⟨Prod.map L.subtype id p, h, rfl⟩
      . unfold lEmbed rEmbed_comap
        rewrite [Finsupp.comapDomain_support, Finset.mem_preimage, Finsupp.support_embDomain,
          Finset.mem_map]
        rintro ⟨p, h₁, h₂⟩
        rewrite [Finsupp.support_embDomain, Finsupp.comapDomain_support, Finset.mem_map]
        refine ⟨(⟨p.fst, hmem₁ p h₁⟩, p.snd), (by rw [Finset.mem_preimage]; exact h₁), ?_⟩
        simpa [Prod.ext_iff, Subtype.ext_iff] using h₂
      . unfold lEmbed rEmbed_comap at ha
        rewrite [Finsupp.support_embDomain, Finsupp.comapDomain_support, Finset.mem_map] at ha
        obtain ⟨p, h, rfl⟩ := ha
        rewrite [Finset.mem_preimage] at h
        unfold lEmbed rEmbed_comap
        have : Prod.map L.subtype id ((Function.Embedding.mk _ (Injective.Prod_map injective_id hψ)) p) =
          (Function.Embedding.mk _ (Injective.Prod_map injective_id hψ)) (Prod.map L.subtype id p) := rfl
        rw [Finsupp.comapDomain_apply,
          show Prod.map L.subtype id
            ((Function.Embedding.mk _ (Injective.Prod_map injective_id hψ)) p) =
              (Function.Embedding.mk _ (Injective.Prod_map injective_id hψ))
                 (Prod.map L.subtype id p) from rfl,
          Finsupp.embDomain_apply, Finsupp.comapDomain_apply, Finsupp.embDomain_apply]]
    unfold TensorProductFinsupp.Null
    rewrite [← span_int_eq_addSubgroup_closure, mem_toAddSubgroup]
    unfold_let z
    apply sum_mem
    rintro p -
    refine zsmul_mem (subset_span ?_) _
    unfold rEmbed_comap
    obtain (⟨m₁, m₂, n, hp, hm₁, hm₂⟩ | ⟨m, n₁, n₂, hp, hm⟩ | ⟨r, m, n, hp, hm⟩) :=
        hts p.val p.property
    . left
      refine ⟨⟨m₁, hmemL₁ (.inl hm₁)⟩, ⟨m₂, hmemL₁ (.inl hm₂)⟩, n, Finsupp.ext fun (m', n') => ?_⟩
      simp? [hp, Finsupp.single_apply,
          Subtype.ext_iff] says simp only [coeSubtype, hp, Finsupp.comapDomain_apply, Prod_map,
          id_eq, Finsupp.coe_sub, Pi.sub_apply, ne_eq, Prod.mk.injEq, not_and,
          Finsupp.single_apply, AddSubmonoid.mk_add_mk, Subtype.ext_iff]
    . right; left
      refine ⟨⟨m, hmemL₁ (.inl hm)⟩, n₁, n₂, Finsupp.ext fun (m', n') => ?_⟩
      simp? [hp, Finsupp.single_apply,
          Subtype.ext_iff] says simp only [coeSubtype, hp, Finsupp.comapDomain_apply, Prod_map,
          id_eq, Finsupp.coe_sub, Pi.sub_apply, ne_eq, Prod.mk.injEq, not_and,
          Finsupp.single_apply, Subtype.ext_iff]
    . right; right
      refine ⟨r, ⟨m, hmemL₁ (.inl hm)⟩, n, Finsupp.ext fun (m', n') => ?_⟩
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
  -- Assuming `ψ.lTensor F x = 0`, show `x = 0`.
  rewrite [injective_iff_map_eq_zero]
  intro x hx₀
  -- Choose a representative `x' = ∑(mᵢ, nᵢ)` of `x` in the free abelian group on `M × N`.
  let x' := Quotient.out' <| (TensorProductFinsupp.Equiv R M N).symm x
  -- Then the image `y'` of `x'` under the map `(1, ψ)` is in `TensorProductFinsupp.Null R M P`.
  have hy' : lEmbed M hψ x' ∈ TensorProductFinsupp.Null R M P := by
    rewrite [← QuotientAddGroup.eq_zero_iff, ← QuotientAddGroup.mk'_apply,
      ← (TensorProductFinsupp.Equiv R M P).symm.map_zero, ← hx₀,
      ← (TensorProductFinsupp.Equiv R M N).apply_symm_apply x]
    unfold_let x'
    rw [mk'_lEmbed, lTensor_equiv',
      (TensorProductFinsupp.Equiv R M P).symm_apply_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.out_eq']
  -- There is a free, finitely generated submodule `L ≤ M` and an element `w' : L × N →₀ ℤ`
  -- whose image in `M × P →₀ ℤ` is equal to `x'` and whose image in `L × P →₀ ℤ` belongs to
  -- `TensorProductFinsupp.Null R L P`.
  have ⟨L, hfree, hfg, w', hx', hz'⟩ := lTensor_free_injective_of_injective.aux hψ hy'
  haveI : Module.Finite R L := ⟨(fg_top L).mpr hfg⟩
  -- Descend to the quotient and apply `lTensor_finite_free_injective_of_injective`.
  unfold_let x' at hx'
  rw [← (TensorProductFinsupp.Equiv R M N).apply_symm_apply x,
      ← QuotientAddGroup.out_eq' ((LinearEquiv.symm (TensorProductFinsupp.Equiv R M N)) x),
      ← QuotientAddGroup.mk'_apply, ← hx', mk'_rEmbed, ← rTensor_equiv',
      ← (L.subtype.rTensor N).map_zero]
  apply congrArg (L.subtype.rTensor N)
  rw [← LinearMap.map_eq_zero_iff _ (lTensor_finite_free_injective_of_injective R L ψ hψ),
    lTensor_equiv', ← mk'_lEmbed L hψ, LinearEquiv.map_eq_zero_iff, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff]
  exact hz'
