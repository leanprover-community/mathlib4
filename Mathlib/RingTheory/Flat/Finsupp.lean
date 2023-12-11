import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.DirectSum.Finsupp

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
open DirectSum in
/-- The natural linear map `⨁̂ⁿ M → ⨁̂ⁿ N` induced on direct sums by a linear map `M → N`. -/
def DirectSum.induced (ι : Type*) [DecidableEq ι] (f : M →ₗ[R] N) :
    (⨁ _ : ι, M) →ₗ[R] (⨁ _ : ι, N) :=
  (DirectSum.toModule R ι (⨁ _i : ι, N) fun i : ι => ((lof R ι (fun _ => N) i) ∘ₗ f))

variable {M} {N} in
open DirectSum in
/-- The natural linear map `F : ⨁̂ⁿ M → ⨁̂ⁿ N` induced on direct sums by a linear map `f : M → N`
satisfies `(F x) i = f (x i)`, for all `x` in `⨁̂ⁿ M`, for each index `i`. -/
theorem DirectSum.induced_apply (ι : Type*) [DecidableEq ι] (f : M →ₗ[R] N)
    (x : ⨁ _ : ι, M) (i : ι) :
      induced R ι f x i = f (x i) := by
  let induced' : (⨁ _ : ι, M) →ₗ[R] (⨁ _ : ι, N) := {
    toFun := DFinsupp.mapRange (fun _ x => f x) (fun _ => f.map_zero)
    map_add' := fun x y => DFinsupp.ext fun i => f.map_add' (x i) (y i)
    map_smul' := fun r x => DFinsupp.ext fun i => f.map_smul r (x i)
  }
  change _ = induced' x i
  conv => rhs ; rewrite [toModule.unique]
  unfold induced
  congr
  ext i x
  rewrite [LinearMap.comp_apply, LinearMap.comp_apply]
  refine DirectSum.ext R fun j => ?_
  change _ = f (lof R ι (fun _ => M) i x j)
  rewrite [component.of]
  split_ifs with h
  . simp? says simp only [eq_rec_constant]
    rw [h, lof_apply]
  . rw [lof_eq_of, of_eq_of_ne _ i j _ h, f.map_zero]

variable {M} {N} in
/-- The linear map on direct sums induced by an injective linear map is injective. -/
theorem DirectSum.induced_injective (ι : Type*) [DecidableEq ι] {ψ : M →ₗ[R] N}
    (hinjective : Function.Injective ψ) : Function.Injective (DirectSum.induced R ι ψ) := by
  refine fun x y h => DirectSum.ext R fun i => ?_
  have : induced R ι ψ x i = induced R ι ψ y i := (DirectSum.ext_iff R).mp h i
  rewrite [induced_apply, induced_apply] at this
  exact hinjective this

-- Auxiliary to the definition of rid_Finprod
private def prod_pi_succ (k : ℕ) : (Fin k.succ → M) ≃ₗ[R] M × (Fin k → M) where
  toFun := fun v => (v 0, Fin.tail v)
  map_add' := fun x y => rfl
  map_smul' := fun x y => rfl
  invFun := fun (h, t) => Fin.cons h t
  left_inv := Fin.cons_self_tail
  right_inv := fun x => by ext ; rfl ; rfl

private theorem prod_pi_succ_apply (k : ℕ) (v : Fin k.succ → M) :
    prod_pi_succ R M k v = (v 0, Fin.tail v) := rfl

private theorem prod_pi_succ_symm_apply (k : ℕ) (v : M × (Fin k → M)) :
    (prod_pi_succ R M k).symm v = Fin.cons v.fst v.snd := rfl

/-- If `N` is an `R`-module then `Rⁿ ⊗ N ≃ Nⁿ`. -/
def TensorProduct.rid_Finprod (n : ℕ) : N ⊗[R] (Fin n → R) ≃ₗ[R] Fin n → N :=
  match n with
  | Nat.zero =>
    -- The zero map is a linear equivalence of zero modules.
    have h₀ : ∀ (x : N ⊗[R] (Fin 0 → R)), x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Matrix.empty_eq y, ← Matrix.zero_empty, tmul_zero]
      | add x y ixh ihy => rw [ixh, ihy, add_zero]
    have h₁ : ∀ (x : Fin 0 → N), x = 0 := fun x => by rw [Matrix.zero_empty, Matrix.empty_eq x]
    { (0 : _ →ₗ[R] _) with
      invFun := 0
      left_inv := fun x => by rewrite [h₀ x] ; rfl
      right_inv := fun x => by rewrite [h₁ x] ; rfl
    }
  | Nat.succ k =>
    (((TensorProduct.congr (LinearEquiv.refl R N) (prod_pi_succ R R k)).trans
      (TensorProduct.prodRight R N R (Fin k → R))).trans
        (LinearEquiv.prod (TensorProduct.rid R N) (rid_Finprod k))).trans
          (prod_pi_succ R N k).symm

open DirectSum BigOperators in
/-- Applying the linear equivalence `rid_Finprod` to a simple element `x ⊗ r` of `N ⊗ Rⁿ`. -/
theorem rid_Finprod_tmul (n : ℕ) (x : N) (r : Fin n → R) :
    ⇑(rid_Finprod R N n) (x ⊗ₜ[R] r) = fun i : Fin n => r i • x := by
  induction n with
  | zero => simp only [Matrix.empty_eq]
  | succ k ih =>
    simp only [rid_Finprod, LinearEquiv.trans_apply, congr_tmul, LinearEquiv.refl_apply,
      LinearEquiv.prod_apply, prodRight, prod_pi_succ_apply]
    dsimp
    rewrite [ih, prod_pi_succ_symm_apply]
    erw [Fin.cons_self_tail (fun i => r i • x)]

open Module.Free DirectSum in
/-- If `M` and `N` are `R`-modules and `M` is finite and free, of rank `n`, then the tensor
product of `M` and `N` is equivalent to a finite direct sum, `N ⊗ M ≃ ⨁̂ⁿ N`. -/
def rid_finite_free [Module.Finite R M] [Module.Free R M] :
    N ⊗[R] M ≃ₗ[R] ⨁ _ : Fin (Fintype.card (ChooseBasisIndex R M)), N :=
  (TensorProduct.congr (LinearEquiv.refl R N)
    ((chooseBasis R M).reindex (Fintype.equivFin (ChooseBasisIndex R M))).equivFun).trans <|
  (rid_Finprod R N (Fintype.card (ChooseBasisIndex R M))).trans <|
  (linearEquivFunOnFintype R (Fin (Fintype.card (ChooseBasisIndex R M))) (fun _ => N)).symm

-- Rewriting lemma auxiliary to rTensor_Finprod_free_equiv_induced
private theorem rTensor_Finprod_equiv_induced.aux (ι : Type*) [DecidableEq ι] (i : ι) (f : M →ₗ[R] N) (x : M) :
    (fun j : ι => Pi.single (f := fun _ => R) i (1 : R) j • f x) =
      fun j : ι => Pi.single (f := fun _ => N) i (f x) j := by
  ext j
  rewrite [Pi.single_apply, Pi.single_apply]
  split_ifs with h
  . exact one_smul R _
  . exact zero_smul R _

open DirectSum in
/-- If `M` and `N` are `R`-modules and `f : M → N` a linear map, the tensor product of `f` and the
identity `Rⁿ → Rⁿ` on a finite product is related by linear equivalences to the
natural linear map `⨁̂ⁿ M → ⨁̂ⁿ N` induced by `f`.

(The mixture of finite products and finite direct sums in this statement is of no mathematical
significance. This lemma is auxiliary to `rTensor_finite_free_equiv_induced`.)
 -/
theorem rTensor_Finprod_equiv_induced (n : ℕ) (f : M →ₗ[R] N) :
    ((rid_Finprod R N n).trans (linearEquivFunOnFintype R (Fin n) (fun _ => N)).symm) ∘ₗ
      rTensor (Fin n → R) f =
        induced R (Fin n) f ∘ₗ
          ((rid_Finprod R M n).trans (linearEquivFunOnFintype R (Fin n) (fun _ => M)).symm) := by
  ext x i
  simp
  have π₀ := rTensor_Finprod_equiv_induced.aux R M N (Fin n) i f x
  have π₁ := rTensor_Finprod_equiv_induced.aux R M M (Fin n) i LinearMap.id x
  simp only [LinearMap.id_apply] at π₁
  rewrite [rid_Finprod_tmul, rid_Finprod_tmul, π₀, π₁,
      ← DFinsupp.single_eq_pi_single, ← DFinsupp.single_eq_pi_single,
      linearEquivFunOnFintype_symm_coe, linearEquivFunOnFintype_symm_coe,
      DirectSum.single_eq_lof R, DirectSum.single_eq_lof R]
  symm
  apply toModule_lof

open DirectSum Module.Free in
/-- If `M`, `N` and `P` are `R`-modules, `M` is finite and free of rank `n`, and `f : N → P` is
a linear map, the tensor product of `f` and the identity `M → M` is related by linear equivalences
given by `rid_finite_free` to the natural linear map `⨁̂ⁿ N → ⨁̂ⁿ P` induced by `f`.
(This establishes a natural isomorphism between the functors `(· ⊗ M)` and `(⨁̂ⁿ ·)` whose
component at `N` is `rid_finite_free R M N`.) -/
theorem rTensor_finite_free_equiv_induced [Module.Finite R M] [Module.Free R M] (f : N →ₗ[R] P) :
    rid_finite_free R M P ∘ₗ rTensor M f =
      induced R (Fin (Fintype.card (ChooseBasisIndex R M))) f ∘ₗ rid_finite_free R M N := by
  let ι := ChooseBasisIndex R M
  let n := Fintype.card ι
  let ℰ := chooseBasis R M
  let e₀' := TensorProduct.congr (LinearEquiv.refl R P) (ℰ.reindex (Fintype.equivFin ι)).equivFun
  let e₁' := rid_Finprod R P n
  let e₂' := (linearEquivFunOnFintype R (Fin n) (fun _ => P)).symm
  let e₀ := TensorProduct.congr (LinearEquiv.refl R N) (ℰ.reindex (Fintype.equivFin ι)).equivFun
  let e₁ := rid_Finprod R N n
  let e₂ := (linearEquivFunOnFintype R (Fin n) (fun _ => N)).symm
  let φ := rTensor M f
  let φ' := rTensor (Fin n → R) f
  let ψ := induced R (Fin (Fintype.card (ChooseBasisIndex R M))) f
  refine LinearMap.ext fun x => ?_
  change e₁'.trans e₂' ((e₀' ∘ₗ φ) x) = (ψ ∘ₗ e₁.trans e₂) (e₀ x)
  rewrite [show e₀' ∘ₗ φ = φ' ∘ₗ e₀ by ext x; simp]
  change (e₁'.trans e₂' ∘ₗ φ') (e₀ x) = (ψ ∘ₗ e₁.trans e₂) (e₀ x)
  rw [(rTensor_Finprod_equiv_induced R N P n f : e₁'.trans e₂' ∘ₗ φ' = ψ ∘ₗ e₁.trans e₂)]

variable {N P} in
open DirectSum Module.Free in
/-- If `M`, `N` and `P` are `R`-modules, `M` is finite and free, and `f : N → P` is an injective
linear map, the tensor product of `f` and the identity `M → M` is also injective. -/
theorem rTensor_finite_free_injective_of_injective [Module.Free R M] [Module.Finite R M]
    (f : N →ₗ[R] P) (hf : Function.Injective f) : Function.Injective (rTensor M f) := by
  rewrite [← (rTensor M f).id_comp, ← LinearEquiv.refl_toLinearMap,
      ← (rid_finite_free R M P).self_trans_symm, LinearEquiv.coe_trans, LinearMap.comp_assoc,
      rTensor_finite_free_equiv_induced, LinearMap.coe_comp, LinearEquiv.coe_coe,
      EmbeddingLike.comp_injective, LinearMap.coe_comp, LinearEquiv.coe_coe,
      EquivLike.injective_comp]
  exact induced_injective R (Fin (Fintype.card (ChooseBasisIndex R M))) hf

variable {N P} in
theorem lTensor_finite_free_injective_of_injective [Module.Free R M] [Module.Finite R M]
    (f : N →ₗ[R] P) (hf : Function.Injective f) : Function.Injective (lTensor M f) := by
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

variable {R} {M} {N} in
/-- Rewriting lemma auxiliary to `extend'`. -/
private theorem map_comap {L : Submodule R M} {x : M × N →₀ ℤ}
    (hmem : ∀ y, y ∈ x.support → y.fst ∈ L) :
      TensorProductFinsupp.rEmbed N L.injective_subtype
        (TensorProductFinsupp.rEmbed_comap N L.injective_subtype x) = x := by
  unfold TensorProductFinsupp.rEmbed TensorProductFinsupp.rEmbed_comap
  rewrite [Finsupp.embDomain_eq_mapDomain]
  have : Set.SurjOn (Prod.map L.subtype id)
      ((Prod.map L.subtype id) ⁻¹' x.support) (x.support : Set (M × N)) :=
    fun y hy => ⟨(⟨y.fst, hmem y hy⟩, y.snd), by exact hy, rfl⟩
  erw [Finsupp.mapDomain_comapDomain _ (Injective.Prod_map L.injective_subtype injective_id) x
    this.subset_range]

open TensorProductFinsupp (lEmbed rEmbed rEmbed_comap) in
variable {R} {M} {N} {P} in
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

This lemma is auxiliary to `lTensor_free_injective_of_injective.aux`.
-/
theorem lTensor_free_injective_of_injective.aux' [DecidableEq M] [DecidableEq P]
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
  refine ⟨L, ⟨⟨κ, ℱ⟩⟩, ⟨κ.image ℰ, by rw [Finset.coe_image]⟩, w, by rw [map_comap hmem₁], ?_⟩
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
variable {R} {M} {N} {P} in
/-- If `M` and `N` are `R`-modules, `M` has a basis `ℰ`, and `y : M × N →₀ ℤ` (representing an
element of the free abelian group on `M × N`) is in the subgroup `TensorProductFinsupp.Null R M N`,
then there is a finite subfamily `κ` of `ℰ` with span `L` for which `y` is the image of some
`z : L × M → ℤ` under the mapping `L × N` to `M × N` induced by the inclusion of `L` in `M`,
and z is in the subgroup `TensorProductFinsupp.Null R L N`. -/
theorem lTensor_free_injective_of_injective.aux [DecidableEq M] [DecidableEq P]
    [DecidableEq (M × N →₀ ℤ)] [Module.Free R M] {x : M ⊗[R] N} {ψ : N →ₗ[R] P}
    (hψ : Injective ψ) (hx₀ : lTensor M ψ x = 0) :
      ∃ (L : Submodule R M) (_ : Module.Free R L) (_ : L.FG)
        (w : L ⊗[R] N), L.subtype.rTensor N w = x ∧ ψ.lTensor L w = 0 := by
  -- Choose a representative `x' = ∑(mᵢ, nᵢ)` of x in the free abelian group on `M × N`.
  let x' := Quotient.out' <| (TensorProductFinsupp.Equiv R M N).symm x
  have hy' : lEmbed M hψ x' ∈ TensorProductFinsupp.Null R M P := by
    rewrite [← QuotientAddGroup.eq_zero_iff, ← QuotientAddGroup.mk'_apply,
      ← (TensorProductFinsupp.Equiv R M P).symm.map_zero, ← hx₀,
      ← (TensorProductFinsupp.Equiv R M N).apply_symm_apply x]
    unfold_let x'
    rw [mk'_lEmbed, lTensor_equiv',
      (TensorProductFinsupp.Equiv R M P).symm_apply_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.out_eq']
  have ⟨L, hfree, hfg, w', hx', hz'⟩ := lTensor_free_injective_of_injective.aux' hψ hy'
  refine ⟨L, hfree, hfg, TensorProductFinsupp.Equiv R L N <| QuotientAddGroup.mk' _ w', ?_, ?_⟩
  . rw [rTensor_equiv', ← mk'_rEmbed N L.injective_subtype, hx',
      QuotientAddGroup.mk'_apply, QuotientAddGroup.out_eq', LinearEquiv.apply_symm_apply]
  . rewrite [lTensor_equiv', ← mk'_lEmbed L hψ, LinearEquiv.map_eq_zero_iff,
      QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact hz'

theorem lTensor_free_injective_of_injective [DecidableEq M] [DecidableEq P]
    [DecidableEq (M × N →₀ ℤ)] [Module.Free R M]
    (ψ : N →ₗ[R] P) (hψ : Injective ψ) : Injective (lTensor M ψ) := by
  -- Nontriviality
  haveI [Subsingleton R] : Subsingleton (M ⊗[R] N) := by exact Module.subsingleton R _
  refine (subsingleton_or_nontrivial R).elim
    (fun _subsingleton x y _ => Subsingleton.allEq x y) (fun _nontrivial => ?_)
  -- Assuming `lTensor F ψ x = 0`, show `x = 0`.
  letI : AddGroup (M ⊗[R] N) := inferInstance -- Type class reminder
  rewrite [injective_iff_map_eq_zero]
  intro x hy
  obtain ⟨L, hfree, hfg, w, rfl, hz⟩ := lTensor_free_injective_of_injective.aux hψ hy
  haveI : Module.Finite R L := ⟨(fg_top L).mpr hfg⟩
  obtain rfl : w = 0 := lTensor_finite_free_injective_of_injective R L ψ hψ hz
  rw [LinearMap.map_zero]
