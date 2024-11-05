/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.LinearAlgebra.Quotient
import Mathlib.LinearAlgebra.Prod

/-!
# Goursat's lemma on submodules of a product

We prove three related results describing submodules of a direct product `A × B` of modules (over
an arbitrary ring `R`):

* `exists_equiv_of_submodule_prod`: a submodule of `A × B` which maps isomorphically to either
  factor is the graph of an isomorphism `A ≃ B`.
* `exists_equiv_fstMod_sndMod_of_surjective` (the most familiar form of Goursat's lemma): a
  submodule of `A × B` which maps isomorphically to either factor is the graph of an isomorphism
  between quotients of `A` and `B`.
* `exists_equiv_fstMod_sndMod` : any submodule of `A × B` is the graph of an isomorphism between
  subquotients of `A` and `B`.
-/

open Function LinearMap Submodule

section Semiring

variable {R A B : Type*} [Semiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]

/--
**Goursat's Lemma**, weak version: given `R`-modules `A, B`, and a submodule `V ⊆ A × B` whose
projection to each factor is bijective, we can find a linear equiv `f : A ≃ B` whose graph is `V`.
-/
theorem exists_equiv_of_submodule_prod {V : Submodule R (A × B)}
    (hV₁ : Bijective (Prod.fst ∘ V.subtype)) (hV₂ : Bijective (Prod.snd ∘ V.subtype)) :
    ∃ f : A ≃ₗ[R] B, V = f.graph := by
  simp only [← coe_fst (R := R), ← coe_snd (R := R), ← coe_comp] at hV₁ hV₂
  use (LinearEquiv.ofBijective _ hV₁).symm.trans (.ofBijective _ hV₂)
  ext ⟨a, b⟩
  simp only [mem_graph_iff, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [← LinearEquiv.symm_apply_eq]
  refine ⟨fun hab ↦ ?_, fun hab ↦ ?_⟩
  · transitivity ⟨(a, b), hab⟩ <;>
    [skip; rw [Eq.comm]] <;>
    simp only [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, LinearMap.comp_apply,
      coe_subtype, fst_apply, snd_apply]
  · convert ((LinearEquiv.ofBijective _ hV₁).symm a).property using 2
    · exact ((LinearEquiv.ofBijective _ hV₁).apply_symm_apply a).symm
    · simpa only [← hab] using ((LinearEquiv.ofBijective _ hV₂).apply_symm_apply b).symm

end Semiring

section Ring

variable {R A B : Type*} [Ring R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

/--
**Goursat's Lemma**: given `R`-modules `A, B`, and a submodule `V ⊆ A × B` which surjects onto
both factors, there are submodules `A' ⊆ A` and `B' ⊆ B`, and an equivalence `A / A' ≃ B / B'`,
such that `V` is precisely the preimage in `A × B` of `f.graph ⊆ (A / A') × (B / B')`.
-/
theorem exists_equiv_fstMod_sndMod_of_surjective {V : Submodule R (A × B)}
    (hV₁ : Surjective (Prod.fst ∘ V.subtype)) (hV₂ : Surjective (Prod.snd ∘ V.subtype)) :
    ∃ (A' : Submodule R A) (B' : Submodule R B) (f : (A ⧸ A') ≃ₗ[R] (B ⧸ B')),
    V = f.graph.comap ((mkQ A').prodMap (mkQ B')) := by
  -- define A' and B'
  let A' := V.comap (LinearMap.inl ..)
  have hA {a} : a ∈ A' → (a, 0) ∈ V := by simp only [mem_comap, coe_inl, imp_self, A']
  let B' := V.comap (LinearMap.inr ..)
  have hB {b} : b ∈ B' → (0, b) ∈ V := by simp only [mem_comap, coe_inr, imp_self, B']
  use A', B'
  let Q : A × B →ₗ[R] (A ⧸ A') × (B ⧸ B') := (mkQ _).prodMap (mkQ _)
  -- show V is the preimage of a submodule of `(A ⧸ A') × (B ⧸ B')`
  have hkQ : ker Q ≤ V := by
    simp only [Q, ker_prodMap, ker_mkQ]
    intro p hp
    simp only [mem_prod, mem_comap, A', B', coe_inl, coe_inr] at hp
    simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using add_mem hp.1 hp.2
  rw [← comap_map_eq_self hkQ]
  -- by prev result, suffices to show that this maps bijectively to `A ⧸ A'` and `B ⧸ B'`
  refine Exists.imp (fun f ↦ congrArg _) (exists_equiv_of_submodule_prod ⟨?_, ?_⟩ ⟨?_, ?_⟩)
  -- is it possible to avoid the duplication here?
  · rw [← LinearMap.coe_fst (R := R), ← coe_comp, injective_iff_map_eq_zero]
    rintro ⟨⟨⟨a⟩, ⟨b⟩⟩, hab⟩ hab'
    simp only [Quotient.quot_mk_eq_mk, coe_comp, coe_subtype, Function.comp_apply, fst_apply,
      Quotient.mk_eq_zero, mk_eq_zero, Prod.mk_eq_zero] at hab hab' ⊢
    simp only [hab', true_and]
    rw [← mkQ_apply, ← mkQ_apply, ← prodMap_apply A'.mkQ B'.mkQ (a, b),
      ← mem_comap, comap_map_eq_self hkQ] at hab
    simpa only [hB, Prod.mk_sub_mk, sub_self, sub_zero] using sub_mem hab (hA hab')
  · rintro ⟨a⟩
    simp only [coe_subtype, Function.comp_apply, Subtype.exists, exists_prop', nonempty_prop]
    refine match hV₁ a with | ⟨⟨p, hp⟩, hp'⟩ => ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    simpa only [coe_comp, Function.comp_apply, fst_apply, ← hp', coe_subtype,
      Quotient.quot_mk_eq_mk] using mkQ_apply _ p.1
  · rw [← LinearMap.coe_snd (R := R), ← coe_comp, injective_iff_map_eq_zero]
    rintro ⟨⟨⟨a⟩, ⟨b⟩⟩, hab⟩ hab'
    simp only [Quotient.quot_mk_eq_mk, coe_comp, coe_subtype, Function.comp_apply, snd_apply,
      Quotient.mk_eq_zero, mk_eq_zero, Prod.mk_eq_zero] at hab hab' ⊢
    simp only [hab', and_true]
    rw [← mkQ_apply, ← mkQ_apply, ← prodMap_apply A'.mkQ B'.mkQ (a, b),
      ← mem_comap, comap_map_eq_self hkQ] at hab
    simpa only [hA, Prod.mk_sub_mk, sub_self, sub_zero] using sub_mem hab (hB hab')
  · rintro ⟨b⟩
    simp only [coe_subtype, Function.comp_apply, Subtype.exists, exists_prop', nonempty_prop]
    refine match hV₂ b with | ⟨⟨p, hp⟩, hp'⟩ => ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    simpa only [coe_comp, Function.comp_apply, snd_apply, ← hp', coe_subtype,
      Quotient.quot_mk_eq_mk] using mkQ_apply _ p.2

/--
**Goursat's Lemma**, most general form: given `R`-modules `A, B`, and a submodule `V ⊆ A × B`,
there are submodules `A'' ⊆ A' ⊆ A` and `B'' ⊆ B' ⊆ B`, and an equivalence
`f : A' / A'' ≃ B' / B''`, such that `V` is precisely the image in `A × B` of the preimage in
`A' × B'` of `graph f ⊆ (A' / A'') × (B' / B'')`.
-/
theorem exists_equiv_fstMod_sndMod (V : Submodule R (A × B)) :
    ∃ (A' A'' : Submodule R A) (B' B'' : Submodule R B) (ha : A'' ≤ A') (hb : B'' ≤ B')
    (f : (A' ⧸ (A''.comap A'.subtype)) ≃ₗ[R] B' ⧸ (B''.comap B'.subtype)),
    V = (f.graph.comap ((mkQ _).prodMap (mkQ _))).map (A'.subtype.prodMap B'.subtype) := by
  -- set up notation to reduce to case when subspace surjects onto factors
  let A' := V.map (LinearMap.fst _ _ _)
  let B' := V.map (LinearMap.snd _ _ _)
  let P : V →ₗ[R] A' := (LinearMap.fst _ _ _).submoduleMap V
  let Q : V →ₗ[R] B' := (LinearMap.snd _ _ _).submoduleMap V
  let V' : Submodule R (A' × B') := LinearMap.range (P.prod Q)
  have hV'₁ : Surjective (Prod.fst ∘ V'.subtype) := by
    simp only [← coe_fst (R := R), ← coe_comp, ← range_eq_top, range_comp, range_subtype, V']
    simp only [← LinearMap.range_comp, fst_prod, range_eq_top]
    apply submoduleMap_surjective
  have hV'₂ : Surjective (Prod.snd ∘ V'.subtype) := by
    simp only [← coe_snd (R := R), ← coe_comp, ← range_eq_top, range_comp, range_subtype, V']
    simp only [← LinearMap.range_comp, snd_prod, range_eq_top]
    apply submoduleMap_surjective
  -- apply result above to `V' ⊆ A' × B'`
  obtain ⟨A'', B'', f, hf⟩ := exists_equiv_fstMod_sndMod_of_surjective hV'₁ hV'₂
  use A', A''.map A'.subtype, B', B''.map B'.subtype, map_subtype_le _ _, map_subtype_le _ _
  rw [comap_map_eq_of_injective (injective_subtype _),
    comap_map_eq_of_injective (injective_subtype _)]
  use f
  rw [← hf]
  -- now show `V = map (A'.subtype.prodMap B'.subtype) V'`, which should surely not be this hard?
  ext ⟨a, b⟩
  refine ⟨fun hab ↦ ?_, fun hab ↦ ?_⟩
  · use (⟨a, ⟨_, hab, rfl⟩⟩, ⟨b, ⟨_, hab, rfl⟩⟩)
    simp only [submoduleMap, SetLike.mem_coe, LinearMap.mem_range, prod_apply, Pi.prod,
      Prod.mk.injEq, Subtype.ext_iff, restrict_coe_apply, fst_apply, snd_apply, Subtype.exists,
      exists_and_left, exists_prop', nonempty_prop, Prod.exists, exists_eq_right, exists_eq_left,
      hab, prodMap_apply, coe_subtype, and_true, V', P, Q]
  · simp only [mem_map, prodMap_apply, Prod.mk.injEq] at hab
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab, rfl, rfl⟩ := hab
    simpa only [submoduleMap, LinearMap.mem_range, prod_apply, Pi.prod, Prod.mk.injEq,
      Subtype.ext_iff, restrict_coe_apply, fst_apply, snd_apply, Subtype.exists, exists_and_left,
      exists_prop', nonempty_prop, Prod.exists, exists_eq_right, exists_eq_left, V', P, Q] using hab

end Ring
