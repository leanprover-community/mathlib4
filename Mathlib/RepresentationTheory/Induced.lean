/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Induced representations

Given a commutative ring `k`, a group homomorphism `φ : G →* H`, and a `k`-linear
`G`-representation `A`, this file introduces the induced representation $Ind_G^H(A)$ of `A` as
an `H`-representation.

By `ind φ A` we mean the `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
We define a representation of `H` on this submodule by sending `h : H` and `⟦h₁ ⊗ₜ a⟧` to
`⟦h₁h⁻¹ ⊗ₜ a⟧`.

We also prove that the restriction functor `Rep k H ⥤ Rep k G` along `φ` is right adjoint to the
induction functor and hence that the induction functor preserves colimits.

Additionally, we show that the functor `Rep k H ⥤ ModuleCat k` sending `B : Rep k H` to
`(Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B` to `(A ⊗ Res(φ)(B))_G`. This
is used to prove Shapiro's lemma in
`Mathlib/RepresentationTheory/Homological/GroupHomology/Shapiro.lean`.

## Main definitions

* `Representation.ind φ ρ` : given a group homomorphism `φ : G →* H`, this is the induction of a
  `G`-representation `(A, ρ)` along `φ`, defined as `(k[H] ⊗[k] A)_G` and with `H`-action given by
  `h • ⟦h₁ ⊗ₜ a⟧ := ⟦h₁h⁻¹ ⊗ₜ a⟧` for `h, h₁ : H`, `a : A`.
* `Rep.indResAdjunction k φ`: given a group homomorphism `φ : G →* H`, this is the adjunction
  between the induction functor along `φ` and the restriction functor `Rep k H ⥤ Rep k G`
  along `φ`.
* `Rep.coinvariantsTensorIndNatIso φ A` : given a group homomorphism `φ : G →* H` and
  `A : Rep k G`, this is a natural isomorphism between the functor sending `B : Rep k H` to
  `(Ind(φ)(A) ⊗ B))_H` and the one sending `B` to `(A ⊗ Res(φ)(B))_G`. Used to prove Shapiro's
  lemma.

-/

@[expose] public section

open Representation

universe w u v v'

namespace Representation

variable {k G H : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H) {A B : Type*}
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] (ρ : Representation k G A)

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`k`-module `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
See `Representation.ind` for the induced `H`-representation on `IndV φ ρ`. -/
@[implicit_reducible]
def IndV := Coinvariants (tprod ((leftRegular k H).comp φ) ρ)

noncomputable instance : AddCommGroup (IndV φ ρ) := by unfold IndV; infer_instance

noncomputable instance : Module k (IndV φ ρ) := by unfold IndV; infer_instance

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`H → A →ₗ[k] (k[H] ⊗[k] A)_G` sending `h, a` to `⟦h ⊗ₜ a⟧`. -/
noncomputable def IndV.mk (h : H) : A →ₗ[k] IndV φ ρ :=
  Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (.single h 1)

variable {φ ρ} in
@[elab_as_elim]
lemma IndV.inductionOn {p : IndV φ ρ → Prop} (v : IndV φ ρ) (mk : ∀ h a, p (IndV.mk φ ρ h a))
    (add : ∀ x y : IndV φ ρ, p x → p y → p (x + y)) : p v := by
  refine Coinvariants.induction_on v fun w => ?_
  refine w.inductionOn (fun m a => ?_) fun _ _ hx hy => by simpa using add _ _ hx hy
  refine m.induction_linear (by simpa using mk 1 0) (fun _ _ hx hy => ?_) (fun h r => ?_)
  · simpa [TensorProduct.add_tmul] using add _ _ hx hy
  · rw [← mul_one r, ← MonoidAlgebra.smul_single', TensorProduct.smul_tmul]
    exact mk h (r • a)

@[ext]
lemma IndV.hom_ext {f g : IndV φ ρ →ₗ[k] B}
    (hfg : ∀ h, f ∘ₗ IndV.mk φ ρ h = g ∘ₗ IndV.mk φ ρ h) : f = g :=
  LinearMap.ext fun v => v.inductionOn (fun h a => congrArg (fun f => f a) (hfg h))
    fun _ _ hx hy => by simp [hx, hy]

@[simp]
lemma IndV.mk_map_mul (g : G) (h : H) (a : A) :
    IndV.mk φ ρ ((φ g) * h) a = IndV.mk φ ρ h (ρ g⁻¹ a) := by
  simp [mk, Coinvariants.mk_tmul_inv (g := g)]

@[simp]
lemma IndV.mk_map_inv_mul (g : G) (h : H) (a : A) :
    IndV.mk φ ρ ((φ g)⁻¹ * h) a = IndV.mk φ ρ h (ρ g a) := by
  simp [← map_inv]

@[simp]
lemma IndV.mk_map_eq (g : G) (a : A) : IndV.mk φ ρ (φ g) a = IndV.mk φ ρ 1 (ρ g⁻¹ a) := by
  simpa using IndV.mk_map_mul φ ρ g 1 a

@[simp]
lemma IndV.mk_map_inv_eq (g : G) (a : A) : IndV.mk φ ρ (φ g)⁻¹ a = IndV.mk φ ρ 1 (ρ g a) := by
  simp [← map_inv]

/-- Construct a linear map `IndV φ ρ →ₗ[k] B` from a compatible family of linear maps
`f : H → A →ₗ[k] B`, whose composition with `IndV.mk φ ρ h : A →ₗ[k] IndV φ ρ` is `f h`. -/
noncomputable def IndV.lift (f : H → A →ₗ[k] B)
    (hf : ∀ (g : G) (h : H) (a : A), f (φ g * h) a = f h (ρ g⁻¹ a)) :
    IndV φ ρ →ₗ[k] B :=
  Coinvariants.lift _ (TensorProduct.lift <| (Finsupp.lift _ _ _ f) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun _ => TensorProduct.ext <|
      MonoidAlgebra.lhom_ext' fun _ => LinearMap.ext_ring <| LinearMap.ext (by simp [hf])

@[simp]
lemma IndV.lift_apply_mk (f : H → A →ₗ[k] B) (h : H) (a : A)
    (hf : ∀ (g : G) (h : H) (a : A), f (φ g * h) a = f h (ρ g⁻¹ a)) :
    lift φ ρ f hf (mk φ ρ h a) = f h a := by
  rw [lift, mk, LinearMap.comp_apply, Coinvariants.lift_mk]
  simp

/-- The induced `H`-action on `IndV φ ρ`, given by `h • ⟦t ⊗ a⟧ = ⟦th⁻¹ ⊗ a⟧`. -/
@[simps -isSimp]
noncomputable def ind : Representation k H (IndV φ ρ) where
  toFun h := IndV.lift φ ρ (fun x => IndV.mk φ ρ (x * h⁻¹)) (by simp [mul_assoc])
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

@[simp]
lemma ind_apply_mk (h₁ h₂ : H) (a : A) :
    ind φ ρ h₁ (IndV.mk _ _ h₂ a) = IndV.mk _ _ (h₂ * h₁⁻¹) a := by
  simp [ind]

@[deprecated (since := "2026-09-19")] alias ind_mk := ind_apply_mk

variable {ρ : Representation k G A} {σ : Representation k H B} {τ : Representation k G B}

/-- Construct an `IntertwiningMap` starting from an induced representation by lifting an
`IntertwiningMap` with a `res` representation as target. -/
noncomputable def ind.lift (f : IntertwiningMap ρ (σ.comp φ)) : (ind φ ρ).IntertwiningMap σ :=
  ⟨IndV.lift φ ρ (fun h => σ h⁻¹ ∘ₗ f.toLinearMap) (by simp [f.isIntertwining]),
    fun g => by ext; simp⟩

@[simp]
lemma ind.lift_apply_mk (f : ρ.IntertwiningMap (σ.comp φ)) (h : H) (a : A) :
    ind.lift φ f (IndV.mk φ ρ h a) = σ h⁻¹ (f a) := by
  simp [ind.lift]

/-- Restrict an equivariant map out of an induced representation to the generators at `1`. -/
noncomputable def ind.evalOne (f : (ind φ ρ).IntertwiningMap σ) : ρ.IntertwiningMap (σ.comp φ) :=
  ⟨f.toLinearMap ∘ₗ IndV.mk φ ρ 1 , fun _ => by ext; simp [← f.isIntertwining]⟩

@[simp]
lemma ind.evalOne_apply (f : (ind φ ρ).IntertwiningMap σ) (a : A) :
    ind.evalOne φ f a = f (IndV.mk φ ρ 1 a) := rfl

/-- The canonical equivariant map from a representation to the restriction of its induction. -/
noncomputable abbrev ind.unit (ρ : Representation k G A) :
    ρ.IntertwiningMap ((ind φ ρ).comp φ) := ind.evalOne φ (IntertwiningMap.id (ind φ ρ))

/-- Evaluate the induction of a restricted representation using its original group action. -/
noncomputable abbrev ind.counit (σ : Representation k H B) :
    (ind φ (σ.comp φ)).IntertwiningMap σ := ind.lift φ (IntertwiningMap.id (σ.comp φ))

/-- An equivariant map from an induced representation is determined by the generators at `1`. -/
@[ext]
lemma ind.hom_ext {f g : (ind φ ρ).IntertwiningMap σ}
    (hfg : f.toLinearMap ∘ₗ IndV.mk φ ρ 1 = g.toLinearMap ∘ₗ IndV.mk φ ρ 1) : f = g := by
  ext h a
  simpa [← IntertwiningMap.isIntertwining] using congrArg (fun f => σ h⁻¹ (f a)) hfg

/-- The universal property of induced representations. -/
@[simps]
noncomputable def indResHomEquiv :
    (ind φ ρ).IntertwiningMap σ ≃ₗ[k] ρ.IntertwiningMap (σ.comp φ) where
  toFun := ind.evalOne φ
  invFun := ind.lift φ
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Given a monoid homomorphism `φ : G →* H` and an intertwining map `f : σ ⟶ ρ`, there is a
  natural intertwining map `ind φ σ ⟶ ind φ ρ` given by composition by `f`. -/
noncomputable def indMap (f : IntertwiningMap ρ τ) : (ind φ ρ).IntertwiningMap (ind φ τ) :=
  ind.lift φ ((ind.unit φ τ).comp f)

@[simp]
lemma indMap_apply_mk (f : ρ.IntertwiningMap τ) (h : H) (a : A) :
    indMap φ f (IndV.mk φ ρ h a) = IndV.mk φ τ h (f a) := by simp [indMap]

variable (ρ : Representation k G A) (σ : Representation k H B)

/-- Move an induced generator across a tensor of coinvariants. -/
noncomputable def coinvariantsTensorIndHom :
    Coinvariants ((ind φ ρ).tprod σ) →ₗ[k] Coinvariants (ρ.tprod (σ.comp φ)) :=
  Coinvariants.lift ((ind φ ρ).tprod σ) (TensorProduct.lift <| IndV.lift φ ρ (fun h =>
      ((TensorProduct.mk k A B).compl₂ (σ h)).compr₂ (Coinvariants.mk (ρ.tprod (σ.comp φ))))
      fun g h a => by ext; simp)
    fun _ => by ext; simp

@[simp]
lemma coinvariantsTensorIndHom_apply_mk (h : H) (x : A) (y : B) :
    coinvariantsTensorIndHom φ ρ σ (Coinvariants.mk ((ind φ ρ).tprod σ)
      (IndV.mk φ ρ h x ⊗ₜ[k] y)) = Coinvariants.mk (ρ.tprod (σ.comp φ)) (x ⊗ₜ[k] σ h y) := by
  simp [coinvariantsTensorIndHom]

/-- Tensor the induction unit and pass to coinvariants. -/
noncomputable def coinvariantsTensorIndInv :
    Coinvariants (ρ.tprod (σ.comp φ)) →ₗ[k] Coinvariants ((ind φ ρ).tprod σ) :=
  let i := (ind.unit φ ρ).rTensor (σ.comp φ)
  Coinvariants.lift (ρ.tprod (σ.comp φ)) (Coinvariants.mk ((ind φ ρ).tprod σ) ∘ₗ i.toLinearMap)
    fun h => LinearMap.ext fun x => (congrArg (Coinvariants.mk _) (i.isIntertwining _ _ h x)).trans
      (Coinvariants.mk_self_apply _ (φ h) _)

@[simp]
lemma coinvariantsTensorIndInv_apply_mk (x : A) (y : B) :
    coinvariantsTensorIndInv φ ρ σ (Coinvariants.mk (ρ.tprod (σ.comp φ)) (x ⊗ₜ[k] y)) =
      Coinvariants.mk ((ind φ ρ).tprod σ) (IndV.mk φ ρ 1 x ⊗ₜ[k] y) := rfl

@[simp]
lemma coinvariantsTensorIndHom_inv (x : Coinvariants (ρ.tprod (σ.comp φ))) :
    coinvariantsTensorIndHom φ ρ σ (coinvariantsTensorIndInv φ ρ σ x) = x :=
  LinearMap.congr_fun (show coinvariantsTensorIndHom φ ρ σ ∘ₗ _ = LinearMap.id by ext; simp) x

@[simp]
lemma coinvariantsTensorIndInv_hom (x : Coinvariants ((ind φ ρ).tprod σ)) :
    coinvariantsTensorIndInv φ ρ σ (coinvariantsTensorIndHom φ ρ σ x) = x :=
  LinearMap.congr_fun (show (ρ.coinvariantsTensorIndInv φ σ ∘ₗ _ = LinearMap.id) by
    ext; simp [← Coinvariants.mk_inv_tmul]) x

/-- Move induction across tensor coinvariants by restriction, sending `⟦h ⊗ a⟧ ⊗ b` to
`⟦a ⊗ σ(h)b⟧`. The inverse sends `⟦a ⊗ b⟧` to `⟦1 ⊗ a⟧ ⊗ b`. -/
noncomputable abbrev coinvariantsTensorIndEquiv :
    Coinvariants ((ind φ ρ).tprod σ) ≃ₗ[k] Coinvariants (ρ.tprod (σ.comp φ)) :=
  LinearEquiv.ofLinearMap (coinvariantsTensorIndHom φ ρ σ) (coinvariantsTensorIndInv φ ρ σ)
    (LinearMap.ext (coinvariantsTensorIndHom_inv φ ρ σ))
    (LinearMap.ext (coinvariantsTensorIndInv_hom φ ρ σ))

end Representation

namespace Rep

open CategoryTheory

variable {k : Type u} {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H] (φ : G →* H)
  (A : Rep.{w} k G)

/-- `Representation.ind` as a bundled representation. -/
noncomputable abbrev ind : Rep k H := Rep.of (A.ρ.ind φ)

/-- `Representation.indMap` as a morphism in `Rep`. -/
noncomputable abbrev indMap {A B : Rep k G} (f : A ⟶ B) :
    ind φ A ⟶ ind φ B := Rep.ofHom <| A.ρ.indMap φ f.hom

variable (k) in
/-- The induction functor along `φ`, with map action given by `Representation.indMap`. -/
@[implicit_reducible, simps obj map]
noncomputable def indFunctor : Rep.{w} k G ⥤ Rep k H where
  obj A := ind φ A
  map f := indMap φ f
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- The linear equivalence `(ind φ A ⟶ B) ≃ₗ[k] (A ⟶ res φ B)`,
obtained by bundling `Representation.indResHomEquiv`. -/
noncomputable def indResHomEquiv (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H) :
    (ind φ A ⟶ B) ≃ₗ[k] (A ⟶ res φ B) :=
  (homLinearEquiv _ B).trans <| (A.ρ.indResHomEquiv φ).trans (homLinearEquiv A (res φ B)).symm

@[simp]
lemma indResHomEquiv_apply_hom (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H)
    (f : ind φ A ⟶ B) :
    (indResHomEquiv.{w} φ A B f).hom = Representation.ind.evalOne φ f.hom := rfl

@[simp]
lemma indResHomEquiv_symm_apply_hom (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H)
    (f : A ⟶ res φ B) :
    ((indResHomEquiv.{w} φ A B).symm f).hom = ind.lift φ f.hom := rfl

/-- Given a group homomorphism `φ : G →* H`, the induction functor `Rep k G ⥤ Rep k H` is left
adjoint to the restriction functor along `φ`. -/
noncomputable def indResAdjunction : indFunctor k φ ⊣ resFunctor.{max w v' u} φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv A B := (indResHomEquiv.{w} φ A B).toEquiv
      homEquiv_naturality_left_symm _ _ := by simp only [indFunctor_obj]; ext; simp
      homEquiv_naturality_right _ _ := rfl }

@[simp]
lemma indResAdjunction_unit_app_hom (A : Rep.{max w v' u} k G) :
    ((indResAdjunction.{w} φ).unit.app A).hom = ind.unit φ A.ρ := rfl

@[simp]
lemma indResAdjunction_counit_app_hom (B : Rep.{max w v' u} k H) :
    ((indResAdjunction.{w} φ).counit.app B).hom = ind.counit φ B.ρ := rfl

@[simp]
lemma indResAdjunction_homEquiv :
    (indResAdjunction φ (k := k)).homEquiv = fun A B => (indResHomEquiv φ A B).toEquiv :=
  Adjunction.mkOfHomEquiv_homEquiv _

instance : (indFunctor.{max u v' w} k φ).IsLeftAdjoint :=
  (indResAdjunction.{w} φ).isLeftAdjoint

instance : (resFunctor.{max u v' w} (k := k) φ).IsRightAdjoint :=
  (indResAdjunction.{w} φ).isRightAdjoint

variable {G H : Type u} [Group G] [Group H] (φ : G →* H) (A : Rep.{u} k G) (B : Rep.{u} k H)

/-- `Representation.coinvariantsTensorIndEquiv` as an isomorphism in `ModuleCat`. -/
noncomputable abbrev coinvariantsTensorIndIso :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ≅
      ((coinvariantsTensor k G).obj A).obj (res φ B) :=
  (A.ρ.coinvariantsTensorIndEquiv φ  B.ρ).toModuleIso

/-- Given a group hom `φ : G →* H` and `A : Rep k G`, the functor `Rep k H ⥤ ModuleCat k` sending
`B ↦ (Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B ↦ (A ⊗ Res(φ)(B))_G`. -/
@[simps (rhsMd := .default) hom_app inv_app]
noncomputable def coinvariantsTensorIndNatIso :
    (coinvariantsTensor k H).obj (ind φ A) ≅ resFunctor φ ⋙ (coinvariantsTensor k G).obj A :=
  (NatIso.ofComponents (fun B => (coinvariantsTensorIndIso φ A B).symm) fun {X Y} f => by
    dsimp only [Functor.comp_obj]; ext; rfl).symm

end Rep
