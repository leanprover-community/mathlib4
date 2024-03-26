import Mathlib.InformationTheory.HomEquivAPI.BaseHom

variable {T:Type*} {a:Type*} {s:a→ Prop} {b:Type*}

def MyProp (foo:a → b) (s:a→ Prop): Prop := sorry

variable (s b)

structure MyHom extends XHom a b, YHom s b where
  myProp : MyProp toFun s

-- DFunLike where applicable/necessary
instance MyHom.instFunLike : FunLike (MyHom s b) a b where
    coe := fun f => f.toYHom
    coe_injective' := fun f g h => by -- this proof is typically a tad annoying to do
      sorry

variable {s b}

-- weird brackets to later allow for magicks at cancel_right
@[ext]
lemma MyHom.ext ⦃f:MyHom s b⦄ ⦃g:MyHom s b⦄ (h:∀ x, f x = g x): f = g :=
  DFunLike.ext _ _ h

-- take [XHomClass T a b] as a parameter.
-- this is because when lean tries to infer [XHomClass T a b],
-- it will try to look for [MyHomClass T s b] and not know what s to use.
-- [YHomClass T s b] is ok tho
class MyHomClass
    (T:Type*) {a:Type*} (s:Set a) (b:Type*) [FunLike T a b] [XHomClass T a b]
    extends YHomClass T s b where
  myProp' : ∀ (f:T), MyProp f s

-- declare instances for classes when it is a parameter to MyHomClass
instance MyHom.instXHomClass {a:Type*} (s:Set a) (b:Type*) : XHomClass (MyHom s b) a b where
  xProp' := fun f => f.xProp

-- in declaring this, you also declare immediately `YHomClass s b`
instance MyHom.instMyHomClass {a:Type*} (s:Set a) (b:Type*) : MyHomClass (MyHom s b) s b where
  yProp' := fun f => f.yProp
  myProp' := fun f => f.myProp

variable--? [MyHomClass T s b] =>
  [FunLike T a b] [XHomClass T a b]

@[coe]
def MyHomClass.toMyHom [MyHomClass T s b] (f:T) : MyHom s b where
  toFun := f
  xProp := XHomClass.xProp' f
  yProp := YHomClass.yProp' f
  myProp := MyHomClass.myProp' f

instance [MyHomClass T s b] : CoeTC T (MyHom s b) :=
  ⟨MyHomClass.toMyHom⟩

@[simp]
theorem MyHom.coe_coe [MyHomClass T s b] (f : T) : ((f : MyHom s b) : a → b) = f := rfl

@[simp]
theorem MyHom.coe_mk
  (f : XHom a b) (yProp: PY f s) (myProp :MyProp f s): (MyHom.mk f yProp myProp : a → b) = f := rfl


protected def MyHom.copy (f : MyHom s b) (f' : a → b) (h : f' = f) :
    MyHom s b where
  toFun := f'
  xProp := h.symm ▸ f.xProp
  yProp := h.symm ▸ f.yProp
  myProp := h.symm ▸ f.myProp

@[simp]
theorem MyHom.coe_copy (f : MyHom s b) (f' : a → b) (h : f' = f) :
    (f.copy f' h) = f' := rfl

-- alternatively, if you want to focus only on added fields:
protected def MyHom.copy' (f: MyHom s b) (f' : a → b) (h : f' = f): MyHom s b := {
  f.toXHom.copy f' h, f.toYHom.copy f' h with
  myProp := by
    simp only
    rw [XHom.copy]
    exact h.symm ▸ f.myProp
  }

theorem MyHom.coe_copy_eq (f :MyHom s b) (f' : a → b) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simps]
def MyHom.id (s:a→Prop) : MyHom s a := {
  toFun := fun x => x
  xProp := sorry
  yProp := sorry
  myProp := sorry
}

variable {s₂:b → Prop} {c:Type*}
def MyHom.comp (hnp : MyHom s₂ c) (hmn : MyHom s b) : MyHom s c := {
  hnp.toXHom.comp hmn.toXHom, hnp.toYHom.comp hmn.toYHom with
  myProp := by
    simp only
    rw [XHom.comp]
    simp only
    sorry
}

@[simp]
theorem MyHom.coe_comp {s₂:b → Prop} {c:Type*} (g : MyHom s₂ c) (f : MyHom s b) :
    ↑(g.comp f) = g ∘ f := rfl

theorem MyHom.comp_apply {s₂:b → Prop} {c:Type*} (g : MyHom s₂ c) (f : MyHom s b) (x : a) :
    g.comp f x = g (f x) := rfl

theorem MyHom.comp_assoc {s₂:b → Prop} {c:Type*} {s₃: c → Prop} {d : Type*}
    (f : MyHom s b) (g : MyHom s₂ c) (h : MyHom s₃ d) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem MyHom.cancel_right {s₂:b → Prop} {c:Type*} {g₁ g₂ : MyHom s₂ c} {f : MyHom s b}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MyHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩


theorem MyHom.cancel_left {s₂:b → Prop} {c:Type*} {g : MyHom s₂ c} {f₁ f₂ : MyHom s b}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => MyHom.ext fun x => hg <| by rw [← MyHom.comp_apply, h, MyHom.comp_apply],
    fun h => h ▸ rfl⟩

@[simp]
theorem MyHom.comp_id (f : MyHom s b) : f.comp (MyHom.id s) = f :=
  MyHom.ext fun _ => rfl

@[simp]
theorem MyHom.id_comp {s₂:b → Prop} (f : MyHom s b) : (MyHom.id s₂).comp f = f :=
  MyHom.ext fun _ => rfl
