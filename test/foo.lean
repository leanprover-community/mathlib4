import Mathlib.Tactic

/- Demo code copied from **RPC method** in `#widget` -/

open Lean Widget Server RequestM

structure GetTypeParams where
  name : Name
  pos : Lsp.Position
  deriving FromJson, ToJson

@[server_rpc_method]
def getType (params : GetTypeParams) : RequestM (RequestTask CodeWithInfos) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    runTermElabM snap do
      let name ← resolveGlobalConstNoOverloadCore params.name
      let some c ← Meta.getConst? name
        | throwThe RequestError ⟨.invalidParams, s!"no constant named '{name}'"⟩
      Widget.ppExprTagged c.type

/- I only removed the `input` part and keep the rest of the code and functionalities unchanged -/

@[widget]
def checkWidget : UserWidgetDefinition where
  name := "#check as a service"
  javascript := "
import * as React from 'react';
const e = React.createElement;
import { RpcContext, InteractiveCode, useAsync, mapRpcError } from '@leanprover/infoview';

export default function(props) {
  const rs = React.useContext(RpcContext)

  const st = useAsync(() =>
    rs.call('getType', { name: props.name, pos: props.pos }), [props.name, rs, props.pos])

  const type = st.state === 'resolved' ? st.value && e(InteractiveCode, {fmt: st.value})
    : st.state === 'rejected' ? e('p', null, mapRpcError(st.error).message)
    : e('p', null, 'Loading..')

  return e('div', null, type)
}
"

def is_zero (a : ℕ) : Prop := a * 1 = 0

theorem addition_comm (a b : ℕ) : a + b = b + a := sorry

/-
#check as a service
ℕ → Prop
-/
#widget checkWidget (Json.mkObj [("name", "is_zero")])

/-
#check as a service
Rpc error: InvalidParams: no constant named 'addition_comm'
-/
#widget checkWidget (Json.mkObj [("name", "addition_comm")])
