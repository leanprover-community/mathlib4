import Lean

open Lean

namespace Embedding

structure IndexedEmbedding where
  index : Nat
  embedding : Array JsonNumber
deriving ToJson, FromJson

structure Error where
  message : String
  type : String
deriving ToJson, FromJson

def Error.isTokenLimit (e : Error) : Bool := e.type == "invalid_request_error"

def parseResponse (response : String) :
    Except String (Except Error (Array IndexedEmbedding)) := do
  match Json.parse response with
  | .error err => .error s!"Error parsing json:\n{err}\n{response}"
  | .ok json =>
    if let .ok out := json.getObjValAs? (Array IndexedEmbedding) "data" then
      .ok <| .ok out
    else if let .ok err := json.getObjValAs? Error "error" then
      .ok <| .error err
    else
      .error s!"Unknown error:\n{json}"

structure Decl where
  name : Name
  module : Option Name
  type : Expr
  rev : String
  nameHash : UInt64 := name.hash
  typeHash : UInt64 := type.hash

structure EmbeddedDecl extends Decl where
  nameEmb : Option (Array JsonNumber) := none
  typeEmb : Option (Array JsonNumber) := none

def EmbeddedDecl.json (e : EmbeddedDecl) (env : Environment) : IO Json := do
  let tp := toJson <| toString <| (← ppExprWithInfos { env := env } e.type).fmt
  return Json.mkObj [
    ("name", toJson e.name),
    ("module", toJson e.module),
    ("type", tp),
    ("rev", e.rev),
    ("nameHash", toJson e.nameHash),
    ("typeHash", toJson e.typeHash),
    ("nameEmb", toJson e.nameEmb),
    ("typeEmb", toJson e.typeEmb)
  ]

end Embedding
