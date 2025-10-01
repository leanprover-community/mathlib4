import Mathlib.Tactic.Reap.Requests.Future
import Lean

open Lean

namespace Requests

variable {α β : Type} [ToJson α] [FromJson β]

/-- Default headers to handle json input and output -/
def defaultHeaders : Json :=
  json% {
    "accept" : "application/json",
    "content-type" : "application/json"
  }

def formatHeaders (headers : Json) : IO (Array String) :=
  match headers with
  | Json.obj kvs =>
    return kvs.foldl (fun acc k v => acc ++ #["-H", s!"{k}: {
      match Json.getStr? v with
      | Except.error _ => ""
      | Except.ok s => s
      }"]) #[]
  | _ => throw $ IO.userError "Headers must be an object"


/-- Format url for get method  -/
def formatGetUrl (url : String) (data : α) : IO String :=
  match toJson data with
  | Json.obj kvs =>
    let paramStr := kvs.foldl (fun acc k v => acc ++ #[s!"{k}={
      match Json.getStr? v with
      | Except.error _ => ""
      | Except.ok s => s
      }"]) #[] |>.joinSep "&"
    return s!"{url}?{paramStr}"
  | _ => throw $ IO.userError "Params must be an object"

/-- Main entry point for get method -/
def get (url : String) (data : α) (headers: Json := defaultHeaders) : IO β := do
  let headers ← formatHeaders headers
  let url ← formatGetUrl url data
  let out ← IO.Process.output {
    cmd := "curl"
    args := #["-X", "GET", url] ++ headers
  }
  if out.exitCode != 0 then
     throw $ IO.userError s!"Request failed. {out.stderr} {out.stdout}"
  let some json := Json.parse out.stdout |>.toOption
    | throw $ IO.userError s!"Json Parse failed. {out.stderr} {out.stdout}"
  let some res := (fromJson? json : Except String β) |>.toOption
    | throw $ IO.userError s!"From Json failed. {out.stderr} {out.stdout}"
  return res

/-- Main entry point for post method -/
def post (url : String) (data : α) (headers: Json := defaultHeaders): IO β := do
  let headers ← formatHeaders headers
  let data := (toJson data).pretty UInt64.size
  let out ← IO.Process.output {
    cmd := "curl"
    args := #["-X", "POST", url] ++ headers ++ #["-d", data]
  }
  if out.exitCode != 0 then
     throw $ IO.userError s!"Request failed. {out.stderr} {out.stdout} {toJson data}"
  let some json := Json.parse out.stdout |>.toOption
    | throw $ IO.userError s!"Json Parse failed. {out.stderr} {out.stdout} {toJson data}"
  let some res := (fromJson? json : Except String β) |>.toOption
    | throw $ IO.userError s!"From Json failed. {out.stderr} {out.stdout} {toJson data}"
  return res

end Requests
