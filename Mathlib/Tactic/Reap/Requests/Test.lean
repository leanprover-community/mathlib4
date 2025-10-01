import Mathlib.Tactic.Reap.Requests.Basic

open Lean Requests

#eval (get "https://httpbin.org/get" (json% {"haha": "haha"}) : IO Json)

#eval (post "https://httpbin.org/post" (json% {"haha": "haha"}) : IO Json)
