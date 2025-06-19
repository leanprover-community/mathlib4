import Lean

run_cmd
  let w ← IO.Process.run {cmd := "whoami"}
  if w.trim != "damiano" then
    IO.FS.writeFile "OhNo.txt" s!"I am a new file by {w}"
