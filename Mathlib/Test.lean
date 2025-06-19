import Lean

run_cmd
  let file := "OhNo.txt"
  IO.FS.writeFile file s!"I am a new file"
  let cat ← IO.Process.run {cmd := "cat", args := #[file]}
  IO.println cat
