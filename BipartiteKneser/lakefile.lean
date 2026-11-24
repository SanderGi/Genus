import Lake
open Lake DSL

package «bipartite-kneser» where
  version := v!"0.1.0"
  builtinLint := true
  leanOptions := #[⟨`warningAsError, true⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

/-- Regenerate data when the certificate, constructor, or encoder changes. -/
target witnesses pkg : System.FilePath := do
  let dir := pkg.dir
  let files := #[dir / "lean" / "witness_data.py", dir / "verify_exceptional.py",
    dir / "kneser_constructor.py", dir / "exceptional_certificates.json"]
  let inputs ← files.mapM fun path => do inputTextFile path
  let dest := pkg.buildDir / "generated" / "KneserWitnessData.lean"
  buildFileAfterDep dest (Job.mixArray inputs) (text := true) fun _ => do
    let data ← IO.Process.output {cmd := "python3", args := #[(dir / "lean" / "witness_data.py").toString]}
    unless data.exitCode == 0 do error data.stderr
    IO.FS.createDirAll (pkg.buildDir / "generated")
    IO.FS.writeFile dest data.stdout

lean_lib KneserWitnessData where
  srcDir := ".lake/build/generated"
  needs := #[witnesses]

@[default_target]
lean_lib BipartiteKneser where
  leanOptions := #[⟨`weak.linter.mathlibStandardSet, true⟩]
  srcDir := "lean"

@[test_driver]
lean_lib CheckProof where
  srcDir := "lean"

lean_lib KneserConstruction where
  srcDir := "lean"
  leanOptions := #[⟨`linter.mathlibStandardSet, true⟩]
