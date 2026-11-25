import Lake
open Lake DSL

/-
Directory names such as `BM1/1` and `BM1.1` become the module names
`BM1.«1».…` and `«BM1.1».…`.  `lakefile.toml` cannot express `«BM1.1»` in a
glob, so this file is written in Lean.
-/

package «dead-bms» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib DeadBms where
  globs := #[.one `DeadBms, .submodules `Common, .submodules `Test,
    .submodules `BM1, .submodules `«BM1.1», .submodules `BM2, .submodules `BM3,
    .submodules `rTSS, .submodules `«BM2.1», .submodules `Bubby3fix]

/-- exploration scripts (`#eval`), not part of the proof -/
lean_lib Explore where
  globs := #[.submodules `Explore]
