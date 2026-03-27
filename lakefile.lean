import Lake
open Lake DSL

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

def RemoteGameServer : Dependency := {
  name := `GameServer
  scope := "leanprover-community"
  src? := DependencySrc.git "https://github.com/leanprover-community/lean4game.git" leanVersion "server"
  version? := s!"git#{leanVersion}"
  opts := ∅
}

open Lean in
#eval (do
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env ``RemoteGameServer)
  : Elab.Command.CommandElabM Unit)

package Game where
  leanOptions := #[
    ⟨`linter.all, false⟩,
    ⟨`pp.showLetValues, true⟩,
    ⟨`tactic.hygienic, false⟩
  ]
  moreLeanArgs := #[
    "-Dtactic.hygienic=false",
    "-Dlinter.unusedVariables.funArgs=false",
    "-Dtrace.debug=false"
  ]
  moreServerOptions := #[
    ⟨`tactic.hygienic, false⟩,
    ⟨`linter.unusedVariables.funArgs, true⟩,
    ⟨`trace.debug, true⟩
  ]

@[default_target]
lean_lib Game

require "leanprover-community" / mathlib @ git leanVersion

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git"
