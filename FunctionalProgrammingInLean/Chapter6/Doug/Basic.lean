module

public section

structure Configuration
  : Type where
  useASCII : Bool := false
  currentPrefix : String := ""

namespace Configuration

def fromArgs?
  (args : List String)
  : Option Configuration :=
  match args with
  | [] => some {}
  | ["--ascii"] => some {useASCII := true}
  | _ => none

end Configuration

def usage
  : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

abbrev ExitCode := UInt32
abbrev ExitCode.success : ExitCode := 0
abbrev ExitCode.failure : ExitCode := 1

axiom dirTree (cfg : Configuration) (path : System.FilePath) : IO Unit
def doug
  (args : List String)
  : IO UInt32 := do
  match Configuration.fromArgs? args with
  | some configuration =>
    let currentDirectory ← IO.currentDir
    dirTree configuration currentDirectory
    pure ExitCode.success
  | none =>
    let args := args.foldl (· ++ " " ++ ·) ""
    let errorMessage := s!"Invalid arguments\n{args}\n{usage}"
    IO.eprintln errorMessage
    pure ExitCode.failure
