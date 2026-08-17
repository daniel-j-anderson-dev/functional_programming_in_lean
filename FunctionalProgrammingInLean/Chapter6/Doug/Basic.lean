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

def preFile
  (self : Configuration)
  : String :=
  if self.useASCII then "|--" else "├──"

def preDirectory
  (self : Configuration)
  : String :=
  if self.useASCII then "|  " else "│  "

def fileName
  (self : Configuration) (path : String)
  : String :=
  s!"{self.currentPrefix}{self.preFile} {path}"

def directoryName
  (self : Configuration) (path : String)
  : String :=
  s!"{self.currentPrefix}{self.preFile} {path}/"

def inDirectory
  (self : Configuration)
  : Configuration :=
  {self with currentPrefix := s!"{self.preDirectory} {self.currentPrefix}"}

end Configuration

inductive Entry where
  | file (name : String)
  | directory (name : String)

namespace Entry

def fromPath?
  (path : System.FilePath)
  : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.directory ""))
  | some "." | some ".." => pure none
  | some name => pure (some (if (← path.isDir) then .directory name else .file name))

end Entry

def showFileName
  (configuration : Configuration) (path : String)
  : IO Unit :=
  IO.println (configuration.fileName path)

def showDirName
  (configuration : Configuration) (path : String)
  : IO Unit :=
  IO.println (configuration.directoryName path)

-- see `List.forA`
def doList
  [Applicative f]
  (xs : List α) (action : (α → f Unit))
  : f Unit :=
  match xs with
  | [] => pure ()
  | head :: tail =>
    action head *>
    doList tail action
#check (@List.forA)

def dirLT
  (lhs rhs : IO.FS.DirEntry)
  : Bool :=
  lhs.fileName < rhs.fileName

partial def dirTree
  (configuration : Configuration) (path : System.FilePath)
  : IO Unit := do
  match ← Entry.fromPath? path with
  | none => pure ()
  | some (.file name) => showFileName configuration name
  | some (.directory name) =>
    showDirName configuration name
    let contents ← path.readDir
    let contents := contents.qsort dirLT
    let newConfiguration := configuration.inDirectory
    for entry in contents do
      dirTree newConfiguration entry.path
    -- doList (contents.qsort dirLt).toList λ entry => dirTree newConfiguration entry.path

def usage
  : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

abbrev ExitCode := UInt32
abbrev ExitCode.success : ExitCode := 0
abbrev ExitCode.failure : ExitCode := 1

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

#eval doug ["--ascii"]
