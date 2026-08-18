module

public section

def usage
  : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

abbrev ExitCode := UInt32
abbrev ExitCode.success : ExitCode := 0
abbrev ExitCode.failure : ExitCode := 1

namespace implementation

structure Config
  : Type where
  useASCII : Bool := false
  currentPrefix : String := ""

namespace Config

def fromArgs?
  (args : List String)
  : Option Config :=
  match args with
  | [] => some {}
  | ["--ascii"] => some {useASCII := true}
  | _ => none

def fileSeparator
  (cfg : Config)
  : String :=
  if cfg.useASCII then "|--" else "├──"

def directorySeparator
  (cfg : Config)
  : String :=
  if cfg.useASCII then "|  " else "│  "

def fileName
  (cfg : Config) (path : String)
  : String :=
  s!"{cfg.currentPrefix}{cfg.fileSeparator} {path}"

def directoryName
  (cfg : Config) (path : String)
  : String :=
  s!"{cfg.currentPrefix}{cfg.fileSeparator} {path}/"

def prependDirectorySeparator
  (cfg : Config)
  : Config :=
  {cfg with currentPrefix := s!"{cfg.directorySeparator} {cfg.currentPrefix}"}

def showFileName
  (Config : Config) (path : String)
  : IO Unit :=
  IO.println (Config.fileName path)

def showDirectoryName
  (Config : Config) (path : String)
  : IO Unit :=
  IO.println (Config.directoryName path)

end Config

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

-- see `List.forA`
def doList
  [Applicative f]
  (xs : List α) (action : α → f Unit)
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
  (cfg : Config) (path : System.FilePath)
  : IO Unit := do
  match ← Entry.fromPath? path with
  | none => pure ()
  | some (.file name) => cfg.showFileName name
  | some (.directory name) =>
    cfg.showDirectoryName name
    let contents ← path.readDir
    let contents := contents.qsort dirLT
    let newcfg := cfg.prependDirectorySeparator
    for entry in contents do
      dirTree newcfg entry.path
    -- doList (contents.qsort dirLt).toList λ entry => dirTree newcfg entry.path

def doug
  (args : List String)
  : IO UInt32 := do
  match Config.fromArgs? args with
  | some Config =>
    let currentDirectory ← IO.currentDir
    dirTree Config currentDirectory
    pure ExitCode.success
  | none =>
    let args := args.foldl (· ++ " " ++ ·) ""
    let errorMessage := s!"Invalid arguments\n{args}\n{usage}\n"
    IO.eprintln errorMessage
    pure ExitCode.failure

#eval doug ["--ascii"]

end implementation

namespace using_a_custom_monad

open implementation (Config Entry)

abbrev IO.pure := @(inferInstance : Pure IO).pure
abbrev IO.bind := @(inferInstance : Bind IO).bind

@[expose]
def ConfigIO
  (α : Type)
  : Type :=
  Config → IO α

namespace ConfigIO

def pure
  : α → ConfigIO α :=
  Function.const _ ∘ IO.pure

def bind
  (current : ConfigIO α) (next : α → ConfigIO β)
  : ConfigIO β :=
  λ cfg => do
    let current' ← current cfg
    let next' ← next current' cfg
    IO.pure next'

instance Monad
  : Monad ConfigIO where
  pure := ConfigIO.pure
  bind := ConfigIO.bind

def locally
  : (ConfigIO α) → (Config → Config) → ConfigIO α :=
  Function.comp

def fromIO
  : IO α → ConfigIO α :=
  Function.const _

def toIO
  (action : ConfigIO α) (cfg : Config)
  : IO α :=
  action cfg

end ConfigIO

def getConfig
  : ConfigIO Config :=
  IO.pure

def IO.toConfigIO : {α : Type} → IO α → ConfigIO α := @ConfigIO.fromIO
open using_a_custom_monad (IO.toConfigIO)

def showFileName'
  (path : String)
  : ConfigIO Unit := do
  ((← getConfig).showFileName path).toConfigIO

def showDirectoryName'
  (path : String)
  : ConfigIO Unit := do
  ((← getConfig).showDirectoryName path).toConfigIO

partial def dirTree
  (path : System.FilePath)
  : ConfigIO Unit := do
  match (← ConfigIO.fromIO (Entry.fromPath? path)) with
  | none => pure ()
  | some (.file name) => showFileName' name
  | some (.directory name) =>
    showDirectoryName' name
    let contents ← ConfigIO.fromIO path.readDir
    (for entry in contents do
      dirTree entry.path
    ).locally .prependDirectorySeparator

def doug
  (args : List String)
  : IO UInt32 := do
  match Config.fromArgs? args with
  | some config =>
    let currentDirectory ← IO.currentDir
    (dirTree currentDirectory).toIO config
    pure ExitCode.success
  | none =>
    let args := args.foldl (· ++ " " ++ ·) ""
    let errorMessage := s!"Invalid arguments\n{args}\n{usage}"
    IO.eprintln errorMessage
    pure ExitCode.failure

#eval doug []
#eval doug ["--ascii"]

end using_a_custom_monad
