
import Lean

namespace Solver

open Lean Elab Tactic Meta

variable [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]

/-
  You may change the input arguments of `callSolver` if you find it helpful,
  but please keep the return type `m (List Nat)` as it is.
-/

def callSolver (mazeInfo : List Nat) (x : Nat) (y : Nat) (x_max : Nat) (y_max : Nat) : m (List Nat) := do
  /-
  mazeInfo : wall coordinates given one by one
  x : starting row
  y : starting col
  x_max : num rows
  y_max : num cols
  -/


  -- launch a process to run the solver
  let proc ← IO.Process.spawn {
    -- solver is run in python3
    cmd := "python3"
    args := #["./external_solver/solver-demo.py"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }

  -- send player info
  proc.stdin.putStr s!"{x} {y}\n"
  proc.stdin.putStr s!"{x_max} {y_max}\n"

  -- send maze info to standard I/O
  for c in mazeInfo do
    proc.stdin.putStr s!"{c}\n"

  proc.stdin.flush
  let (_, proc) ← proc.takeStdin
  let _ ← proc.wait

  -- read the output from the solver
  let output ← proc.stdout.readToEnd
  let answer := output.trim.splitOn.map String.toNat!
  return answer
