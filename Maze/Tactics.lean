
import Lean
import Maze.Basic
import Maze.Solver

open Lean Elab Tactic Meta

/-
  Please complete the following search / decision procedure
  if you plan to use Method-1 (i.e., implement the automation tactic in Lean 4)
-/
-- def search_proof (game: GameState) : List Nat := sorry


def extractCoords (walls : List Coords) : List Nat :=
  -- simple function to put the walls into a list
  walls.bind (fun coord => [coord.x, coord.y])

def action (x: Nat) : TacticM Unit := do
  match x with
  | 0 => evalTactic $ ← `(tactic| north)
  | 1 => evalTactic $ ← `(tactic| east)
  | 2 => evalTactic $ ← `(tactic| south)
  | 3 => evalTactic $ ← `(tactic| west)
  | 4 => evalTactic $ ← `(tactic| out)
  | _ => return ()

open Solver

def myAuto  : TacticM Unit := do
  match (← getGoals) with
  | [g] =>
    let e : Expr ← instantiateMVars (← g.getType)
    match e with
    | .app fn args =>
      -- logInfo m!"args: {args}"
      let game ←  (extractGameState args)
      /-
        Method-1: implement a `search_proof` decision procedure in Lean 4
      -/

      --let proof := search_proof game

      /-
        Method-2: call an external solver to find the proof.
        If you are going to pursue this approach,
        please revise the solver path in `Solver.lean`.
      -/

      -- call an external solver, passing in the game information
      let coords := extractCoords game.walls
      let proof ← (callSolver coords game.position.y game.position.x game.size.y game.size.x)

      -- let proof := [2, 4]

      logInfo m! "proof is {proof}"

      let _ ← proof.mapM action
      return ()
    | _ => return ()
  | _ => throwError "myAuto only works when there is a single goal"

syntax "my_auto" : tactic
elab_rules : tactic
  | `(tactic| my_auto) => withMainContext $ myAuto
