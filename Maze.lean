import Lean
import Maze.Basic
import Maze.Tactics

-- Can escape the trivial maze in any direction.
example : can_escape ┌─┐
                     │@│
                     └─┘ := by out


-- some other mazes with immediate escapes
example : can_escape ┌──┐
                     │░░│
                     │@░│
                     │░░│
                     └──┘ := by out
example : can_escape ┌──┐
                     │░░│
                     │░@│
                     │░░│
                     └──┘ := by out
example : can_escape ┌───┐
                     │░@░│
                     │░░░│
                     │░░░│
                     └───┘ := by out
example : can_escape ┌───┐
                     │░░░│
                     │░░░│
                     │░@░│
                     └───┘ := by out


-- Now for some more interesting mazes.

def maze0 := ┌──────┐
             │▓▓▓▓▓▓│
             │▓░░░░▓│
             │▓@░░░▓│
             │▓░░░░▓│
             │▓▓▓▓░▓│
             └──────┘

-- example : can_escape maze0 := by
--   east
--   south
--   out

def maze1 := ┌──────┐
             │▓▓▓▓▓▓│
             │▓░░@░▓│
             │▓░░░░▓│
             │▓░░░░▓│
             │▓▓▓▓░▓│
             └──────┘


def maze1_2 := ┌──────┐
               │▓▓▓▓▓▓│
               │▓░@▓░▓│
               │▓░░░░▓│
               │▓░░░░▓│
               │▓▓▓▓░▓│
               └──────┘

example : can_escape maze1 := by
  repeat south
  east
  south
  out

macro "naive_auto" : tactic =>
  `(tactic| repeat (first | out | east | south ))

example : can_escape maze0 := by naive_auto
example : can_escape maze1 := by naive_auto

example : can_escape maze1_2 := by
  repeat (first | out | east | south)

example : can_escape maze0 := by my_auto

example : can_escape maze1 := by my_auto

example : can_escape maze1_2 := by my_auto



def maze2 :=  ┌──────┐
              │▓▓▓▓▓▓│
              │▓░░░░▓│
              │▓░░░░▓│
              │▓░░@░▓│
              │▓░▓▓▓▓│
              └──────┘
example : can_escape maze2 := sorry

example : can_escape maze2 := by my_auto


def maze3 := ┌────────┐
             │▓▓▓▓▓▓▓▓│
             │▓░▓@▓░▓▓│
             │▓░▓░░░▓▓│
             │▓░░▓░▓▓▓│
             │▓▓░▓░▓░░│
             │▓░░░░▓░▓│
             │▓░▓▓▓▓░▓│
             │▓░░░░░░▓│
             │▓▓▓▓▓▓▓▓│
             └────────┘

example : can_escape maze3 := by my_auto


example : can_escape maze3 :=
 by south
    east
    south
    south
    south
    west
    west
    west
    south
    south
    east
    east
    east
    east
    east
    north
    north
    north
    east
    out

def maze4 := ┌────────────────────────────┐
             │▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│
             │▓░░░░░░░░░░░░░░░░░░░░▓░░░@░▓│
             │▓░▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓░▓░▓▓▓▓▓│
             │▓░▓░░░▓░░░░▓░░░░░░░░░▓░▓░░░▓│
             │▓░▓░▓░▓░▓▓▓▓░▓▓▓▓▓▓▓▓▓░▓░▓░▓│
             │▓░▓░▓░▓░▓░░░░▓░░░░░░░░░░░▓░▓│
             │▓░▓░▓░▓░▓░▓▓▓▓▓▓▓▓▓▓▓▓░▓▓▓░▓│
             │▓░▓░▓░▓░░░▓░░░░░░░░░░▓░░░▓░▓│
             │▓░▓░▓░▓▓▓░▓░▓▓▓▓▓▓▓▓▓▓░▓░▓░▓│
             │▓░▓░▓░░░░░▓░░░░░░░░░░░░▓░▓░▓│
             │▓░▓░▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓░▓│
             │░░▓░░░░░░░░░░░░░░░░░░░░░░░░▓│
             │▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│
             └────────────────────────────┘

example : can_escape maze4 := by my_auto


example : can_escape maze4 := sorry
--  by west
--     west
--     west
--     south
--     sorry -- can you finish the proof?
