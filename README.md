# CSC 2108 A1

### Description of Files
```bash
├── CSC_2108_Assignment_Fall_2024.pdf
├── Maze
│   ├── Basic.lean
│   ├── Solver.lean
│   └── Tactics.lean
├── Maze.lean
├── P1a_result.txt
├── P1b_result.txt
├── Palindrome.lean
├── encrypted.txt
├── encrypted_test.txt
├── external_solver
│   ├── solver-demo
│   └── solver-demo.py
├── google-10000-english.txt
├── lake-manifest.json
├── lakefile.lean
├── lean-toolchain
├── mapping.txt
├── my.log
├── q1a.py
├── q1b.py
├── requirements.txt
└── translated.txt
```

**venv**

Implementation uses Python 3.12.7.

Virtual environment requirements are in `requirements.txt`.

The only actual package required is z3-solver (no need to setup a venv if this is already installed globally)

**Q1A Translation**

Files: q1a.py, P1a_result.txt

Data files: google-10000-english.txt, encrypted.txt

Auxiliary files: mapping.txt, translated.txt

Execute command:

`python3 q1a.py`

**Q1B Palindrome**

Files: q1b.py, P1b_result.txt

Execute command:

`python3 q1b.py`

**Q2 Palindrome**

Files: Palindrome.lean

**Q3 Maze**

Files: Maze.lean, external_solver/solver-demo.py, Maze/*