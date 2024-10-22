
/-
Check out theorems of List and Nat, which might be helpful.
- https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html

Note:
  1) theorems of List and Nat can be directly used without importing any libraries
  2) you shall not import any libraries
  3) you can define as many helper theorems as you want
-/

/-
Hint:

the following tactics are frequently used tactics, which should be sufficient for this assignment,
but feel free to use other tactics in Lean 4.

- intro, apply, rw, simp, induction, case, unfold, have, contradiction, assumption

-/

/-
  Strong Induction Principle
-/
axiom strong_induction_on (p : Nat → Prop) (n : Nat)
    (h : ∀ n, (∀ m, m < n → p m) → p n) : p n

/-
  Definition of Palindrome
-/
def isPalindrome (xs : List Nat) : Prop := xs = xs.reverse

/-
  Definition of duplication of a list k times
-/
def dup (k : Nat) (xs : List Nat) : List Nat :=
  match k with
  | 0 => []
  | k' + 1 => xs ++ (dup k' xs)


#eval dup 5 [1,2]

theorem test1 : isPalindrome [] := by rfl
theorem test2 : isPalindrome [1, 2, 1] := by rfl
theorem test3 : isPalindrome (dup 3 [1]) := by simp [dup]; rfl

theorem assoc_dup (xs : List Nat) : (k : Nat) -> (xs ++ dup k xs) = (dup k xs ++ xs) := by
  intro k
  induction k with
  | zero =>
    simp [dup]
  | succ k' ih =>
    simp [dup]
    apply ih

/-
  TODO: prove that if xs is a Palindrome, then any duplications of xs are Palindromes as well.
-/

-- (2 points)
theorem palindrome_dup_easy1 (xs : List Nat) : isPalindrome xs → isPalindrome (dup 1 xs) := by
  intro h
  unfold dup
  simp [dup]
  apply h

-- (3 points)
theorem palindrome_dup_easy2 (xs : List Nat) : isPalindrome xs → isPalindrome (dup 2 xs) := by
  intro h
  simp [isPalindrome, dup]
  rw [← h]

-- (5 points)
theorem palindrome_dup_easy3 (xs : List Nat) : isPalindrome xs → isPalindrome (dup 3 xs) := by
  intro h
  simp [isPalindrome, dup]
  rw [← h]

-- (10 points)
theorem palindrome_dup (xs : List Nat) : (k : Nat) -> isPalindrome xs → isPalindrome (dup k xs) := by
  intro k
  induction k with
  | zero =>
    intro h
    simp [dup]
    rfl
  | succ k' ih =>
    intro h
    unfold dup
    unfold isPalindrome
    simp
    rw [← ih]
    rw [← h]
    apply assoc_dup
    apply h

/-
  TODO: prove that if some duplication of xs is a Palindrome, then xs itself is also a Palindrome.
-/

-- (2 points)
theorem dup_palindrome_easy1 (xs : List Nat) : isPalindrome (dup 1 xs) -> isPalindrome xs := by
  unfold dup
  unfold isPalindrome
  simp [dup]

-- (3 points)
theorem dup_palindrome_easy2 (xs : List Nat) : isPalindrome (dup 2 xs) -> isPalindrome xs := by
  simp [isPalindrome, dup]




-- (5 points)
theorem dup_palindrome_easy3 (xs : List Nat) : isPalindrome (dup 3 xs) -> isPalindrome xs := by
  simp [isPalindrome]

-- (10 points)
theorem dup_palindrome (xs : List Nat) (k : Nat) : (k > 0) -> isPalindrome (dup k xs) -> isPalindrome xs := sorry
