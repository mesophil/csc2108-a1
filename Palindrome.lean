
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
    simp [dup]
    simp [isPalindrome]
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
  unfold dup
  unfold isPalindrome
  rw [assoc_dup]
  simp
  rw [← assoc_dup]

  intro h

  let a1 := xs ++ dup 1 xs
  let a2 := xs.reverse ++ (dup 1 xs).reverse

  have h0 : a1 = a2 := by
    apply h

  let l1 := List.take xs.length (xs ++ dup 1 xs)
  let l2 := List.take xs.reverse.length (xs.reverse ++ (dup 1 xs).reverse)

  have h1 : l1 = xs := by
    apply List.take_left

  have h2 : l2 = xs.reverse := by
    apply List.take_left

  have h3 : l1 = l2 := by
    have : List.take xs.length a1 = List.take xs.length a2 := congrArg (List.take xs.length) h0
    simp [a1, a2, h1, h2] at this
    rw [← h2] at this
    rw [← h1] at this
    exact this

  rw [h1] at h3
  rw [h2] at h3
  exact h3


-- (5 points)
theorem dup_palindrome_easy3 (xs : List Nat) : isPalindrome (dup 3 xs) -> isPalindrome xs := by
  unfold dup
  unfold isPalindrome
  rw [assoc_dup]
  simp
  rw [← assoc_dup]

  intro h

  let a1 := xs ++ dup 2 xs
  let a2 := xs.reverse ++ (dup 2 xs).reverse

  have h0 : a1 = a2 := by
    apply h

  let l1 := List.take xs.length (xs ++ dup 1 xs)
  let l2 := List.take xs.reverse.length (xs.reverse ++ (dup 1 xs).reverse)

  have h1 : l1 = xs := by
    apply List.take_left

  have h2 : l2 = xs.reverse := by
    apply List.take_left

  have h3 : l1 = l2 := by
    have : List.take xs.length a1 = List.take xs.length a2 := congrArg (List.take xs.length) h0
    simp [a1, a2, h1, h2] at this
    rw [← h2] at this
    rw [← h1] at this
    exact this

  rw [h1] at h3
  rw [h2] at h3
  exact h3


-- (10 points)
theorem dup_palindrome (xs : List Nat) (k : Nat) : (k > 0) -> isPalindrome (dup k xs) -> isPalindrome xs := by
  induction k with
  | zero =>
    simp
  | succ n =>
    unfold dup
    rw [assoc_dup]
    unfold isPalindrome
    simp
    rw [← assoc_dup]

    intro h

    let a1 := xs ++ dup n xs
    let a2 := xs.reverse ++ (dup n xs).reverse

    have h0 : a1 = a2 := by
      apply h

    let l1 := List.take xs.length (xs ++ dup n xs)
    let l2 := List.take xs.reverse.length (xs.reverse ++ (dup n xs).reverse)

    have h1 : l1 = xs := by
      apply List.take_left

    have h2 : l2 = xs.reverse := by
      apply List.take_left

    have h3 : l1 = l2 := by
      have : List.take xs.length a1 = List.take xs.length a2 := congrArg (List.take xs.length) h0
      simp [a1, a2, h1, h2] at this
      rw [← h2] at this
      rw [← h1] at this
      exact this

    rw [h1] at h3
    rw [h2] at h3
    exact h3
