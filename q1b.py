from z3 import *
import time

def solve_palindrome_sum(n, bit_length):
    s = Solver()

    # represent bits as Bool
    a = [Bool(f'a_{i}') for i in range(bit_length)]
    b = [Bool(f'b_{i}') for i in range(bit_length)]

    # enforce the palindrome condition
    for i in range(bit_length // 2):
        s.add(a[i] == a[bit_length - 1 - i])
        s.add(b[i] == b[bit_length - 1 - i])
    
    def full_adder(x, y, cin):
        sum_bit = Xor(Xor(x, y), cin)
        cout = Or(And(x, y), And(x, cin), And(y, cin))
        return sum_bit, cout

    # starting from the least significant bit, add the bits of a and b with the carry
    # I have chosen to define a[0] as the LSB and a[-1] as the MSB (reversed order)
    # as it makes for easier indexing, and it doesn't matter for the end result as it should be symmetric
    carry = False
    result = []
    
    for i in range(bit_length):
        sum_bit, carry = full_adder(a[i], b[i], carry)
        result.append(sum_bit)

    s.add(carry)

    # add the conditions for each bit depending on the binary representation of n
    for i in range(bit_length):
        if (n & (1 << i)):
            s.add(result[i])
        else:
            s.add(Not(result[i]))

    # sat solve
    if s.check() == sat:
        m = s.model()
        # generate the candidate numbers and return them (noting the conversion from base 2)
        a_val = int(''.join(['1' if m.evaluate(a[i]) else '0' for i in range(bit_length)]), 2)
        b_val = int(''.join(['1' if m.evaluate(b[i]) else '0' for i in range(bit_length)]), 2)
        return a_val, b_val
    else:
        # unsat -> return None
        return None

def test(n):
    # assume bit_length is n.bit_length() - 1 as a and b have the same bitlength
    # if this was n.bit_length, then MSB on both would be 1
    # in which case there is a carry leftover which is a contradiction
    # therefore, constituents must be length n.bit_length() - 1

    result = solve_palindrome_sum(n, bit_length=n.bit_length()-1)

    if result:
        a, b = result
        with open('P1b_result.txt', 'a') as f:
            print(f"{n} = {a} + {b}", file=f)
            print(f"In binary: {n:b} = {a:b} + {b:b}", file=f)
    else:
        print(f"No solution found for {n}")

if __name__ == "__main__":
    n = [44, 426, 130686, 7887885102, 301743514744735708883980044592643868768690451940670457873179837584805502928507260100275167414297278919454863664936917127855779929905145859759141468926324014180668109424490555196408928664480223861034652769306700079557938008034793476140590605145656692273313364807613593082036221225110204142908645394181908936406]

    # helper loop to test all the cases from the assignment
    for num in n:
        print("--------")
        start = time.time()
        print(f"n: {num}")
        test(num)
        print(f"time elapsed: {time.time()-start}s")
    