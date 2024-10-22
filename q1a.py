from z3 import And, Or, Solver, Int, sat
import string

def load_set_from_file(filename):
    with open(filename, 'r') as f:
        return {word.strip().lower().replace(",", "").replace(".", "") for word in f}
    
def load_str_from_file(filename):
    with open(filename, 'r') as f:
        return f.readline()

def solve_cipher(encrypted_text, wordlist):
    solver = Solver()
    
    mapping = {}
    valid_chars = string.ascii_lowercase + string.digits
    
    # setup sat map char -> char
    for c in valid_chars:
        mapping[c] = Int(f'map_{c}')
        solver.add(mapping[c] >= 0, mapping[c] <= 25)
    
    encrypted_words = set(encrypted_text.split())
    
    # iterate through the dictionary and apply two constraints:
    # 1. word constraint - can be any of the words which match in length (OR)
    # 2. char constraint - the characters of the candidate words must map to one another (AND)
    for encrypted_word in encrypted_words:
        word_constraint = False

        for valid_word in wordlist:
            if len(encrypted_word) != len(valid_word):
                continue

            word_match = True
            
            for e_char, v_char in zip(encrypted_word, valid_word):
                char_match = (mapping[e_char] == ord(v_char) - ord('a'))
                word_match = And(word_match, char_match)
            
            word_constraint = Or(word_constraint, word_match)
        
        # add the whole thing to the solver
        solver.add(word_constraint)
    
    # check for sat
    if solver.check() == sat:
        model = solver.model()
        
        fwd_map = {}
        for c in valid_chars:
            # convert back to a char map
            fwd_map[c] = chr(model[mapping[c]].as_long()+ord('a'))

        return fwd_map
        
    else:
        return None

def main():
    wordlist = load_set_from_file('google-10000-english.txt')
    
    # combined both of the prompts together as they use the same key
    # also loaded as a set to reduce complexity (we are not considering sentence construction, only vocab)
    encrypted_text = load_set_from_file('encrypted.txt')

    mapping = solve_cipher(" ".join(encrypted_text), wordlist)

    # translate using the mapping
    to_translate = load_str_from_file('encrypted.txt')
    res = ""
    for c in to_translate.lower():
        if c not in mapping:
            res = res + c
        else:
            res = res + mapping[c].upper()
    
    # output results in convenient format
    print(res)

    with open('P1a_result.txt', 'w') as f:
        print(mapping, file=f)
        print(res, file=f)


if __name__ == "__main__":
    main()