import random
import z3

# Author: Gidon Ernst, gidon.ernst (*) gmail.com
# BSD 3 clause license
# with some modifications
# https://github.com/gernst/bvsampler

# Approach taken from:
#   Rafael Dutra, Kevin Laeufer, Jonathan Bachrach and Koushik Sen:
#   Efficient Sampling of SAT Solutions for Testing, ICSE 2018.
#   https://github.com/RafaelTupynamba/quicksampler/

# https://stackoverflow.com/questions/39299015/sum-of-all-the-bits-in-a-bit-vector-of-z3
def bvcount(b):
    n = b.size()
    bits = [ z3.Extract(i, i, b) for i in range(n) ]
    bvs  = [ z3.Concat(z3.BitVecVal(0, n - 1), b) for b in bits ]
    nb   = reduce(lambda a, b: a + b, bvs)
    return nb

MAX_LEVEL = 6

def bvsampler(solver, target):
    n = target.size()

    delta  = z3.BitVec('delta',  n)
    result = z3.BitVec('result', n)
    solver.add(result == target)

    # this distance metric is sloooow
    # solver.minimize(bvcount(delta))

    solver.minimize(delta)

    results = set()

    while True:
        # print('---------------------------')
        guess = z3.BitVecVal(random.getrandbits(n), n)

        solver.push()
        solver.add(result ^ delta == guess)

        for known in results:
            solver.add(result != known)

        if solver.check() != z3.sat:
            break

        model   = solver.model()
        result0 = model[result].as_long()
        solver.pop()

        results.add(result0)
        yield result0

        # print('solver: ' + str(solver))
        # print('guess: ' + str(guess))
        # print('model: ' + str(model))

        mutations = {}
        
        solver.push()

        for i in range(n):
            # print('mutating bit ' + str(i))
            solver.push()
            goal = z3.BitVecVal(result0, n)
            solver.add(result ^ delta == goal)
            solver.add(z3.Extract(i, i, delta) == 0x1)

            if solver.check() == z3.sat:
                model   = solver.model()
                result1 = model[result].as_long()

                if result1 not in results:
                    results.add(result1)
                    yield result1

                new_mutations = {}
                new_mutations[result1] = 1

                for value in mutations:
                    level = mutations[value]
                    if level > MAX_LEVEL:
                        continue

                    candidate = (result0 ^ ((result0^value) | (result0^result1)))
                    # print('yielding candidate ' + str(candidate) + ' at level ' + str(level))
                    if candidate not in results:
                        results.add(candidate)
                        yield candidate

                    new_mutations[candidate] = level + 1

                mutations.update(new_mutations)

            solver.pop()

        solver.pop()
