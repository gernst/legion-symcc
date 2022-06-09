import z3
import random
from legion.helper import *
from math import inf, sqrt, log

INPUTS = set()
KNOWN = set()
RHO = 1

class Arm:
    def __init__(self, node):
        self.node = node

        self.reward = 0
        self.selected = 0

    def score(self, N):
        return uct(self.reward, self.selected, N)

    def descr(self, N):
        return "uct(%d, %d, %d)" % (self.reward, self.selected, N)


class Node:
    def __init__(self, target, path, pos, neg, parent=None):
        self.site = None

        self.target = target
        self.nbytes = len(target)

        self.path = path
        self.pos = pos
        self.neg = neg

        self.parent = parent
        self.yes = None
        self.no = None

        self.sampler = None

        self.is_phantom = True

        # statistics collected for sampling in this node and subtree, respectively
        self.here = Arm(self)
        self.tree = Arm(self)


    def propagate(self, reward, selected, here=True):
        if here:  # to this node
            self.here.reward += reward
            self.here.selected += selected

        self.tree.reward += reward
        self.tree.selected += selected

        if self.parent:
            self.parent.propagate(reward, selected, here=False)

    def insert(self, trace, is_complete):
        base = None
        node = self

        for index in range(len(trace)):
            # print(index)
            was_phantom = node.is_phantom

            site, target, polarity, phi = trace[index]

            if was_phantom:
                # yes = phi
                # no = z3.Not(phi) # SLOOOOW (hash consing)
                node.is_phantom = False
                node.site = site
                # node.yes = Node(target, node.path + "1", node.constraints + [yes], parent=node)
                # node.no = Node(target, node.path + "0", node.constraints + [no], parent=node)
                node.yes = Node(
                    target, node.path + "1", node.pos + [phi], node.neg, parent=node
                )
                node.no = Node(
                    target, node.path + "0", node.pos, node.neg + [phi], parent=node
                )

                if not base:
                    base = node

            node = node.yes if polarity else node.no

        return base, node

    def sample(self):
        if not self.target:
            return b""  # no bytes to sample

        if self.sampler is None:
            solver = z3.Optimize()
            solver.add(self.pos)
            solver.add([z3.Not(phi) for phi in self.neg])
            # print("target     ", self.target, " with size", self.nbytes)
            # print("constraints", self.constraints)
            self.sampler = naive(solver, self.target)

        try:
            sample = next(self.sampler)
            return sample

        except StopIteration:
            return None

    def select(self, bfs):
        if self.is_phantom:
            return self
        else:
            if bfs:
                options = [self.yes.tree, self.no.tree]
            else:
                options = [self.here, self.yes.tree, self.no.tree]

            N = self.tree.selected

            # print([arm.descr(N) for arm in options])
            # print([arm.score(N) for arm in options])

            candidates = []
            best = -inf

            for arm in options:
                cur = arm.score(N)

                if cur == best:
                    candidates.append(arm)
                    continue
                if cur > best:
                    best = cur
                    candidates = [arm]

            arm = random.choice(candidates)
            node = arm.node

            if node is self:
                return node
            else:
                return node.select(bfs)
    def pp_legend(self):
        print("              local              subtree")
        print("    score  win  try      score  win  try    path")
        self.pp()

    def pp(self):
        if not self.parent:
            key = "*"
        elif self.is_phantom:
            key = "?"
        else:
            key = "."

        N = self.tree.selected

        if True or key != ".":
            a = "{:7.2f} {:4d} {:4d}".format(
                self.here.score(N), self.here.reward, self.here.selected
            )
            b = "{:7.2f} {:4d} {:4d}".format(
                self.tree.score(N), self.tree.reward, self.tree.selected
            )
            print(key, a, "  ", b, "  ", self.path)

        if key != "E":
            if self.no:
                self.no.pp()
            if self.yes:
                self.yes.pp()
                

# higher is better
def uct(w, n, N):
    if not n:
        return inf
    else:
        exploit = w / n
        explore = RHO * sqrt(2 * log(N) / n)
        return exploit + explore

def naive(solver, target):
    assert target
    assert type(target) == list

    if len(target) == 1:
        target = target[0]
    else:
        target = z3.Concat(list(reversed(target)))

    n = target.size()

    delta = z3.BitVec("delta", n)
    result = z3.BitVec("result", n)
    solver.add(result == target)

    solver.minimize(delta)

    while True:
        # print('---------------------------')
        guess = z3.BitVecVal(random.getrandbits(n), n)

        solver.push()
        solver.add(result ^ delta == guess)

        # for known in KNOWN:
        #     if result.size() == known.size():
        #         solver.add(result != known)

        if solver.check() != z3.sat:
            break

        model = solver.model()
        value = model[result]

        sample = int_to_bytes(value.as_long(), n // 8)

        solver.pop()

        KNOWN.add(value)
        INPUTS.add(sample)
        yield sample