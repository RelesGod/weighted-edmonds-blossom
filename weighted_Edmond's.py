from collections import deque
from math import inf

EPS = 1e-9

UNLABELED = 0
OUTER = 1
INNER = 2


class Edge:

    def __init__(self, u, v, cost):
        self.u = u
        self.v = v
        self.cost = cost


class Graph:

    def __init__(self, n, edges):

        self.n = n

        self.edges = []

        self.adj = [[] for _ in range(n)]

        self.cost = [
            [inf] * n
            for _ in range(n)
        ]

        for u, v, w in edges:
            e = Edge(u, v, w)

            self.edges.append(e)

            self.adj[u].append(e)
            self.adj[v].append(e)

            self.cost[u][v] = w
            self.cost[v][u] = w

        for i in range(n):
            self.cost[i][i] = 0


class Blossom:

    def __init__(self, blossom_id, base, members):
        self.id = blossom_id

        self.base = base

        self.members = set(members)

        self.gamma = 0.0


class WeightedEdmonds:

    def __init__(self, graph):

        self.G = graph

        self.n = graph.n

        self.mate = [-1] * self.n

        self.alpha = [0.0] * self.n

        self.blossoms = {}

        self.next_blossom_id = self.n

        self.in_blossom = list(range(self.n))

        self.last_forest = None

        self.initialize_duals()

        self.theta_history = []
        self.alpha_history = []

    # ====================================================
    # INITIALIZATION
    # ====================================================

    def initialize_duals(self):

        for v in range(self.n):

            best = inf

            for e in self.G.adj[v]:
                best = min(best, e.cost)

            if best == inf:
                self.alpha[v] = 0.0
            else:
                self.alpha[v] = best / 2.0

    def dual_value(self, i, j):

        value = self.alpha[i] + self.alpha[j]

        for B in self.blossoms.values():

            if (
                    i in B.members
                    and
                    j in B.members
            ):
                value += B.gamma

        return value

    def reduced_cost(self, i, j):

        return (
                self.G.cost[i][j]
                - self.dual_value(i, j)
        )

    def admissible(self, i, j):

        return abs(
            self.reduced_cost(i, j)
        ) < EPS

    # ====================================================
    # ADMISSIBLE GRAPH
    # ====================================================

    def build_admissible_graph(self):

        adj = [[] for _ in range(self.n)]

        for e in self.G.edges:

            if self.admissible(e.u, e.v):
                adj[e.u].append(e.v)
                adj[e.v].append(e.u)

        return adj

    # ====================================================
    # BLOSSOMS
    # ====================================================

    def create_blossom(
            self,
            base,
            members):


        bid = self.next_blossom_id

        self.next_blossom_id += 1

        B = Blossom(
            bid,
            base,
            members
        )

        self.blossoms[bid] = B

        for v in members:
            self.in_blossom[v] = bid

        return bid

    def classify_blossoms(self, label):

        outer_blossoms = []

        inner_blossoms = []

        for bid, B in self.blossoms.items():

            if label[B.base] == OUTER:

                outer_blossoms.append(bid)

            elif label[B.base] == INNER:

                inner_blossoms.append(bid)

        return (
            outer_blossoms,
            inner_blossoms
        )

    def expand_blossom(self, bid):

        B = self.blossoms[bid]

        for v in B.members:
            self.in_blossom[v] = v

        del self.blossoms[bid]

    def expand_zero_blossoms(self):

        to_delete = []

        for bid, B in self.blossoms.items():

            if B.gamma >= -EPS:
                to_delete.append(bid)

        for bid in to_delete:
            self.expand_blossom(bid)

    # ====================================================
    # DELTAS
    # ====================================================

    def delta1(self, outer):

        delta = inf

        for u in outer:

            for v in outer:

                if u >= v:
                    continue

                if (
                        self.in_blossom[u]
                        ==
                        self.in_blossom[v]
                ):
                    continue
                if self.G.cost[u][v] == inf:
                    continue

                rc = self.reduced_cost(u, v)

                if rc <= EPS:
                    continue

                delta = min(
                    delta,
                    rc / 2.0
                )

        return delta

    def delta2(self, outer, unlabeled):

        delta = inf

        for u in outer:

            for v in unlabeled:

                if self.G.cost[u][v] == inf:
                    continue

                rc = self.reduced_cost(u, v)

                if rc <= EPS:
                    continue

                delta = min(delta, rc)

        return delta

    def delta3(
            self,
            inner_blossoms):

        delta = inf

        for bid in inner_blossoms:
            B = self.blossoms[bid]

            delta = min(
                delta,
                -B.gamma / 2.0
            )

        return delta

    def compute_theta(
            self,
            outer,
            unlabeled,
            inner_blossoms):

        d1 = self.delta1(outer)
        d2 = self.delta2(outer, unlabeled)
        d3 = self.delta3(inner_blossoms)

        theta = min(d1, d2, d3)

        if theta == inf:
            return None

        return theta

    def dual_step(
            self,
            outer,
            inner,
            unlabeled,
            outer_blossoms,
            inner_blossoms):

        theta = self.compute_theta(
            outer,
            unlabeled,
            inner_blossoms
        )
        if theta is None:
            return None

        for v in outer:
            self.alpha[v] += theta

        for v in inner:
            self.alpha[v] -= theta

        for bid in outer_blossoms:
            self.blossoms[bid].gamma -= (
                    2.0 * theta
            )

        for bid in inner_blossoms:
            self.blossoms[bid].gamma += (
                    2.0 * theta
            )

        return theta

    # ====================================================
    # SEARCH IN ADMISSIBLE GRAPH
    # ====================================================

    def search_admissible_graph(self):

        graph = self.build_admissible_graph()

        n = self.n

        combined_label = [UNLABELED] * n

        parent = [-1] * n

        base = list(range(n))

        q = deque()

        def lca(u, v):

            used = [False] * n

            while True:

                u = base[u]

                used[u] = True

                if self.mate[u] == -1:
                    break

                nxt = parent[self.mate[u]]

                u = nxt

            while True:

                v = base[v]

                if used[v]:
                    return v

                nxt = parent[self.mate[v]]

                v = nxt

        def mark_path(
                v,
                b,
                child,
                blossom):

            while base[v] != b:
                blossom[base[v]] = True
                blossom[base[self.mate[v]]] = True

                parent[v] = child

                child = self.mate[v]

                v = parent[self.mate[v]]

        def find_path(root):

            nonlocal parent

            label = [UNLABELED] * n

            for i in range(n):
                base[i] = i

            q.clear()

            q.append(root)

            label[root] = OUTER

            while q:

                v = q.popleft()

                for to in graph[v]:

                    if base[v] == base[to]:
                        continue

                    if self.mate[v] == to:
                        continue

                    if (
                            to == root
                            or (
                            self.mate[to] != -1
                            and parent[self.mate[to]] != -1
                    )
                    ):

                        curbase = lca(v, to)

                        blossom = [False] * n

                        mark_path(
                            v,
                            curbase,
                            to,
                            blossom
                        )

                        mark_path(
                            to,
                            curbase,
                            v,
                            blossom
                        )

                        members = {curbase}

                        for i in range(n):

                            if blossom[base[i]]:

                                members.add(i)

                                base[i] = curbase

                                if label[i] == UNLABELED:
                                    label[i] = OUTER

                                    q.append(i)



                        if len(members) >= 3:
                            self.create_blossom(
                                curbase,
                                members
                            )
                    elif label[to] == UNLABELED:

                        parent[to] = v

                        label[to] = INNER

                        if self.mate[to] == -1:

                            cur = to

                            while cur != -1:

                                prev = parent[cur]

                                nxt = (
                                    self.mate[prev]
                                    if prev != -1
                                    else -1
                                )

                                self.mate[cur] = prev

                                if prev != -1:
                                    self.mate[prev] = cur

                                cur = nxt

                            return {
                                "augment": True,
                                "label": label,
                                "base": base[:]
                            }

                        else:

                            partner = self.mate[to]

                            label[partner] = OUTER

                            q.append(partner)

            return {
                "augment": False,
                "label": label,
                "base": base[:]
            }

        augment_found = False

        self.last_forest = None

        combined_label = [UNLABELED] * n

        for root in range(n):

            if self.mate[root] == -1:

                parent = [-1] * n

                result = find_path(root)

                if result["augment"]:

                    augment_found = True

                else:

                    for v in range(n):

                        if result["label"][v] == OUTER:
                            combined_label[v] = OUTER

                        elif result["label"][v] == INNER:
                            combined_label[v] = INNER

        self.last_forest = {
            "label": combined_label
        }

        return augment_found

    # ====================================================
    # MAIN LOOP
    # ====================================================

    def solve(self):

        while True:

            improved = self.search_admissible_graph()

            # нашли хотя бы один увеличивающий путь
            if improved:
                continue

            # больше ничего улучшить нельзя
            if self.last_forest is None:
                break

            label = self.last_forest["label"]

            outer = [
                v
                for v in range(self.n)
                if label[v] == OUTER
            ]

            inner = [
                v
                for v in range(self.n)
                if label[v] == INNER
            ]

            unlabeled = [
                v
                for v in range(self.n)
                if label[v] == UNLABELED
            ]

            (
                outer_blossoms,
                inner_blossoms
            ) = self.classify_blossoms(label)

            theta = self.dual_step(
                outer,
                inner,
                unlabeled,
                outer_blossoms,
                inner_blossoms
            )

            if theta is not None:
                self.theta_history.append(theta)

                self.alpha_history.append(
                    self.alpha.copy()
                )



            if theta is None:
                break

            if theta == inf:
                break

            if theta <= EPS:
                break

            self.expand_zero_blossoms()

        return self.mate

    def matching_edges(self):

        result = []

        used = set()

        for v in range(self.n):

            u = self.mate[v]

            if u == -1:
                continue

            if v in used:
                continue

            result.append(
                (v + 1, u + 1)
            )

            used.add(v)
            used.add(u)

        return result

    def matching_weight(self):

        total = 0

        used = set()

        for v in range(self.n):

            u = self.mate[v]

            if u == -1:
                continue

            if v in used:
                continue

            total += self.G.cost[v][u]

            used.add(v)
            used.add(u)

        return total
