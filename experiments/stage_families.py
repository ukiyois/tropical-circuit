"""Candidate admissible families read from G_t (Question 2 of phase 2b).

Every family here is computed from the relation G = G_t only (plus M), through
`relation(v, t)`, so it is determined by G_t by construction; N(t) = M^{u_t} with
u_t a weak order on PO_t (non-PO elements on top).

  posl     PO-SL (Definition def:posl), for reference.
  clsl     circuit-certified single linkage: x ~ z for x, z in PO_t in one
           component of M, (x,z),(z,x) in G, and x, z in one component of
           M | {g : (x,g) in G and (z,g) in G}  (that is v_g <= min(v_x,v_z) + t).
           Classes: transitive closure; ordered by height in the digraph of
           certain comparisons (class X below class Y if some x in X, y in Y
           with (y,x) not in G, i.e. v_y - v_x > t); classes on a directed cycle
           of that digraph are merged.
  clheight arcs f -> e (u(f) <= u(e) required) for e, f in PO_t, one component,
           (e,f) in G and e, f in one component of M | {g : (e,g) in G}; plus
           certain-order arcs f -> e when (f,e) not in G; u = height of the
           strongly connected components.
"""
import stage_core as sc


def relation(v, t):
    m = len(v)
    return {(e, f) for e in range(m) for f in range(m) if v[f] - v[e] <= t}


def po_from_G(M, G):
    out = []
    for f in range(M.m):
        if M.rank(1 << f) == 0:
            continue
        low = sc.mask_of(g for g in range(M.m) if (g, f) not in G)
        if not M.in_cl(low, f):
            out.append(f)
    return out


def components_of_restriction(M, X):
    """Connected components of M | X as a dict element -> root (X a mask)."""
    parent = {e: e for e in sc.bits(X)}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    B = 0
    for e in sc.bits(X):
        if M.rank(B | (1 << e)) > sc.popcount(B):
            B |= 1 << e
    rB = sc.popcount(B)
    for e in sc.bits(X & ~B):
        if M.rank(1 << e) == 0:
            continue
        for f in sc.bits(B):
            if M.rank((B & ~(1 << f)) | (1 << e)) == rB:
                parent[find(e)] = find(f)
    return {e: find(e) for e in sc.bits(X)}


def scc_heights(nodes, arcs):
    """Strongly connected components and the height (longest path from a source)
    of each node's component in the condensation.  arcs: dict node -> iterable."""
    index, low, onstack, stack, comp = {}, {}, set(), [], {}
    counter = [0]
    ncomp = [0]

    def strong(x):
        index[x] = low[x] = counter[0]
        counter[0] += 1
        stack.append(x)
        onstack.add(x)
        for y in arcs.get(x, ()):
            if y not in index:
                strong(y)
                low[x] = min(low[x], low[y])
            elif y in onstack:
                low[x] = min(low[x], index[y])
        if low[x] == index[x]:
            while True:
                y = stack.pop()
                onstack.discard(y)
                comp[y] = ncomp[0]
                if y == x:
                    break
            ncomp[0] += 1
    for x in nodes:
        if x not in index:
            strong(x)
    carcs = {}
    for x in nodes:
        for y in arcs.get(x, ()):
            if comp[x] != comp[y]:
                carcs.setdefault(comp[x], set()).add(comp[y])
    height = {}
    # Tarjan numbers components in reverse topological order: arcs go from higher to lower ids
    for c in range(ncomp[0] - 1, -1, -1):
        height.setdefault(c, 0)
        for d in carcs.get(c, ()):
            height[d] = max(height.get(d, 0), height[c] + 1)
    return {x: height[comp[x]] for x in nodes}


def u_clsl(M, G):
    po = po_from_G(M, G)
    big = M.m + 1
    u = [big] * M.m
    parent = {e: e for e in po}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for i, x in enumerate(po):
        for z in po[i + 1:]:
            if M.comp[x] != M.comp[z] or (x, z) not in G or (z, x) not in G:
                continue
            L = sc.mask_of(g for g in range(M.m) if (x, g) in G and (z, g) in G)
            cr = components_of_restriction(M, L)
            if cr[x] == cr[z]:
                parent[find(x)] = find(z)
    cls = {e: find(e) for e in po}
    arcs = {}
    for x in po:
        for y in po:
            if M.comp[x] == M.comp[y] and (y, x) not in G:      # v_x - v_y > t : y certainly below x
                arcs.setdefault(cls[y], set()).add(cls[x])
    nodes = sorted(set(cls.values()))
    h = scc_heights(nodes, arcs)
    for e in po:
        u[e] = h[cls[e]]
    return u


def u_clheight(M, G):
    po = po_from_G(M, G)
    big = M.m + 1
    u = [big] * M.m
    arcs = {}
    comp_cache = {}
    for e in po:
        L = sc.mask_of(g for g in range(M.m) if (e, g) in G)
        if L not in comp_cache:
            comp_cache[L] = components_of_restriction(M, L)
        cr = comp_cache[L]
        for f in po:
            if f == e or M.comp[e] != M.comp[f]:
                continue
            if (f, e) not in G:                     # v_e - v_f > t : certain order
                arcs.setdefault(f, set()).add(e)
            elif (e, f) in G and f in cr and cr[f] == cr[e]:
                arcs.setdefault(f, set()).add(e)
    h = scc_heights(po, arcs)
    for e in po:
        u[e] = h[e]
    return u


def posl_from_G(M, G):
    """PO-SL computed from G only (as in Lemma lem:observer)."""
    po = po_from_G(M, G)
    big = M.m + 1
    u = [big] * M.m
    parent = {e: e for e in po}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for x in po:
        for z in po:
            if x < z and M.comp[x] == M.comp[z] and (x, z) in G and (z, x) in G:
                parent[find(x)] = find(z)
    cl = {e: find(e) for e in po}
    for e in po:
        below = {cl[f] for f in po if M.comp[f] == M.comp[e] and cl[f] != cl[e] and (f, e) not in G}
        u[e] = len(below)
    return u


FAMILIES = {"posl": posl_from_G, "clsl": u_clsl, "clheight": u_clheight}


def family(name):
    fn = FAMILIES[name]

    def N(M, v, t):
        return sc.MinBase(M, fn(M, relation(v, t)))
    return N


# ---------------------------------------------------------------- brute-force forced linkage
_BASES = {}


def _bases(M):
    if not hasattr(M, "_all_bases"):
        M._all_bases = sc.all_bases(M)
    return M._all_bases


def theta_G(M, G, B):
    """theta(B) <= t  iff  every exchange pair (e, f) of B lies in G (Proposition prop:pos)."""
    for e in range(M.m):
        if B >> e & 1 or M.rank(1 << e) == 0:
            continue
        for f in sc.bits(M.fund_circuit(B, e) & ~(1 << e)):
            if (e, f) not in G:
                return False
    return True


def u_xlink(M, G):
    """Links: (e, f) for every exchange pair of a base of P(G) (f in C(B, e)) unless G
    certifies v_f < v_e (strict trace order), plus G-twins in PO_t of one component.  Classes ordered by certain comparisons (height of the
    condensation).  Brute force over the bases of M: small m only."""
    po = po_from_G(M, G)
    poset = set(po)
    big = M.m + 1
    u = [big] * M.m
    parent = {e: e for e in po}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    nbr = {x: (frozenset(g for g in range(M.m) if (x, g) not in G),
               frozenset(g for g in range(M.m) if (g, x) not in G)) for x in range(M.m)}

    def below(a, b):
        """G certifies v_a < v_b (strict trace order of the semiorder G)."""
        Ua, Da = nbr[a]
        Ub, Db = nbr[b]
        return Ua >= Ub and Da <= Db and not (Ub >= Ua and Db <= Da)
    for B in _bases(M):
        if not theta_G(M, G, B):
            continue
        for e in range(M.m):
            if B >> e & 1 or e not in poset:
                continue
            for f in sc.bits(M.fund_circuit(B, e) & ~(1 << e)):
                if f in poset and not below(f, e):
                    parent[find(e)] = find(f)
    for i, x in enumerate(po):
        for z in po[i + 1:]:
            if M.comp[x] == M.comp[z] and nbr[x] == nbr[z]:
                parent[find(x)] = find(z)
    cls = {e: find(e) for e in po}
    arcs = {}
    for x in po:
        for y in po:
            if M.comp[x] == M.comp[y] and (y, x) not in G:
                arcs.setdefault(cls[y], set()).add(cls[x])
    nodes = sorted(set(cls.values()))
    h = scc_heights(nodes, arcs)
    for e in po:
        u[e] = h[cls[e]]
    return u


FAMILIES["xlink"] = u_xlink


def u_xh(M, G):
    """Exchange height: arcs f -> e (u(f) <= u(e) required) for every exchange pair
    (e, f) of a base of P(G) with e in PO_t (so P(G) is inside M^u by construction),
    plus arcs y -> x whenever G certifies v_y < v_x (strict trace order), in one
    component; u = height of the strongly connected components.  No twin merging:
    u need not be order-preserving in every realization of G.  Brute force."""
    po = po_from_G(M, G)
    poset = set(po)
    big = M.m + 1
    u = [big] * M.m
    nbr = {x: (frozenset(g for g in range(M.m) if (x, g) not in G),
               frozenset(g for g in range(M.m) if (g, x) not in G)) for x in range(M.m)}

    def below(a, b):
        Ua, Da = nbr[a]
        Ub, Db = nbr[b]
        return Ua >= Ub and Da <= Db and not (Ub >= Ua and Db <= Da)
    arcs = {}
    for B in _bases(M):
        if not theta_G(M, G, B):
            continue
        for e in range(M.m):
            if B >> e & 1 or e not in poset:
                continue
            for f in sc.bits(M.fund_circuit(B, e) & ~(1 << e)):
                if f in poset:
                    arcs.setdefault(f, set()).add(e)
    for x in po:
        for y in po:
            if x != y and M.comp[x] == M.comp[y] and below(y, x):
                arcs.setdefault(y, set()).add(x)
    h = scc_heights(po, arcs)
    for e in po:
        u[e] = h[e]
    return u


def u_xlink2(M, G):
    """xlink with class order given by the strict trace order (instead of direct
    certain comparisons only)."""
    po = po_from_G(M, G)
    poset = set(po)
    big = M.m + 1
    u = [big] * M.m
    parent = {e: e for e in po}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    nbr = {x: (frozenset(g for g in range(M.m) if (x, g) not in G),
               frozenset(g for g in range(M.m) if (g, x) not in G)) for x in range(M.m)}

    def below(a, b):
        Ua, Da = nbr[a]
        Ub, Db = nbr[b]
        return Ua >= Ub and Da <= Db and not (Ub >= Ua and Db <= Da)
    for B in _bases(M):
        if not theta_G(M, G, B):
            continue
        for e in range(M.m):
            if B >> e & 1 or e not in poset:
                continue
            for f in sc.bits(M.fund_circuit(B, e) & ~(1 << e)):
                if f in poset and not below(f, e):
                    parent[find(e)] = find(f)
    for i, x in enumerate(po):
        for z in po[i + 1:]:
            if M.comp[x] == M.comp[z] and nbr[x] == nbr[z]:
                parent[find(x)] = find(z)
    cls = {e: find(e) for e in po}
    arcs = {}
    for x in po:
        for y in po:
            if M.comp[x] == M.comp[y] and below(y, x):
                arcs.setdefault(cls[y], set()).add(cls[x])
    nodes = sorted(set(cls.values()))
    h = scc_heights(nodes, arcs)
    for e in po:
        u[e] = h[cls[e]]
    return u


FAMILIES["xh"] = u_xh
FAMILIES["xlink2"] = u_xlink2
