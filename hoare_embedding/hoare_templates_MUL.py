from adt import adt, Case

from typing import Callable, Tuple

State = dict[str, int]
Condition = Callable[[State], bool]
HoareTriple = Tuple[Condition, "Stmt", Condition]

# Big-step semantics
# ==================

@adt
class Stmt:
    SKIP: Case
    ASSIGN: Case[str, Callable[[State], int]]
    SEQ: Case["Stmt", "Stmt"]
    IF_THEN_ELSE: Case[Callable[[State], bool], "Stmt", "Stmt"]
    WHILE_DO: Case[Callable[[State], bool], "Stmt"]

def evaluate(stmt: Stmt, state: State) -> State:
    return stmt.match(
        # skip (s):
        #     BigStep (Stmt.skip, s) s
        skip=lambda: state,

        # assign (x a s):
        #     BigStep (Stmt.assign x a, s) (s[x ↦ a s])
        assign=lambda x, a: assignH(x, a, state),

        # seq (S T s t u) (hS : BigStep (S, s) t)
        #                (hT : BigStep (T, t) u):
        #     BigStep (S; T, s) u
        seq=lambda s1, s2: evaluate(s2, evaluate(s1, state)),

        # if_true (B S T s t) (hcond : B s)
        #                    (hbody : BigStep (S, s) t):
        #     BigStep (Stmt.ifThenElse B S T, s) t
        # if_false (B S T s t) (hcond : ¬ B s)
        #                     (hbody : BigStep (T, s) t):
        #     BigStep (Stmt.ifThenElse B S T, s) t
        if_then_else=lambda b, s1, s2: evaluate(s1, state) if b(state) else evaluate(s2, state),

        # while_true (B S s t u) (hcond : B s)
        #                       (hbody : BigStep (S, s) t)
        #                       (hrest : BigStep (Stmt.whileDo B S, t) u):
        #     BigStep (Stmt.whileDo B S, s) u
        # while_false (B S s) (hcond : ¬ B s):
        #             BigStep (Stmt.whileDo B S, s) s
        while_do=lambda b, s: while_loopH(b, s, state)
    )

def assignH(x: str, a: Callable[[State], int], state: State) -> State:
    new_state = state.copy()
    new_state[x] = a(state)
    return new_state

def while_loopH(b: Callable[[State], bool], s: Stmt, state: State) -> State:
    if b(state):
        new_state = evaluate(s, state)
        return while_loopH(b, s, new_state)
    else:
        return state

# Magic functions
# ===============
# Some of the following functions are meant to do things that
# cannot easily be implements in python

# However, we describe the semantics of the function 
# in the comments to assist you in synthesizing later proofs

def check_equal(P1: Condition, P2: Condition) -> bool:
    # this represents all possible states
    states = [{"x": x, "y": y} for x in range(10) for y in range(10)]
    return all(P1(state) == P2(state) for state in states)

# P1 ⇒ P2
def check_implies(P1: Condition, P2: Condition) -> bool:
    # this represents all possible states
    states = [{"x": x, "y": y} for x in range(10) for y in range(10)]
    return all((not P1(state)) or P2(state) for state in states)

# represents Q[a/x]
def subst(P: Condition, a: Callable[[State], int], x: str) -> Condition:
    return lambda s: P({**s, x: a(s)})

# Hoare Logic rules
# =================
# We can prove that these rules are correct with respect
# to the big-step semantics. However, this is hard to do
# in Python, so we will not do it here. We can instead use
# the following rules to prove Hoare Triples.

# Corresponds to Lean:
# theorem skip_intro {P} :
#   {* P *} (Stmt.skip) {* P *}
def skip_intro(P: Condition) -> HoareTriple:
    """
    Encodes the Hoare logic rule:
    ———————————— Skip
    {P} skip {P}
    """
    return (P, Stmt.SKIP(), P)
# Example:
# skip_intro(lambda s: s["x"] == 0) == (lambda s: s["x"] == 0, Stmt.SKIP(), lambda s: s["x"] == 0) 

# Corresponds to Lean:
# theorem assign_intro (P) {x a} :
#   {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *}
def assign_intro(x: str, a: Callable[[State], int], Q: Condition) -> HoareTriple:
    """
    Encodes the Hoare logic rule:
    ——————————————————— Assign
    {Q[a/x]} x := a {Q}
    """
    return (subst(Q, a, x), Stmt.ASSIGN(x, a), Q)
# Example
# assign_intro("x", lambda s: s["x"] + 1, lambda s: s["x"] == 1) == (lambda s: s["x"] + 1 == 1, Stmt.ASSIGN("x", lambda s: s["x"] + 1), lambda s: s["x"] == 1)
# note that the precondition is Q[a/x] and the postcondition is Q

# Corresponds to Lean:
# theorem seq_intro {P Q R S T} (hS : {* P *} (S) {* Q *})
#     (hT : {* Q *} (T) {* R *}) :
#   {* P *} (S; T) {* R *}
def seq_intro(HT1: HoareTriple, HT2: HoareTriple) -> HoareTriple:
    """
    Encodes the Hoare logic rule:
    {P} S {R}   {R} S' {Q}
    —————————————————————— Seq
    {P} S; S' {Q}
    """
    P1, S1, R = HT1
    R2, S2, Q = HT2

    assert check_equal(R, R2)

    return (P1, Stmt.SEQ(S1, S2), Q)
# Example
# HT1 = (lambda s: s["x"] == 0, Stmt.SKIP(), lambda s: s["x"] == 0)
# HT2 = (lambda s: s["x"] == 0, Stmt.ASSIGN("x", lambda s: s["x"] + 1), lambda s: s["x"] == 1)
# seq_intro(HT1, HT2) == (lambda s: s["x"] == 0, Stmt.SEQ(Stmt.SKIP(), Stmt.ASSIGN("x", lambda s: s["x"] + 1)), lambda s: s["x"] == 1)

# Corresponds to Lean:
# theorem if_intro {B P Q S T}
#     (hS : {* fun s ↦ P s ∧ B s *} (S) {* Q *})
#     (hT : {* fun s ↦ P s ∧ ¬ B s *} (T) {* Q *}) :
#   {* P *} (Stmt.ifThenElse B S T) {* Q *}
def if_intro(P: Condition, B: Callable[[State], bool], HT1: HoareTriple, HT2: HoareTriple) -> HoareTriple:
    """
    Encodes the Hoare logic rule:
    {P ∧ B} S {Q}   {P ∧ ¬B} S' {Q}
    ——————————————————————————————— If
    {P} if B then S else S' {Q}
    """
    P1, S1, Q1 = HT1
    P2, S2, Q2 = HT2

    assert check_equal(P1, lambda s: P(s) and B(s))
    assert check_equal(P2, lambda s: P(s) and not B(s))
    assert check_equal(Q1, Q2)

    return (P, Stmt.IF_THEN_ELSE(B, S1, S2), Q)

# Corresponds to Lean:
# theorem while_intro (P) {B S}
#     (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
#   {* P *} (Stmt.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *}
def while_intro(I: Condition, B: Callable[[State], bool], HT: HoareTriple) -> HoareTriple:
    """
    Encodes the Hoare logic rule:
    {I ∧ B} S {I}
    ————————————————————————— While
    {I} while B do S {I ∧ ¬B}
    """
    P, S, Q = HT

    assert check_equal(P, lambda s: I(s) and B(s))
    assert check_equal(Q, I)

    return (I, Stmt.WHILE_DO(B, S), lambda s: I(s) and not B(s))


# Corresponds to Lean:
# theorem consequence {P P' Q Q' S}
#     (h : {* P *} (S) {* Q *}) 
#     (hp : ∀s, P' s → P s)
#     (hq : ∀s, Q s → Q' s) :
#   {* P' *} (S) {* Q' *}
def consequence(Pp: Condition, HT: HoareTriple, Qp: Condition) -> HoareTriple:
    """
    Encodes the Hoare logic rule:
    P' → P   {P} S {Q}   Q → Q'
    ——————————————————————————— Conseq
    {P'} S {Q'}
    """
    P, S, Q = HT

    assert check_implies(Pp, P)
    assert check_implies(Q, Qp)

    return (Pp, S, Qp)

# Fun part
# ========
# Now comes the fun part, let's prove some Hoare Triples!

SWAP_PROG = Stmt.SEQ(
    Stmt.ASSIGN("tmp", lambda s: s["x"]),
    Stmt.SEQ(
        Stmt.ASSIGN("x", lambda s: s["y"]),
        Stmt.ASSIGN("y", lambda s: s["tmp"])
    )
)

# Example Proof: Swap
# We want to prove the following Hoare Triple:
# {x = a ∧ y = b} swap {x = b ∧ y = a}
def swap_proof(a, b):
     P = lambda s: s["x"] == a and s["y"] == b
    Q = lambda s: s["x"] == b and s["y"] == a
    
    # Step 1: Assign temporary variable
    # {x = a ∧ y = b} tmp := x {tmp = a ∧ y = b}
    hoare_tmp = assign_intro("tmp", lambda s: s["x"], 
        lambda s: s["y"] == b and s["tmp"] == a)
    
    # Step 2: Assign x to y's value
    # {y = b ∧ tmp = a} x := y {x = b ∧ tmp = a}
    hoare_x = assign_intro("x", lambda s: s["y"], 
        lambda s: s["tmp"] == a and s["x"] == b)
    
    # Step 3: Assign y to tmp's value
    # {x = b ∧ tmp = a} y := tmp {x = b ∧ y = a}
    hoare_y = assign_intro("y", lambda s: s["tmp"], 
        lambda s: s["x"] == b and s["y"] == a)
    
    # Glue them together
    # {x = a ∧ y = b} swap {x = b ∧ y = a}
    return seq_intro(hoare_tmp, 
        seq_intro(hoare_x, hoare_y))

#######################################################################################

# Your turn

MUL = Stmt.SEQ(
    Stmt.ASSIGN("r", lambda s: 0),
    Stmt.WHILE_DO(
        lambda s: s["n"] != 0,
        Stmt.SEQ(
            Stmt.ASSIGN("r", lambda s: s["r"] + s["m"]),
            Stmt.ASSIGN("n", lambda s: s["n"] - 1)
        )
    )
)

# You want to prove the triple: # {n = a ∧ m = b} MUL {r = a * b}

def proof(a, b):
    P = lambda s: s["n"] == a and s["m"] == b
    Q = lambda s: s["r"] == a * b

    # TODO: Fill in the proof!
