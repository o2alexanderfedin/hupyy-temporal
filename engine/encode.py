# engine/encode.py
from typing import List, Optional
from engine.schemas import Problem, Query

def _decls(problem: Problem, out: List[str]) -> None:
    out.append("; ---------- declarations ----------")
    lo: Optional[int] = getattr(problem, "horizon_lo", None)
    hi: Optional[int] = getattr(problem, "horizon_hi", None)

    # events[*].timeVar like "t_A1" -> we declare t_A1_s, t_A1_e and well-formedness
    for ev in problem.events:
        base = getattr(ev, "timeVar", None) or f"t_{ev.id}"
        s = f"{base}_s"
        e = f"{base}_e"
        out.append(f"(declare-const {s} Int)")
        out.append(f"(declare-const {e} Int)")
        out.append(f"(assert (<= {s} {e}))")
        if lo is not None:
            out.append(f"(assert (<= {lo} {s}))")
            out.append(f"(assert (<= {lo} {e}))")
        if hi is not None:
            out.append(f"(assert (<= {s} {hi}))")
            out.append(f"(assert (<= {e} {hi}))")

def _encode_constraints(problem: Problem, out: List[str]) -> None:
    out.append("; ---------- constraints ----------")
    for c in problem.constraints:
        rel = c.relation
        # BEFORE (strict): A_e + delta < B_s
        if rel == "before":
            delta = c.delta if getattr(c, "delta", None) is not None else 0
            out.append(f"(assert (< (+ {c.A}_e {delta}) {c.B}_s))")
        # GAP_AT_LEAST / GEQ: B_s >= A_e + delta
        elif rel in ("gap_at_least", "geq"):
            delta = c.delta if getattr(c, "delta", None) is not None else 0
            out.append(f"(assert (>= {c.B}_s (+ {c.A}_e {delta})))")
        # Optional supported relations for later extension
        elif rel == "meets":
            out.append(f"(assert (= {c.A}_e {c.B}_s))")
        elif rel == "overlaps":
            # strict overlaps: A_s < B_s < A_e < B_e
            out.append(
                f"(assert (and (< {c.A}_s {c.B}_s) (< {c.B}_s {c.A}_e) (< {c.A}_e {c.B}_e)))"
            )
        else:
            raise ValueError(f"Unknown relation: {rel}")

def _encode_query_negation(query: Query, out: List[str]) -> None:
    out.append("; ---------- query (negated) ----------")
    out.append("(push)")
    # accept query.kind / query.type / query.relation
    kind = getattr(query, "kind", None) or getattr(query, "type", None) or getattr(query, "relation", None)
    if kind in ("before_strict", "before"):
        # Negation of (A_e < B_s) is (A_e >= B_s)
        out.append(f"(assert (>= {query.A}_e {query.B}_s))")
    else:
        raise ValueError(f"Unknown/unsupported query kind: {kind}")
    out.append("(check-sat)")
    out.append("(pop)")

def encode(problem: Problem) -> str:
    """Encode the temporal problem into SMT-LIB2 (QF_LIA)."""
    out: List[str] = []
    # Professional SMT preamble
    out.append("(set-logic QF_LIA)")
    out.append("(set-option :produce-models true)")
    out.append("(set-option :produce-unsat-cores true)")
    out.append("(set-option :incremental true)")

    _decls(problem, out)
    _encode_constraints(problem, out)
    _encode_query_negation(problem.query, out)

    return "\n".join(out)

# Backwards-compatible export for solver.py
def encode_to_smt(problem: Problem) -> str:
    return encode(problem)
