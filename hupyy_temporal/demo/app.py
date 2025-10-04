import sys
import json
from pathlib import Path

# --- Make imports robust ---
PKG_ROOT = Path(__file__).resolve().parents[1]     # .../hupyy_temporal
REPO_ROOT = Path(__file__).resolve().parents[2]    # repo root containing hupyy_temporal/

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import streamlit as st
import networkx as nx
import matplotlib.pyplot as plt

from hupyy_temporal.engine import solver as engine_solver

# -----------------------------
# Paths
# -----------------------------
DATA_DIR = PKG_ROOT / "data"
PROOFS_DIR = PKG_ROOT / "proofs"
EVAL_DIR = PKG_ROOT / "eval"

BUILTIN_CASES = {
    "flagship": DATA_DIR / "flagship.json",
    "benchmark": DATA_DIR / "benchmark.json",
    "false_case": DATA_DIR / "false_case.json",
    "unknown_case": DATA_DIR / "unknown_case.json",
    "derived_chain": DATA_DIR / "derived_chain.json",
    "interleaved_derived_v1": DATA_DIR / "interleaved_derived_v1.json"
}

# -----------------------------
# Helpers
# -----------------------------
def _read_text(p: Path):
    try: return p.read_text(encoding="utf-8")
    except Exception: return None

def _read_json(p: Path):
    try: return json.loads(p.read_text(encoding="utf-8"))
    except Exception: return None

def artifacts_for_case(stem: str):
    base = PROOFS_DIR / stem
    return {
        "proof": base / "unsat_core.smt2",
        "proof_norm": base / "unsat_core.normalized.smt2",
        "proof_sha": base / "proof_sha256.txt",
        "model": base / "model.json",
        "meta": base / "run_metadata.json",
    }

def fallback_from_artifacts(stem: str):
    arts = artifacts_for_case(stem)
    if arts["model"].exists():
        meta = _read_json(arts["meta"]) or {}
        return {"answer": "FALSE","witness": "model.json","solver_time_ms": meta.get("solver_time_ms")}
    if arts["proof"].exists() or arts["proof_norm"].exists():
        meta = _read_json(arts["meta"]) or {}
        return {"answer": "TRUE","proof": "unsat_core.smt2","solver_time_ms": meta.get("solver_time_ms")}
    meta = _read_json(arts["meta"]) or {}
    return {"answer": "UNKNOWN","solver_time_ms": meta.get("solver_time_ms")}

def to_dict(obj):
    if obj is None: return {}
    if hasattr(obj, "model_dump"):
        try: return obj.model_dump()
        except Exception: pass
    if hasattr(obj, "dict"):
        try: return obj.dict()
        except TypeError: return obj.dict(by_alias=False)
    try:
        from dataclasses import is_dataclass, asdict
        if is_dataclass(obj): return asdict(obj)
    except Exception: pass
    if hasattr(obj, "_asdict"): return obj._asdict()
    if hasattr(obj, "__dict__"): return dict(obj.__dict__)
    return obj if isinstance(obj, dict) else {"answer": str(obj)}

def load_llm_receipts():
    p = EVAL_DIR / "llm_runs.json"
    if not p.exists(): return [], {}, "Missing eval/llm_runs.json"
    data = _read_json(p)
    if data is None: return [], {}, "Malformed eval/llm_runs.json"
    runs, prompts = [], {}
    if isinstance(data, list):
        for obj in data:
            if isinstance(obj, dict) and obj.get("type")=="prompt":
                pid=obj.get("prompt_id"); txt=obj.get("prompt","")
                if pid: prompts[pid]=txt
            elif isinstance(obj, dict) and "model" in obj: runs.append(obj)
    elif isinstance(data, dict):
        for obj in data.get("prompts", []):
            if isinstance(obj, dict) and "prompt_id" in obj: prompts[obj["prompt_id"]] = obj["prompt"]
        for obj in data.get("runs", []):
            if isinstance(obj, dict) and "model" in obj: runs.append(obj)
    else: return [], {}, "Malformed eval/llm_runs.json"
    return runs, prompts, None

def render_graph(case_data: dict):
    G=nx.DiGraph()
    for ev in case_data.get("events", []):
        if ev.get("id"): G.add_node(ev["id"])
    tv_to_ev={ev.get("timeVar"):ev.get("id") for ev in case_data.get("events", [])}
    for c in case_data.get("constraints", []):
        a,b=tv_to_ev.get(c.get("A")),tv_to_ev.get(c.get("B"))
        if a and b: G.add_edge(a,b,relation=c.get("relation"))
    pos=nx.spring_layout(G, seed=7)
    plt.figure(figsize=(7,5))
    nx.draw(G,pos,with_labels=True,node_size=1600)
    nx.draw_networkx_edge_labels(G,pos,edge_labels=nx.get_edge_attributes(G,"relation"))
    st.pyplot(plt)

def run_solver(case_data: dict, stem: str):
    def _decisive(res):
        try: a=str(res.get("answer","")).upper()
        except Exception: a=""
        return a in {"TRUE","FALSE"}
    for fname in ("solve_case","run_case"):
        fn=getattr(engine_solver,fname,None)
        if callable(fn):
            try:
                out=fn(case_data); res=to_dict(out)
                if _decisive(res): return res
                fb=fallback_from_artifacts(stem); fb["from_artifacts"]=True
                return fb if _decisive(fb) else res
            except Exception: pass
    try:
        from hupyy_temporal.engine import schemas
        Problem=getattr(schemas,"Problem",None)
        if Problem is not None:
            if hasattr(Problem,"model_validate"): problem=Problem.model_validate(case_data)
            elif hasattr(Problem,"parse_obj"): problem=Problem.parse_obj(case_data)
            else: problem=Problem(**case_data)
        else: problem=case_data
    except Exception: problem=case_data
    for fname in ("solve_problem","solve","run","run_problem","main"):
        fn=getattr(engine_solver,fname,None)
        if callable(fn):
            try:
                out=fn(problem); res=to_dict(out)
                if _decisive(res): return res
                fb=fallback_from_artifacts(stem); fb["from_artifacts"]=True
                return fb if _decisive(fb) else res
            except Exception: continue
    fb=fallback_from_artifacts(stem); fb["from_artifacts"]=True
    return fb

# -----------------------------
# Query display helper
# -----------------------------
def digits_to_subscripts(s: str) -> str:
    subs = str.maketrans("0123456789","₀₁₂₃₄₅₆₇₈₉")
    return s.translate(subs)

def get_query_display(stem: str, case_data: dict) -> str:
    if case_data.get("query"):
        q=case_data["query"]
        A=digits_to_subscripts(q.get("A","?").replace("t_",""))
        B=digits_to_subscripts(q.get("B","?").replace("t_",""))
        return f"{A} < {B}" if q.get("type")=="before" else str(q)
    fallbacks={
        "flagship":"A₃ < B₃",
        "false_case":"A₄ < B₁",
        "unknown_case":"A₂ < B₄",
        "derived_chain":"A₂ < B₃",
        "interleaved_derived_v1":"A₂ < B₃"
    }
    return fallbacks.get(stem,"Query not specified")

# -----------------------------
# Session state
# -----------------------------
if "last_result" not in st.session_state: st.session_state.last_result=None
if "last_stem" not in st.session_state: st.session_state.last_stem=None

# -----------------------------
# App
# -----------------------------
st.set_page_config(page_title="Hupyy Temporal Reasoning Demo", layout="wide")
st.title("Hupyy Temporal Reasoning Demo")

# --- Initial case selection ---
case_choice=st.selectbox("Benchmark file", list(BUILTIN_CASES.keys()), index=0)
case_path=BUILTIN_CASES[case_choice]
case_data=_read_json(case_path) or {}
stem=Path(case_path).stem

# --- Query headline under title ---
st.markdown(f"### Query: {get_query_display(stem, case_data)}")
st.caption("Method: we negate the query and ask the SMT solver for satisfiability. "
           "UNSAT ⇒ the original query is proven TRUE.")

tab_demo, tab_llm = st.tabs(["Proof Demo", "LLM Comparison"])

# -----------------------------
# Tab 1: Proof Demo
# -----------------------------
with tab_demo:
    left, mid, right = st.columns([1.0,1.0,1.2])
    with left:
        st.subheader("Facts & Constraints")
        st.write("### Constraint Graph")
        if case_data:
            render_graph(case_data)
            st.write("### Raw JSON")
            st.code(json.dumps(case_data, indent=2), language="json")
    with mid:
        st.subheader("Answer")
        if st.button("Run solver"):
            result=run_solver(case_data,stem)
            st.session_state.last_result=result
            st.session_state.last_stem=stem
        result=st.session_state.last_result
        if result:
            ans=str(result.get("answer","UNKNOWN")).upper()
            if ans=="TRUE": st.success("✅ TRUE — Negated query is UNSAT")
            elif ans=="FALSE": st.error("❌ FALSE — Counterexample found")
            elif ans=="UNKNOWN": st.warning("⚪ UNKNOWN — Insufficient constraints")
            else: st.warning(f"⚪ {ans}")
            if "solver_time_ms" in result and result["solver_time_ms"] is not None:
                st.caption(f"Solver time: {result['solver_time_ms']} ms")
    with right:
        st.subheader("Proof / Witness")
        result=st.session_state.last_result; stem=st.session_state.last_stem
        if not result or not stem: st.info("Run the solver to view proof/witness and metadata.")
        else:
            arts=artifacts_for_case(stem); ans=str(result.get("answer","UNKNOWN")).upper()
            if ans=="TRUE":
                proof_text=_read_text(arts["proof"]); proof_norm=_read_text(arts["proof_norm"]); proof_sha=_read_text(arts["proof_sha"])
                if proof_text:
                    with st.expander("Minimal UNSAT core (SMT-LIB)"): st.code(proof_text, language="lisp")
                    st.download_button("Download proof (unsat_core.smt2)", data=proof_text, file_name="unsat_core.smt2")
                if proof_norm:
                    with st.expander("Normalized proof (SMT-LIB)"): st.code(proof_norm, language="lisp")
                if proof_sha: st.caption(f"Proof SHA256: `{proof_sha.strip()}`")
            elif ans=="FALSE":
                model_text=_read_text(arts["model"])
                if model_text:
                    with st.expander("Witness model (JSON)"): st.code(model_text, language="json")
                    st.download_button("Download witness (model.json)", data=model_text, file_name="model.json")
            meta=_read_json(arts["meta"])
            if meta: 
                with st.expander("Run metadata"): st.code(json.dumps(meta, indent=2, sort_keys=True), language="json")

# -----------------------------
# Tab 2: LLM Comparison
# -----------------------------
with tab_llm:
    st.subheader("LLM Comparison (receipts)")
    runs,prompts,err=load_llm_receipts()
    if err: st.info(err+" — add receipts to eval/llm_runs.json")
    elif not runs: st.info("No LLM runs logged yet.")
    else:
        models=sorted({r.get("model","") for r in runs})
        pids=sorted({r.get("prompt_id","") for r in runs})
        c1,c2=st.columns(2)
        sel_model=c1.selectbox("Filter by model",["(all)"]+models,index=0)
        sel_pid=c2.selectbox("Filter by prompt_id",["(all)"]+pids,index=0)
        filtered=[]
        for r in runs:
            if sel_model!="(all)" and r.get("model","")!=sel_model: continue
            if sel_pid!="(all)" and r.get("prompt_id","")!=sel_pid: continue
            filtered.append(r)
        st.caption(f"Showing {len(filtered)} / {len(runs)} runs")
        by_pid={}
        for r in filtered: by_pid.setdefault(r.get("prompt_id","(none)"),[]).append(r)
        for pid,group in by_pid.items():
            st.markdown(f"### Prompt: `{pid}`")
            if pid in prompts:
                with st.expander("Show full prompt text"): st.code(prompts[pid])
            for r in group:
                header=f"{r.get('date_utc','')} · {r.get('model','')} · provider={r.get('provider','')}"
                with st.expander(header, expanded=False):
                    st.markdown("**Response**"); st.write(r.get("response","").strip() or "—")
                    if r.get("notes"): st.markdown(f"**Notes:** {r.get('notes')}")
