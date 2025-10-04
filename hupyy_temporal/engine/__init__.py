# hupyy_temporal/engine/__init__.py

from . import schemas
from . import encode
from . import solver

# Re-export optional conveniences (present if defined)
solve_case    = getattr(solver, "solve_case", None)
solve_problem = getattr(solver, "solve_problem", None)
run           = getattr(solver, "run", None)
run_problem   = getattr(solver, "run_problem", None)

Problem = getattr(schemas, "Problem", None)
Query   = getattr(schemas, "Query", None)
Answer  = getattr(schemas, "Answer", None)

__all__ = [
    "schemas", "encode", "solver",
    "solve_case", "solve_problem", "run", "run_problem",
    "Problem", "Query", "Answer",
]
