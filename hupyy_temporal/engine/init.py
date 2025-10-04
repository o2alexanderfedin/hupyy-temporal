"""
Engine package for Hupyy Temporal Reasoning.

Exposes:
- Event, Constraint, Query, Problem (schemas)
- encode_to_smt (encoder)
- solve (solver)
"""

from .schemas import Event, Constraint, Query, Problem
from .encode import encode_to_smt
from .solver import solve

__all__ = [
    "Event",
    "Constraint",
    "Query",
    "Problem",
    "encode_to_smt",
    "solve",
]
