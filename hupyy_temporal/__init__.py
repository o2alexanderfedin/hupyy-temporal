"""
Hupyy Temporal package root.

We deliberately do NOT import submodules here to avoid circular/import-time errors.
Downstream code should import from the engine explicitly:

    from hupyy_temporal.engine import solve_problem  # or solve_case/run/etc.
"""

__all__ = ["engine"]
