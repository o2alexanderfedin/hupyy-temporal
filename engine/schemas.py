from typing import List, Optional, Literal
from pydantic import BaseModel

class Event(BaseModel):
    id: str
    label: Optional[str] = None
    timeVar: str

class Constraint(BaseModel):
    # relations supported in this Day-2 MVP
    relation: Literal["before", "meets", "overlaps", "during", "ge_delta", "geq"]
    A: str
    B: str
    delta: Optional[int] = 0  # used by ge_delta or min-gap for "before"

class Query(BaseModel):
    type: Literal["before", "after", "equals"]
    A: str
    B: str

class Problem(BaseModel):
    events: List[Event]
    constraints: List[Constraint]
    query: Query

class Answer(BaseModel):
    answer: Literal["True", "False", "Unknown"]
    proof: str
    witness: Optional[dict] = None

# NOTE: Supporting both 'ge_delta' and legacy 'geq' spelling
