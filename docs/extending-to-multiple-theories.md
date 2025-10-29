# Extending Hupyy-Temporal to Support Multiple cvc5 Theories

## Current Situation

The hupyy-temporal project currently has a hardcoded JSON schema for temporal reasoning problems in the Claude AI prompt. This document explores options for supporting other types of SMT problems without overwhelming the prompt.

## Research Findings

### Available External Resources

#### 1. SMT-LIB Standard (Official Specification)

- **Current Version:** 2.7 (February 2025) ⭐ **USE THIS**
- **Website:** https://smt-lib.org
- **Reference Documents:**
  - [SMT-LIB v2.7 Reference](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf) - **Primary reference**
  - [SMT-LIB v2.6 Reference](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) - Recent stable
  - [SMT-LIB v2.0 Reference](https://smt-lib.org/papers/smt-lib-reference-v2.0-r10.12.21.pdf) - Historical reference only

**Important:** Always use **SMT-LIB v2.7** syntax. Version 2.0 (2010) is 15 years old and uses deprecated syntax.

**Coverage:** The SMT-LIB standard defines the official format for ALL SMT theories

**Theory Attributes:** Theory declarations use an attribute-value-based format with predefined keywords including:
- `:definition` - Theory definition
- `:funs` - Function declarations
- `:sorts` - Sort declarations
- `:values` - Value declarations
- `:notes` - Documentation

**Version Evolution:**
- **v2.0 (2010)** - Major upgrade from 1.x, foundational standard
- **v2.6 (2021)** - Added improved datatypes, better quantifier support
- **v2.7 (2025)** - Modern bit-vector syntax, enhanced theory combinations

**cvc5 Support:** cvc5 fully supports SMT-LIB v2.7 including:
- Modern bit-vector conversions: `int_to_bv`, `ubv_to_int`, `sbv_to_int`
- Algebraic datatypes with `match` expressions
- All standardized theories with latest semantics

**Benefit:** Theory-agnostic, well-documented, and solver-native format

**Challenge:** More technical than user-friendly JSON format

#### 2. cvc5 Examples Repository

- **Location:** https://github.com/cvc5/cvc5/tree/main/examples
- **Content:** Production-ready code examples in C++, C, and Java

**Theories Demonstrated:**
- Bit-vectors - Boolean satisfiability with bit-vector theories
- Arithmetic - Linear and nonlinear arithmetic (integers, reals)
- Arrays - Array theory with select/store operations
- Datatypes - Algebraic datatypes
- Strings - String constraints and operations
- Separation Logic - Memory reasoning
- And more...

**Example Organization:**
```
examples/
├── api/
│   ├── cpp/           # C++ examples
│   ├── c/             # C examples
│   ├── java/          # Java examples
│   └── python/        # Python examples
└── SimpleVC*          # "Hello world" examples
```

**Building:** Examples must be built separately after installing cvc5 using CMake

#### 3. cvc5 Beginner's Tutorial

- **Location:** https://cvc5.github.io/tutorials/beginners/
- **Format:** Interactive tutorial with 13 exercises and solutions
- **Languages:** Examples in both Python and SMT-LIB format
- **Solvers:** Works with cvc5 or z3

**Topics Covered:**

**Formal Foundations:**
- Syntax and semantics of SMT
- Theory definitions
- First-order logic foundations

**SMT Theories:**
- Core theory with uninterpreted functions
- Arithmetic (linear and nonlinear, integers and reals)
- Arrays
- Bit-vectors
- Datatypes
- Floating-point arithmetic
- Strings and regular expressions
- Quantifiers
- Non-standard theory extensions
- Theory combinations

**SMT Solver Outputs:**
- Satisfiable results (SAT)
- Unsatisfiable results (UNSAT)
- Unknown/timeout responses

#### 4. cvc5 Official Documentation

- **Main Site:** https://cvc5.github.io/
- **Documentation:** https://cvc5.github.io/docs/
- **Quickstart:** https://cvc5.github.io/docs/cvc5-1.0.2/binary/quickstart.html

**Content:**
- Installation and setup instructions
- SMT-LIB v2 quickstart with practical examples
- API documentation for all language bindings
- Theory descriptions with examples
- Model and proof generation guides

### cvc5 Supported Theories

Based on research, cvc5 supports:

1. **Linear Real Arithmetic** - Simplex-based implementation
2. **Non-linear Arithmetic** - Incremental linearization or cylindrical algebraic coverings
3. **Arrays** - Generalized efficient array decision procedures
4. **Bitvectors** - Lazy bitblasting schema
5. **Separation Logic** - With negation, separation star, and magic wand
6. **Strings and Regular Expressions** - Full string theory support
7. **Datatypes** - Algebraic datatypes with constructors
8. **Floating-Point** - IEEE 754 floating-point arithmetic
9. **Sets and Bags** - Finite sets and multisets
10. **Quantifiers** - First-order quantification

## Recommended Approaches

### Option 1: Schema Library Pattern ⭐ RECOMMENDED

Create a library of JSON schemas for different problem types:

```
demo/problem_schemas/
├── temporal.json      # Current temporal reasoning format
├── arithmetic.json    # Linear/nonlinear arithmetic problems
├── bitvector.json     # Bit-vector constraints
├── array.json         # Array theory problems
├── string.json        # String constraints
└── logic.json         # General logic problems
```

**How It Works:**
1. Add problem type selector in UI (dropdown or tabs)
2. Load appropriate schema dynamically based on selection
3. Pass only relevant schema to Claude prompt
4. Keep prompt size manageable (~500-1000 tokens per schema)

**Advantages:**
- ✅ Prompt stays focused and manageable
- ✅ Easy to add new problem types
- ✅ Schemas are maintainable and versioned
- ✅ Clear separation of concerns

**Implementation Effort:** Low-Medium

### Option 2: SMT-LIB Direct Generation

Skip custom JSON format entirely and generate SMT-LIB directly:

```python
def convert_to_smtlib(text: str) -> str:
    """Have Claude generate SMT-LIB format directly"""
    prompt = f"""Convert this problem to SMT-LIB v2.7 format:

{text}

Return valid SMT-LIB v2.7 code starting with (set-logic ...)
and ending with (check-sat)."""
    # Call Claude CLI
    return smtlib_code
```

**Advantages:**
- ✅ Standard format, no custom schema needed
- ✅ cvc5's native format - no translation layer
- ✅ Direct access to full cvc5 capabilities
- ✅ Eliminates JSON→SMT-LIB conversion bugs

**Challenges:**
- ❌ Requires rewriting solver integration
- ❌ Less user-friendly than JSON
- ❌ Harder to validate and debug

**Implementation Effort:** Medium-High

### Option 3: Few-Shot Learning with References

Update Claude prompt to include external references:

```python
def build_prompt(problem_type: str, text: str) -> str:
    return f"""You are an expert in SMT-LIB format and cvc5 solver.

Reference Resources:
- SMT-LIB v2.7 standard: https://smt-lib.org
- cvc5 examples: https://github.com/cvc5/cvc5/tree/main/examples
- cvc5 tutorial: https://cvc5.github.io/tutorials/beginners/

Problem Type: {problem_type}

Generate JSON matching this schema:
{{load_schema(problem_type)}}

Problem description:
{text}

Return ONLY the JSON object, no explanations."""
```

**Advantages:**
- ✅ Leverages external documentation
- ✅ Claude can access authoritative sources
- ✅ Reduces need for verbose examples in prompt
- ✅ Easy to update by changing URLs

**Challenges:**
- ❌ Depends on Claude's web knowledge cutoff
- ❌ Less deterministic than explicit schemas
- ❌ May require multiple iterations

**Implementation Effort:** Low

### Option 4: Hybrid Approach ⭐⭐ BEST

Combine schema library with external references:

```python
class ProblemTypeHandler:
    def __init__(self, problem_type: str):
        self.schema = load_schema(f"schemas/{problem_type}.json")
        self.smtlib_ref = "https://smt-lib.org"
        self.examples_ref = f"https://github.com/cvc5/cvc5/tree/main/examples/api/{problem_type}"

    def build_prompt(self, text: str) -> str:
        return f"""Convert this {problem_type} problem to JSON.

Schema:
{json.dumps(self.schema, indent=2)}

For SMT-LIB syntax reference: {self.smtlib_ref}
For examples: {self.examples_ref}

Problem:
{text}"""
```

**Steps:**
1. User selects problem type from dropdown
2. System loads corresponding schema template
3. Includes brief SMT-LIB reference in prompt
4. Claude generates JSON following loaded schema
5. Optional: Validate against SMT-LIB semantics

**Advantages:**
- ✅ Best of both worlds
- ✅ Explicit schemas for determinism
- ✅ References for edge cases
- ✅ Extensible without prompt bloat
- ✅ Gradual expansion to new theories

**Implementation Effort:** Medium

## Theory Coverage Comparison

| Theory | Current Support | Schema Library | SMT-LIB Direct | Hybrid |
|--------|----------------|----------------|----------------|--------|
| Temporal (QF_IDL) | ✅ Full | ✅ Full | ✅ Full | ✅ Full |
| Arithmetic | ❌ None | ✅ Easy | ✅ Full | ✅ Full |
| Bit-vectors | ❌ None | ✅ Easy | ✅ Full | ✅ Full |
| Arrays | ❌ None | ✅ Medium | ✅ Full | ✅ Full |
| Strings | ❌ None | ✅ Medium | ✅ Full | ✅ Full |
| Datatypes | ❌ None | ✅ Medium | ✅ Full | ✅ Full |
| Floating-point | ❌ None | ✅ Hard | ✅ Full | ✅ Medium |
| Quantifiers | ❌ None | ❌ Hard | ✅ Full | ✅ Medium |
| Separation Logic | ❌ None | ❌ Hard | ✅ Full | ✅ Medium |

## Implementation Roadmap

### Phase 1: Schema Library Foundation (1-2 weeks)

**Tasks:**
1. Create `demo/problem_schemas/` directory
2. Document temporal schema (current format)
3. Add 2-3 common schemas:
   - Arithmetic (linear constraints)
   - Logic (Boolean satisfiability)
   - Bit-vectors (basic operations)
4. Add problem type selector to UI
5. Update Claude prompt to load schema dynamically

**Deliverables:**
- Schema directory with 4 problem types
- Updated UI with type selector
- Dynamic prompt generation

### Phase 2: Enhanced Validation (2-3 weeks)

**Tasks:**
1. Add JSON schema validation
2. Create SMT-LIB syntax validator
3. Add schema documentation generator
4. Implement error messages with suggestions
5. Add schema version management

**Deliverables:**
- Validation pipeline
- Better error messages
- Versioned schemas

### Phase 3: Advanced Theories (3-4 weeks)

**Tasks:**
1. Add complex theory schemas:
   - Arrays with nested operations
   - Strings with regex
   - Floating-point arithmetic
   - Datatypes with recursion
2. Fetch examples from cvc5 GitHub
3. Cache examples locally
4. Use as few-shot examples in prompts

**Deliverables:**
- 8-10 theory schemas
- Example caching system
- Enhanced Claude prompts

### Phase 4: SMT-LIB Bridge (4-5 weeks)

**Tasks:**
1. Build JSON→SMT-LIB translator
2. Add SMT-LIB validation
3. Support direct SMT-LIB input
4. Generate both formats from Claude
5. Add format conversion utilities

**Deliverables:**
- Bidirectional format conversion
- Full SMT-LIB support
- Format switching UI

## Example Schema Formats

### Arithmetic Schema

```json
{
  "schema_version": "1.0",
  "problem_type": "arithmetic",
  "logic": "QF_LIA",
  "variables": [
    {"name": "x", "type": "Int"},
    {"name": "y", "type": "Int"}
  ],
  "constraints": [
    {"relation": ">=", "left": "x", "right": 0},
    {"relation": "+", "operands": ["x", "y"], "result": "z"}
  ],
  "query": {
    "type": "satisfiability",
    "formula": "x > 10"
  }
}
```

### Bit-vector Schema

```json
{
  "schema_version": "1.0",
  "problem_type": "bitvector",
  "logic": "QF_BV",
  "variables": [
    {"name": "bv1", "type": "BitVec", "width": 8},
    {"name": "bv2", "type": "BitVec", "width": 8}
  ],
  "constraints": [
    {"relation": "bvult", "left": "bv1", "right": "bv2"},
    {"relation": "bvand", "operands": ["bv1", "bv2"], "result": "#x00"}
  ],
  "query": {
    "type": "satisfiability",
    "formula": "bv1 != bv2"
  }
}
```

### String Schema

```json
{
  "schema_version": "1.0",
  "problem_type": "string",
  "logic": "QF_S",
  "variables": [
    {"name": "s1", "type": "String"},
    {"name": "s2", "type": "String"}
  ],
  "constraints": [
    {"relation": "str.contains", "string": "s1", "substring": "hello"},
    {"relation": "str.len", "string": "s1", "operator": ">", "value": 5}
  ],
  "query": {
    "type": "satisfiability",
    "formula": "s1 = str.++ s2 \"world\""
  }
}
```

## References

1. **SMT-LIB Standard**
   - Website: https://smt-lib.org
   - Latest Spec: https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf

2. **cvc5 Project**
   - GitHub: https://github.com/cvc5/cvc5
   - Documentation: https://cvc5.github.io/
   - Examples: https://github.com/cvc5/cvc5/tree/main/examples
   - Tutorial: https://cvc5.github.io/tutorials/beginners/

3. **Academic Papers**
   - "cvc5: A Versatile and Industrial-Strength SMT Solver" (TACAS 2022)
   - "The SMT-LIB Standard Version 2.0" (2010)

## Conclusion

The **Hybrid Approach** is recommended as the optimal path forward:

1. **Immediate Benefits:**
   - Extensible without prompt bloat
   - Maintainable schema library
   - Clear separation by problem type
   - Gradual expansion capability

2. **Long-term Value:**
   - Full theory coverage potential
   - Standard format compatibility
   - Community contribution friendly
   - Production-ready validation

3. **Implementation Path:**
   - Start with 3-4 core schemas
   - Add problem type selector
   - Dynamic prompt generation
   - Iteratively expand theories

**Next Step:** Implement Phase 1 of the roadmap to establish the schema library foundation.
