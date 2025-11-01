# Medical Database Integration Approach

*Discussion Document: 2025-10-31*

## Overview

This document outlines approaches for integrating public medical database APIs into the Hupyy Temporal SMT-LIB solver for real-world constraint verification with external data sources.

---

## 🎯 Objectives

1. **Demonstrate External Resource Loading**: Show that AI Hive® can fetch and integrate real medical data
2. **Real-World Verification**: Validate constraints against actual medical databases, not mock data
3. **Reproducibility**: Ensure results can be verified by external reviewers
4. **Practical Value**: Create use cases relevant to healthcare/clinical domains

---

## 🏗️ Architecture Options

### Option A: AI Hive® Fetches During SMT-LIB Generation
```
User Input (Natural Language)
    ↓
AI Hive® analyzes and identifies external resources needed
    ↓
AI Hive® makes HTTP GET requests to medical APIs
    ↓
AI Hive® incorporates fetched data into SMT-LIB constraints
    ↓
cvc5 solver validates constraints
    ↓
Result: SAT/UNSAT with proof
```

**Pros**:
- Already implemented in prompt (external document loading)
- No changes to solver infrastructure
- AI Hive® handles API complexity

**Cons**:
- Depends on AI Hive®'s ability to make HTTP requests
- Less transparent (data fetch happens in LLM)

### Option B: Python Middleware Fetches Data
```
User Input (Natural Language)
    ↓
Python script identifies API endpoints from problem description
    ↓
Python makes HTTP GET requests
    ↓
Python injects data into problem description
    ↓
AI Hive® generates SMT-LIB with embedded data
    ↓
cvc5 solver validates
```

**Pros**:
- Explicit, transparent data fetching
- Easier to debug and verify
- Can add caching, retry logic, error handling

**Cons**:
- Requires new Python middleware
- More complex integration

### Option C: Hybrid Approach (Recommended)
```
User provides problem + API endpoint URL
    ↓
Python fetches data and caches it locally
    ↓
Problem description references local cached file
    ↓
AI Hive® reads local file and generates SMT-LIB
    ↓
cvc5 validates with real data
```

**Pros**:
- Best of both worlds
- Reproducible (cached data can be saved)
- Transparent audit trail
- Works with existing external resource test case

**Cons**:
- Need to implement Python fetch/cache layer

---

## 🧪 Proposed Use Cases (Prioritized)

### 1. Drug Interaction Verification (HIGH PRIORITY)
**Database**: openFDA Drug Events API
**Complexity**: Medium
**Value**: High - practical clinical relevance

**Example Problem**:
```
Problem: Can a patient safely take Aspirin and Warfarin together?

External Resource:
https://api.fda.gov/drug/event.json?search=patient.drug.medicinalproduct:"ASPIRIN"+AND+patient.drug.medicinalproduct:"WARFARIN"&limit=100

Constraint Logic:
- If adverse event count > threshold → UNSAT (unsafe)
- If no serious interactions reported → SAT (potentially safe)

Expected Result: UNSAT (known dangerous interaction)
```

### 2. Disease Diagnosis Validation (MEDIUM PRIORITY)
**Database**: NIH Clinical Tables + PubMed
**Complexity**: High
**Value**: Medium - demonstrates medical reasoning

**Example Problem**:
```
Given symptoms: [fever, cough, fatigue, loss of taste]
Possible diagnoses: [COVID-19, Influenza, Common Cold]

External Resource:
- NIH Clinical Tables for condition definitions
- PubMed for symptom-disease associations

Constraint: At least N symptoms must match for diagnosis to be valid
Expected Result: SAT for COVID-19, possibly UNSAT for common cold
```

### 3. Medication Dosage Safety (HIGH PRIORITY)
**Database**: openFDA Drug Labeling
**Complexity**: Low-Medium
**Value**: High - clear safety implications

**Example Problem**:
```
Patient: Weight 70kg, Age 45, Renal function normal
Medication: Metformin 1000mg twice daily
Conditions: Type 2 Diabetes, Hypertension

External Resource:
https://api.fda.gov/drug/label.json?search=openfda.generic_name:"metformin"

Constraints:
- Dosage within FDA-approved range for patient profile
- No contraindications with existing conditions
- Renal function adequate for medication

Expected Result: SAT or UNSAT based on real labeling data
```

### 4. ICD Code Consistency (LOW PRIORITY)
**Database**: WHO ICD API
**Complexity**: Low
**Value**: Low - more administrative than clinical

**Example Problem**:
```
Diagnosis description: "Type 2 Diabetes Mellitus"
Assigned ICD-10 code: E11.9

External Resource: WHO ICD API

Constraint: Code must match diagnosis description
Expected Result: SAT if correct, UNSAT if wrong code assigned
```

---

## 🛠️ Implementation Roadmap

### Phase 1: Proof of Concept (Recommended Start)
**Goal**: Demonstrate external data fetching works

**Steps**:
1. ✅ Create simple drug interaction test case
2. ✅ Use openFDA API (no auth required, simple queries)
3. ✅ Manually fetch data and save to JSON file
4. ✅ Create problem description referencing the JSON file
5. ✅ Test with existing external resource test case structure
6. ✅ Verify AI Hive® can read and use the data

**Timeline**: 1-2 hours
**Output**: Working demo with real FDA data

### Phase 2: Python Middleware
**Goal**: Automate data fetching

**Steps**:
1. Create `engine/medical_api_client.py`
2. Implement openFDA query functions
3. Add caching layer (save to `data/medical-cache/`)
4. Add retry logic and error handling
5. Create test suite for API client

**Timeline**: 4-6 hours
**Output**: Reusable API client library

### Phase 3: Multiple Database Support
**Goal**: Expand to NIH, WHO, CDC

**Steps**:
1. Abstract API client interface
2. Implement NIH Clinical Tables client
3. Implement WHO ICD API client (requires API key)
4. Add database selection logic
5. Create comprehensive test suite

**Timeline**: 8-12 hours
**Output**: Multi-database support

### Phase 4: UI Integration
**Goal**: User-friendly interface for medical queries

**Steps**:
1. Add "Medical Verification" page to Streamlit app
2. Database selection dropdown
3. Query builder for common use cases
4. Real-time data preview
5. One-click SMT-LIB generation with fetched data

**Timeline**: 6-8 hours
**Output**: Complete medical verification UI

---

## 📋 Technical Decisions

### Data Fetching Strategy
**Recommendation**: Hybrid approach
- Python fetches and caches data
- AI Hive® reads cached JSON
- Best transparency and reproducibility

### API Selection for POC
**Recommendation**: openFDA Drug Events API
- No authentication required
- Well-documented
- Stable and reliable
- Directly relevant to healthcare
- Public domain data

### Caching Strategy
```python
data/
  medical-cache/
    openfda/
      drug-interactions/
        aspirin-warfarin-20251031.json
        aspirin-ibuprofen-20251031.json
    nih/
      conditions/
        diabetes-mellitus-20251031.json
```

**Benefits**:
- Reproducible results
- No repeated API calls
- Audit trail
- Works offline after initial fetch

### Error Handling
1. **API unavailable**: Use cached data if available
2. **Rate limit exceeded**: Wait and retry with exponential backoff
3. **Invalid response**: Log error, return graceful failure message
4. **No data found**: Explicitly indicate in constraint (may lead to UNKNOWN)

---

## 🔒 Safety and Compliance

### What We CAN Do
✅ Use public, de-identified medical data
✅ Demonstrate constraint verification concepts
✅ Research and educational purposes
✅ Reference real drug/disease information

### What We CANNOT Do
❌ Access patient health records
❌ Handle HIPAA-protected data
❌ Make clinical decisions (openFDA explicitly warns against this)
❌ Claim medical accuracy for production use

### Disclaimers Needed
```
⚠️ IMPORTANT DISCLAIMER:
This system uses public medical databases for research and
demonstration purposes only. Results are NOT validated for
clinical use. Do not use for actual medical decision-making.
Consult qualified healthcare professionals for medical advice.
```

---

## 📊 Success Metrics

### Minimum Viable Demo
- [ ] Successfully fetch data from openFDA API
- [ ] Parse JSON response
- [ ] Generate SMT-LIB constraints using real data
- [ ] Produce SAT/UNSAT result
- [ ] Show clear audit trail (what data was used)

### Extended Success
- [ ] Support 3+ different medical databases
- [ ] Handle 10+ different use cases
- [ ] Comprehensive error handling
- [ ] Performance: <5 seconds for typical query
- [ ] UI for non-technical users

---

## 🎬 Recommended Next Steps

### Immediate (Next 30 minutes)
1. **Create POC drug interaction test**
   - Manually fetch aspirin-warfarin interaction data
   - Save to `data/medical-cache/openfda/aspirin-warfarin.json`
   - Create problem description file
   - Test with current system

### Short Term (Next 2 hours)
2. **Implement basic Python API client**
   - Create `engine/medical_api_client.py`
   - Add openFDA query function
   - Test with 3-5 drug combinations
   - Document usage

### Medium Term (Next Session)
3. **Expand test coverage**
   - Add 5-10 real medical test cases
   - Dosage verification
   - Contraindication checking
   - Drug class interactions

### Long Term (Future)
4. **Full integration**
   - UI page for medical queries
   - Multiple database support
   - Comprehensive documentation
   - Publication-ready demo

---

## 💡 Innovation Opportunity

### Unique Value Proposition
**"First SMT solver with real-time medical database verification"**

This could be a significant differentiator:
- Most SMT research uses synthetic data
- Real medical data adds practical credibility
- Demonstrates external resource integration at scale
- Valuable for healthcare AI verification research

### Potential Research Contributions
1. **Methodology**: External resource integration patterns for SMT solvers
2. **Use Cases**: Medical constraint verification taxonomy
3. **Benchmark**: Real-world medical reasoning test suite
4. **Safety**: Verification approach for clinical decision support systems

---

## 📖 References

- See: `docs/medical-databases-api-access.md` for API details
- openFDA API Documentation: https://open.fda.gov/apis/
- SMT-LIB Standard: https://smtlib.cs.uiowa.edu/
- Related Work: Clinical Decision Support Systems (CDSS) verification

---

*Ready for discussion and decision on approach*
