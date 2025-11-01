# Public Medical Databases with API/HTTP GET Access

*Research Date: 2025-10-31*

## Overview

This document catalogs publicly accessible medical databases that provide API/HTTP GET interfaces for programmatic access. These can be used for external resource verification in SMT-LIB constraint solving.

---

## 1. PubMed/NCBI E-utilities

**Type**: Biomedical Literature Database
**Size**: 39+ million citations
**Coverage**: MEDLINE, life science journals, online books

### API Details
- **Name**: E-utilities (Entrez Programming Utilities)
- **Base URL**: `https://eutils.ncbi.nlm.nih.gov/entrez/eutils/`
- **Protocol**: REST/HTTP GET
- **Response Format**: XML, JSON (via retmode parameter)
- **Authentication**: Optional API key (increases rate limit)

### Rate Limits
- Without API key: 3 requests/second
- With free API key: 10 requests/second
- API key management: My NCBI Account Settings

### Key Endpoints
- **ESearch**: Search and retrieve UIDs
  - Example: `esearch.fcgi?db=pubmed&term=diabetes&retmode=json`
- **EFetch**: Retrieve full records by UID
  - Example: `efetch.fcgi?db=pubmed&id=12345678&retmode=xml`
- **ESummary**: Document summaries
- **ELink**: Related records

### Cost
**FREE** - No usage fees

### Use Cases
- Literature verification for medical claims
- Evidence-based constraint validation
- Clinical decision support logic verification

---

## 2. openFDA (FDA Drug Database)

**Type**: FDA Public Data (Drugs, Devices, Foods)
**Coverage**: 2004-present, updated weekly
**Maintained by**: U.S. Food and Drug Administration

### API Details
- **Technology**: Elasticsearch-based REST API
- **Base URL**: `https://api.fda.gov/`
- **Response Format**: JSON
- **Authentication**: Optional API key (recommended for production)

### Drug Endpoints
1. **Drug Labeling** - `/drug/label.json`
   - Product information, warnings, dosage

2. **Adverse Events** - `/drug/event.json`
   - Post-market safety surveillance reports

3. **NDC Directory** - `/drug/ndc.json`
   - National Drug Code product listing

4. **Enforcement Reports** - `/drug/enforcement.json`
   - Drug product recalls

5. **Drugs@FDA** - `/drug/drugsfda.json`
   - FDA-approved drug products

### Example Query
```
GET https://api.fda.gov/drug/label.json?search=openfda.brand_name:lipitor&limit=1
```

### Important Notes
- Data has NOT been validated for clinical production use
- No Personally Identifiable Information (PII)
- Bulk download options available

### Cost
**FREE** - Public domain data

### Use Cases
- Drug interaction constraint verification
- Dosage safety range validation
- Recall status checking
- Adverse event pattern analysis

---

## 3. NIH Clinical Tables Search Service

**Type**: Medical Conditions, ICD Codes
**Size**: 2,400+ medical conditions
**Source**: Regenstrief Institute's Medical Gopher

### API Details
- **Base URL**: `https://clinicaltables.nlm.nih.gov/api/`
- **Protocol**: HTTP GET with query parameters
- **Response Format**: JSON

### Endpoints
- **Conditions**: `/conditions/v3/search`
  - Search medical conditions
  - Returns ICD-10-CM and ICD-9-CM codes

- **Other tables available**:
  - Drugs, procedures, lab tests, etc.

### Example Query
```
GET https://clinicaltables.nlm.nih.gov/api/conditions/v3/search?terms=diabetes
```

### Cost
**FREE**

### Use Cases
- Medical condition classification
- ICD code validation
- Diagnosis code lookup

---

## 4. WHO (World Health Organization) APIs

### 4.1 ICD API (International Classification of Diseases)

**Type**: Disease Classification System
**Coverage**: ICD-10, ICD-11

#### API Details
- **Base URL**: `https://icd.who.int/icdapi`
- **Protocol**: HTTP-based REST API
- **Authentication**: API key required (free registration)
- **Response Format**: JSON, XML

#### Use Cases
- Standard disease classification
- Global health data integration
- Medical coding verification

### 4.2 GHO API (Global Health Observatory)

**Type**: Global Health Statistics
**Coverage**: 1,000+ health indicators

#### API Details
- **Current API**: `https://ghoapi.azureedge.net/api/`
- **Status**: Being deprecated end of 2025
- **Migration**: Moving to data.who.int
- **Format**: OData API

#### Use Cases
- Epidemiological data analysis
- Population health statistics
- Global disease prevalence

### Cost
**FREE** with registration

---

## 5. CDC Open Data API

**Type**: U.S. Public Health Data
**Coverage**: Environmental health, disease surveillance, health statistics

### API Details
- **Portal**: `https://open.cdc.gov/apis.html`
- **Protocol**: Standard REST API
- **Response Format**: JSON
- **Authentication**: Varies by dataset

### Available Data
- Environmental Public Health Tracking
- Disease surveillance data
- Immunization statistics
- Mortality data
- Health surveys

### Cost
**FREE**

### Use Cases
- Disease outbreak modeling
- Public health constraint verification
- Epidemiological trend analysis

---

## 6. Additional Resources

### HealthIT.gov Open Data API
- **URL**: `https://www.healthit.gov/data/api`
- **Format**: CSV, XML
- **Features**: Filtering, sorting, pagination

### European Health Information Portal API
- **URL**: `https://www.healthinformationportal.eu/about/health-information-portal-api`
- **Protocol**: HTTP GET
- **Coverage**: European health datasets

---

## Comparison Matrix

| Database | Size | Update Frequency | Auth Required | Rate Limit | Best For |
|----------|------|------------------|---------------|------------|----------|
| PubMed | 39M+ articles | Daily | Optional | 3-10 req/s | Literature evidence |
| openFDA | Years of data | Weekly | Optional | Varies | Drug safety data |
| NIH Clinical Tables | 2,400+ conditions | Periodic | No | Unknown | Condition lookup |
| WHO ICD | Complete ICD | Periodic | Yes (free) | Unknown | Disease classification |
| CDC | Multiple datasets | Varies | Varies | Varies | US public health |

---

## Integration Recommendations for SMT-LIB

### High Priority
1. **openFDA Drug API** - Well-documented, stable, comprehensive drug data
2. **NIH Clinical Tables** - Simple query interface, no auth required
3. **PubMed E-utils** - Largest evidence base, excellent documentation

### Medium Priority
4. **WHO ICD API** - Requires registration but standardized
5. **CDC Open Data** - Variable quality, dataset-dependent

### Integration Approach
1. **External Resource References**: Problem descriptions include HTTP URLs
2. **Solver Fetches Data**: AI Hive® fetches data during SMT-LIB generation
3. **Constraint Integration**: Fetched data becomes part of constraint logic
4. **Verification**: Solver validates constraints against real medical data

---

## Example Use Cases for SMT-LIB Solver

### 1. Drug Interaction Verification
```
Problem: Can a patient take Drug A and Drug B simultaneously?
External Resource: openFDA adverse events API
Constraint: Check if interaction events exist for drug combination
Result: SAT/UNSAT based on safety data
```

### 2. Disease Diagnosis Logic
```
Problem: Given symptoms S1, S2, S3, is diagnosis D1 possible?
External Resource: NIH Clinical Tables + PubMed literature
Constraint: Symptom-disease associations from medical evidence
Result: Validate diagnostic reasoning
```

### 3. Dosage Safety Verification
```
Problem: Is dosage D safe for patient with conditions C1, C2?
External Resource: openFDA drug labeling
Constraint: Contraindications and dosage limits
Result: Safety validation
```

### 4. Clinical Guideline Compliance
```
Problem: Does treatment plan T comply with guidelines for condition C?
External Resource: PubMed clinical guidelines
Constraint: Treatment protocol adherence rules
Result: Compliance verification
```

---

## Security and Privacy Considerations

### Safe to Use
✅ All listed APIs provide PUBLIC data only
✅ No PII (Personally Identifiable Information)
✅ Aggregated, de-identified information
✅ Suitable for research and development

### Not Suitable For
❌ Real patient data access
❌ HIPAA-protected information
❌ Clinical production systems (openFDA explicitly states this)
❌ Individual health records

---

## References

- PubMed E-utilities: https://www.ncbi.nlm.nih.gov/home/develop/api/
- openFDA: https://open.fda.gov/apis/
- NIH Clinical Tables: https://clinicaltables.nlm.nih.gov/
- WHO ICD API: https://icd.who.int/icdapi
- CDC Open Data: https://open.cdc.gov/apis.html

---

*Last Updated: 2025-10-31*
