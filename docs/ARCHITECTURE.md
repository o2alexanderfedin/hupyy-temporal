# Hupyy Temporal - System Architecture

**Version:** 1.7.5
**Last Updated:** November 4, 2025
**Document Type:** Technical Architecture for Investors

---

## Executive Summary

Hupyy Temporal is an AI-powered formal verification platform that transforms natural language queries into mathematical proofs using Satisfiability Modulo Theories (SMT) solvers. The system combines cutting-edge AI (Claude API) with formal methods (SMT-LIB, cvc5 solver) to provide rigorous, mathematically-sound verification of complex temporal, logical, and data constraints.

**Current State:** Production-ready web application with UI testbench
**Target State:** Enterprise SaaS platform with RESTful API
**Key Differentiator:** Only platform combining LLM-based natural language understanding with formal SMT verification

---

## System Architecture Overview

### High-Level Architecture

```mermaid
graph TB
    subgraph "Presentation Layer"
        UI[Streamlit Web UI<br/>demo/app.py]
        API[Future: RESTful API<br/>FastAPI/Flask]
    end

    subgraph "Business Logic Layer"
        AI[AI Integration<br/>ai/claude_client.py]
        Engine[Verification Engine<br/>engine/]
        Reports[Report Generator<br/>reports/]
    end

    subgraph "Integration Layer"
        Solver[SMT Solver Integration<br/>solvers/cvc5_runner.py]
        Parser[Result Parser<br/>solvers/result_parser.py]
    end

    subgraph "External Services"
        Claude[Claude API<br/>Anthropic]
        CVC5[cvc5 SMT Solver<br/>Local Binary]
    end

    subgraph "Storage Layer"
        Config[Configuration<br/>config/constants.py]
        Prefs[User Preferences<br/>JSON Files]
        Logs[Application Logs<br/>logs/]
        PDFs[Generated Reports<br/>reports/]
    end

    UI --> AI
    UI --> Engine
    UI --> Reports
    API -.Future.-> AI
    API -.Future.-> Engine

    AI --> Claude
    Engine --> Solver
    Solver --> CVC5
    Solver --> Parser

    Reports --> PDFs
    AI --> Logs
    Solver --> Logs

    UI --> Prefs
    AI --> Config
    Solver --> Config

    style UI fill:#4A90E2,stroke:#2E5C8A,color:#fff
    style API fill:#7B68EE,stroke:#5A4BB5,color:#fff,stroke-dasharray: 5 5
    style AI fill:#50C878,stroke:#3A9B5C,color:#fff
    style Engine fill:#50C878,stroke:#3A9B5C,color:#fff
    style Solver fill:#F39C12,stroke:#C87F0A,color:#fff
    style Claude fill:#E74C3C,stroke:#C0392B,color:#fff
    style CVC5 fill:#E74C3C,stroke:#C0392B,color:#fff
```

### Component Architecture

```mermaid
graph LR
    subgraph "ai Package"
        CC[ClaudeClient<br/>Unified AI Interface]
        RP[ResponseParsers<br/>Extract SMT-LIB/Explanations]
    end

    subgraph "solvers Package"
        CR[CVC5Runner<br/>Solver Execution]
        ResP[ResultParser<br/>Output Analysis]
    end

    subgraph "engine Package"
        Enc[Encoder<br/>encode.py]
        Sch[Schemas<br/>Pydantic Models]
        Sol[Solver<br/>Legacy]
    end

    subgraph "reports Package"
        PDF[PDFReportGenerator<br/>FPDF-based]
        San[TextSanitizer<br/>Unicode Handling]
        RepSch[ReportSchemas<br/>Pydantic Models]
    end

    CC --> RP
    CR --> ResP
    Enc --> Sch
    PDF --> San
    PDF --> RepSch

    style CC fill:#50C878,stroke:#3A9B5C,color:#fff
    style CR fill:#F39C12,stroke:#C87F0A,color:#fff
    style Enc fill:#9B59B6,stroke:#7D3C98,color:#fff
    style PDF fill:#3498DB,stroke:#2874A6,color:#fff
```

---

## Data Flow Architecture

### End-to-End Verification Flow

```mermaid
sequenceDiagram
    participant User
    participant UI as Streamlit UI
    participant AI as Claude Client
    participant Claude as Claude API
    participant Solver as CVC5 Runner
    participant CVC5 as cvc5 Binary
    participant PDF as PDF Generator

    User->>UI: Enter natural language query
    UI->>UI: Validate input

    alt AI Conversion Enabled
        UI->>AI: convert_to_smtlib(query)
        AI->>Claude: 5-Phase Structured Prompt
        Note over Claude: Phase 1: Problem Comprehension<br/>Phase 2: Domain Modeling<br/>Phase 3: Logic Selection<br/>Phase 4: SMT-LIB Encoding<br/>Phase 5: Self-Verification
        Claude-->>AI: SMT-LIB Code + Phase Outputs
        AI->>AI: extract_smtlib_code()
        AI-->>UI: Formatted SMT-LIB
    else Direct SMT-LIB Input
        User->>UI: Paste SMT-LIB code
    end

    UI->>Solver: run(smtlib_code)
    Solver->>CVC5: Execute solver binary
    CVC5-->>Solver: stdout, stderr, returncode
    Solver->>Solver: parse_cvc5_output()
    Solver-->>UI: CVC5Result(status, model, error)

    alt Error Occurred & Auto-Fix Enabled
        UI->>AI: fix_smtlib_error(code, error)
        AI->>Claude: Error fixing prompt
        Claude-->>AI: Fixed SMT-LIB
        AI-->>UI: Corrected code
        Note over UI: Retry up to 3 times (TDD loop)
    end

    alt Success
        UI->>AI: generate_explanation()
        AI->>Claude: Explanation prompt (Opus model)
        Claude-->>AI: Human-readable explanation
        AI-->>UI: Formatted explanation

        UI->>PDF: generate(ReportData)
        PDF->>PDF: Sanitize all text fields
        PDF->>PDF: Add sections (problem, code, results, explanation)
        PDF-->>UI: PDF bytes
        UI-->>User: Download PDF report
    end

    UI-->>User: Display results
```

### 5-Phase SMT-LIB Generation

```mermaid
graph TD
    Start[Natural Language Query] --> P1[Phase 1: Problem Comprehension]
    P1 --> P1Out[Identify: Entities, Properties,<br/>Requirements, Data Sources]

    P1Out --> P2[Phase 2: Domain Modeling]
    P2 --> P2A[Ground Truth<br/>Assert known facts]
    P2 --> P2B[Derived Logic<br/>Compute properties]
    P2 --> P2C[CRITICAL: Linking Constraints<br/>property => precondition]

    P2A --> P3[Phase 3: Logic Selection]
    P2B --> P3
    P2C --> P3
    P3 --> P3Out[Choose SMT-LIB Logic:<br/>QF_LIA, QF_UFLIA, etc.]

    P3Out --> P4[Phase 4: SMT-LIB Encoding]
    P4 --> P4A[set-logic]
    P4 --> P4B[declare-const]
    P4 --> P4C[assert constraints]
    P4 --> P4D[check-sat]

    P4A --> P5[Phase 5: Self-Verification]
    P4B --> P5
    P4C --> P5
    P4D --> P5

    P5 --> P5A{Verify Phases 1-4<br/>Complete?}
    P5A -->|Missing| P5B[Add missing logic]
    P5A -->|Complete| P5C{Linking Constraints<br/>Present?}

    P5B --> P5C
    P5C -->|No| P5D[CRITICAL: Add<br/>derived => precondition]
    P5C -->|Yes| Output[Valid SMT-LIB Code]
    P5D --> Output

    style P2C fill:#E74C3C,stroke:#C0392B,color:#fff
    style P5C fill:#E74C3C,stroke:#C0392B,color:#fff
    style P5D fill:#E74C3C,stroke:#C0392B,color:#fff
    style Output fill:#27AE60,stroke:#1E8449,color:#fff
```

### TDD Loop (Auto-Error Correction)

```mermaid
graph TD
    Start[Execute SMT-LIB Code] --> Exec[cvc5 Solver Execution]
    Exec --> Check{Status?}

    Check -->|sat/unsat/unknown| Success[Success Path]
    Check -->|Error| AutoFix{Auto-Fix<br/>Enabled?}

    AutoFix -->|No| DisplayError[Display Error to User]
    AutoFix -->|Yes| Attempt{Attempt < 3?}

    Attempt -->|No| MaxRetries[Max Retries Reached<br/>Display Error]
    Attempt -->|Yes| FixPrompt[Send to Claude:<br/>Code + Error + Context]

    FixPrompt --> ExtractFix[Extract Fixed Code]
    ExtractFix --> RecordFix[Record Correction<br/>in History]
    RecordFix --> Exec

    Success --> GenExplanation[Generate Human Explanation]
    GenExplanation --> GenPDF[Generate PDF Report]
    GenPDF --> Download[User Downloads Report]

    style Success fill:#27AE60,stroke:#1E8449,color:#fff
    style MaxRetries fill:#E74C3C,stroke:#C0392B,color:#fff
    style Download fill:#3498DB,stroke:#2874A6,color:#fff
```

---

## Technology Stack

### Core Technologies

| Layer | Technology | Version | Purpose |
|-------|-----------|---------|---------|
| **Frontend** | Streamlit | 1.x | Rapid web UI prototyping |
| **AI Backend** | Claude API | Latest | Natural language → SMT-LIB conversion |
| **Verification** | cvc5 SMT Solver | Latest | Formal constraint solving |
| **Language** | Python | 3.12+ | Primary development language |
| **Reports** | FPDF | 2.x | PDF generation |
| **Schemas** | Pydantic | 2.x | Type-safe data validation |
| **Testing** | pytest, Playwright | Latest | Unit, integration, E2E tests |

### External Dependencies

```mermaid
graph TD
    subgraph "AI Services"
        Anthropic[Anthropic Claude API<br/>Haiku 3.5 / Sonnet 4.5 / Opus]
    end

    subgraph "Formal Methods"
        CVC5Solver[cvc5 SMT Solver<br/>Local Binary]
        SMTLIB[SMT-LIB v2.7<br/>Standard Format]
    end

    subgraph "Python Ecosystem"
        Streamlit2[Streamlit<br/>Web Framework]
        Pydantic2[Pydantic<br/>Data Validation]
        FPDF2[FPDF<br/>PDF Generation]
        Pytest[pytest/Playwright<br/>Testing]
    end

    App[Hupyy Temporal] --> Anthropic
    App --> CVC5Solver
    App --> SMTLIB
    App --> Streamlit2
    App --> Pydantic2
    App --> FPDF2
    App --> Pytest

    style App fill:#4A90E2,stroke:#2E5C8A,color:#fff
    style Anthropic fill:#E74C3C,stroke:#C0392B,color:#fff
    style CVC5Solver fill:#F39C12,stroke:#C87F0A,color:#fff
```

### Why These Technologies?

**Streamlit:**
- Rapid prototyping and iteration
- Python-native (no JS required)
- Easy to replace with FastAPI for production SaaS

**Claude API:**
- State-of-the-art reasoning capabilities
- Best-in-class for formal reasoning tasks
- Multiple models (Haiku, Sonnet, Opus) for cost/quality trade-offs

**cvc5 SMT Solver:**
- Industry-leading SMT solver
- Open-source (BSD license)
- Active development and community
- Supports all major SMT-LIB logics

**Pydantic:**
- Runtime type validation
- Automatic API schema generation
- Perfect for future REST API

---

## Component Details

### 1. Presentation Layer (demo/app.py)

**Purpose:** Web-based UI for user interaction
**Lines of Code:** ~1,635 lines
**Key Features:**
- Natural language query input
- Direct SMT-LIB code input
- Model selection (Haiku/Sonnet/Opus)
- User preferences persistence
- Real-time result display
- PDF report download

**Architecture Pattern:** Monolithic Streamlit app (transitioning to modular)

**User Preferences:**
```python
{
    "model": "sonnet",              # AI model selection
    "use_claude_conversion": false, # Enable AI conversion
    "auto_fix_errors": true        # Enable TDD loop
}
```

### 2. AI Integration Layer (ai/)

**ClaudeClient (ai/claude_client.py):**
- Unified interface for all Claude API operations
- Consolidates 11+ duplicate subprocess calls
- Type-safe with custom exception hierarchy
- Configurable timeouts and models

**Key Methods:**
```python
class ClaudeClient:
    def invoke(prompt, model, timeout) -> str
    def convert_to_smtlib(text) -> str
    def fix_smtlib_error(code, error) -> str
    def generate_explanation(...) -> str
```

**ResponseParsers (ai/response_parsers.py):**
- Extract SMT-LIB code from markdown blocks
- Two-pass extraction with proof content detection
- Handles preambles and edge cases

### 3. Solver Integration Layer (solvers/)

**CVC5Runner (solvers/cvc5_runner.py):**
- Unified cvc5 execution with consistent timeouts
- Type-safe CVC5Result dataclass
- Temp file management
- Environment setup (DYLD_LIBRARY_PATH, LD_LIBRARY_PATH)

**CVC5Result:**
```python
@dataclass
class CVC5Result:
    stdout: str
    stderr: str
    wall_time_ms: int
    status: str  # "sat", "unsat", "unknown"
    model: Optional[str]
    error: Optional[str]
    has_error: bool
```

**ResultParser (solvers/result_parser.py):**
- Parse cvc5 output into structured data
- Distinguish real errors from informational stderr
- Extract satisfying models

### 4. Verification Engine (engine/)

**Encoder (engine/encode.py):**
- Temporal constraint encoding
- Allen's Interval Algebra relations
- QF_LIA logic generation

**Schemas (engine/schemas.py):**
```python
class Event(BaseModel):
    id: str
    label: Optional[str]
    timeVar: str

class Constraint(BaseModel):
    relation: Literal["before", "meets", "overlaps", "during", "ge_delta", "geq"]
    A: str
    B: str
    delta: Optional[int]

class Query(BaseModel):
    type: Literal["before", "after", "equals"]
    A: str
    B: str

class Problem(BaseModel):
    events: List[Event]
    constraints: List[Constraint]
    query: Query
```

### 5. Report Generation (reports/)

**PDFReportGenerator (reports/pdf_generator.py):**
- SOLID-compliant PDF generation
- Comprehensive sanitization (Unicode → ASCII)
- Multi-section reports with optional components

**Report Sections:**
1. Header (title, metadata)
2. Problem Statement
3. Phase Analysis (optional)
4. Generated SMT-LIB Code
5. Verification Results
6. Human-Readable Explanation (optional)
7. Auto-Correction History (optional)
8. Technical Details Appendix

**TextSanitizer (reports/sanitizers.py):**
- Unicode → ASCII conversion for PDF compatibility
- Context-specific sanitization
- Truncation limits per section

### 6. Configuration (config/)

**Constants (config/constants.py):**
- Centralized timeout configuration
- Model selection
- File paths
- Retry limits
- Truncation limits

**Key Constants:**
```python
TIMEOUT_AI_CONVERSION = 300      # 5 minutes for 5-phase processing
TIMEOUT_AI_ERROR_FIXING = 180    # 3 minutes for phase-aware correction
TIMEOUT_AI_EXPLANATION = 180     # 3 minutes for complex queries
TIMEOUT_CVC5_EXEC = 120          # 2 minutes for solver execution
MAX_TDD_LOOP_ATTEMPTS = 10       # Auto-correction retry limit
```

---

## SaaS Vision: Current vs. Future

### Current Architecture (v1.7.5)

```mermaid
graph LR
    User[User Browser] --> Streamlit[Streamlit UI<br/>Port 8501]
    Streamlit --> Logic[Business Logic<br/>In demo/app.py]
    Logic --> AI[Claude API]
    Logic --> Solver[cvc5 Solver]
    Logic --> PDF[PDF Generator]

    style Streamlit fill:#4A90E2,stroke:#2E5C8A,color:#fff
```

**Characteristics:**
- Monolithic Streamlit application
- Single-user sessions
- Local file storage
- Direct API calls embedded in UI code

### Target SaaS Architecture

```mermaid
graph TB
    subgraph "API Gateway Layer"
        LB[Load Balancer<br/>nginx/AWS ALB]
        Auth[Authentication<br/>JWT/OAuth2]
    end

    subgraph "Application Layer"
        API1[API Server 1<br/>FastAPI]
        API2[API Server 2<br/>FastAPI]
        API3[API Server 3<br/>FastAPI]
    end

    subgraph "Service Layer"
        VerifSvc[Verification Service]
        AISvc[AI Service<br/>Claude Integration]
        SolverSvc[Solver Service<br/>cvc5 Pool]
        ReportSvc[Report Service<br/>PDF Generation]
    end

    subgraph "Data Layer"
        DB[(PostgreSQL<br/>User Data, Jobs)]
        Cache[(Redis<br/>Session Cache)]
        S3[S3/Object Storage<br/>Reports, Logs]
        Queue[RabbitMQ/SQS<br/>Job Queue]
    end

    subgraph "Clients"
        WebUI[Web UI<br/>React/Streamlit]
        MobileApp[Mobile App<br/>Future]
        CLI[CLI Client<br/>Future]
        SDK[Python SDK<br/>Future]
    end

    WebUI --> LB
    MobileApp -.Future.-> LB
    CLI -.Future.-> LB
    SDK -.Future.-> LB

    LB --> Auth
    Auth --> API1
    Auth --> API2
    Auth --> API3

    API1 --> VerifSvc
    API2 --> VerifSvc
    API3 --> VerifSvc

    VerifSvc --> AISvc
    VerifSvc --> SolverSvc
    VerifSvc --> ReportSvc

    VerifSvc --> DB
    VerifSvc --> Cache
    VerifSvc --> Queue
    ReportSvc --> S3

    style LB fill:#E74C3C,stroke:#C0392B,color:#fff
    style API1 fill:#50C878,stroke:#3A9B5C,color:#fff
    style API2 fill:#50C878,stroke:#3A9B5C,color:#fff
    style API3 fill:#50C878,stroke:#3A9B5C,color:#fff
    style DB fill:#3498DB,stroke:#2874A6,color:#fff
    style Queue fill:#F39C12,stroke:#C87F0A,color:#fff
```

### RESTful API Design

**Proposed Endpoints:**

```
POST   /api/v1/verify
    Body: { "query": "...", "mode": "nl|smtlib", "model": "haiku|sonnet|opus" }
    Response: { "job_id": "...", "status": "queued" }

GET    /api/v1/jobs/{job_id}
    Response: { "status": "pending|running|completed|failed", "result": {...} }

GET    /api/v1/jobs/{job_id}/report
    Response: PDF binary (Content-Type: application/pdf)

POST   /api/v1/verify/sync
    Body: { "query": "...", "timeout": 60 }
    Response: { "status": "sat|unsat|unknown", "model": {...}, "explanation": "..." }

GET    /api/v1/models
    Response: { "models": ["haiku", "sonnet", "opus"], "default": "sonnet" }

POST   /api/v1/validate
    Body: { "smtlib_code": "..." }
    Response: { "valid": true|false, "errors": [...] }
```

### Migration Path

**Phase 1: API Extraction (Q1 2026)**
- Extract business logic from demo/app.py
- Create FastAPI service layer
- Maintain Streamlit UI as first client

**Phase 2: Database Integration (Q2 2026)**
- Add PostgreSQL for job persistence
- Implement user authentication
- Add job queue for async processing

**Phase 3: Multi-tenancy (Q3 2026)**
- Implement tenant isolation
- Add usage metering and billing
- Deploy on cloud infrastructure (AWS/GCP)

**Phase 4: Advanced Features (Q4 2026)**
- React-based web UI
- Mobile applications
- Python SDK for programmatic access

---

## Scalability & Performance

### Current Performance Metrics

| Operation | Time | Bottleneck |
|-----------|------|------------|
| AI Conversion (5-phase) | 30-180s | Claude API latency |
| cvc5 Solver Execution | 0.1-60s | Problem complexity |
| PDF Generation | 0.5-2s | fpdf library |
| Explanation Generation | 20-120s | Claude API (Opus model) |

### Scaling Strategy

**Horizontal Scaling:**
```mermaid
graph LR
    subgraph "Before Scaling"
        U1[User 1] --> A1[App Instance 1]
        U2[User 2] --> A1
        U3[User 3] --> A1
    end

    subgraph "After Scaling"
        U4[User 1] --> LB2[Load Balancer]
        U5[User 2] --> LB2
        U6[User 3] --> LB2

        LB2 --> A2[App Instance 1]
        LB2 --> A3[App Instance 2]
        LB2 --> A4[App Instance 3]

        A2 --> Pool[cvc5 Solver Pool]
        A3 --> Pool
        A4 --> Pool
    end

    style LB2 fill:#E74C3C,stroke:#C0392B,color:#fff
    style Pool fill:#F39C12,stroke:#C87F0A,color:#fff
```

**Caching Strategy:**
- Cache SMT-LIB conversions (NL query → code)
- Cache solver results for identical problems
- Cache explanations for common patterns
- TTL: 24 hours for active queries

**Async Processing:**
- Job queue for long-running verifications
- Webhook notifications on completion
- Batch processing for multiple queries

**Rate Limiting:**
- Per-user quotas (queries/hour)
- Model-specific limits (Opus more restrictive)
- Graceful degradation (queue vs. reject)

---

## Security & Reliability

### Security Measures

**Input Validation:**
- Pydantic schema validation for all inputs
- SMT-LIB syntax validation before execution
- Timeout enforcement on all external calls
- Sandboxed cvc5 execution (temp files, no network)

**Data Protection:**
- User preferences stored locally (current)
- Future: Encrypted database storage
- HTTPS for all API communication
- JWT-based authentication (future)

**Dependency Security:**
- Regular security audits (pip-audit)
- Pinned dependency versions
- Automated CVE scanning (GitHub Dependabot)

### Reliability Measures

**Error Handling:**
- Custom exception hierarchy
- Comprehensive logging (timestamps, context)
- TDD loop for auto-recovery
- User-friendly error messages

**Monitoring:**
```mermaid
graph TD
    App[Application] --> Logs[Application Logs<br/>logs/hupyy_YYYYMMDD.log]
    App --> Metrics[Metrics<br/>Future: Prometheus]
    App --> Traces[Tracing<br/>Future: OpenTelemetry]

    Logs --> Alerts[Alert Manager<br/>Future]
    Metrics --> Alerts
    Traces --> Debugging[Debug Analysis]

    Alerts --> Oncall[On-Call Team]

    style Logs fill:#50C878,stroke:#3A9B5C,color:#fff
    style Metrics fill:#F39C12,stroke:#C87F0A,color:#fff,stroke-dasharray: 5 5
    style Alerts fill:#E74C3C,stroke:#C0392B,color:#fff,stroke-dasharray: 5 5
```

**Logging Levels:**
- DEBUG: Detailed execution traces
- INFO: User actions, API calls
- WARNING: Recoverable errors, TDD loop retries
- ERROR: Unrecoverable failures

**Current Log Example:**
```
2025-11-04 13:20:15 [INFO] [demo.app:1250] User submitted query (247 chars)
2025-11-04 13:20:15 [INFO] [ai.claude_client:103] Invoking Claude CLI: model=sonnet, timeout=300s
2025-11-04 13:21:42 [INFO] [ai.claude_client:120] Claude CLI succeeded: 3521 chars returned
2025-11-04 13:21:42 [INFO] [solvers.cvc5_runner:175] Running cvc5: /tmp/tmp_abc123.smt2
2025-11-04 13:21:43 [INFO] [solvers.result_parser:45] Parsed result: status=unsat, has_error=False
```

---

## Development Practices

### Code Quality

**SOLID Principles:**
- Single Responsibility: Each class has one job
- Open/Closed: Extensible without modification
- Liskov Substitution: Subtypes are substitutable
- Interface Segregation: Focused interfaces
- Dependency Inversion: Depend on abstractions

**Type Safety:**
- Pydantic models for all data structures
- Type hints throughout codebase
- mypy static analysis (enabled)
- No 'any' types

**Testing Strategy:**

```mermaid
graph TD
    subgraph "Test Pyramid"
        E2E[E2E Tests<br/>Playwright<br/>tests/e2e/]
        Integration[Integration Tests<br/>pytest<br/>tests/manual/]
        Unit[Unit Tests<br/>pytest<br/>tests/unit/]
    end

    Unit --> Integration
    Integration --> E2E

    style Unit fill:#27AE60,stroke:#1E8449,color:#fff
    style Integration fill:#F39C12,stroke:#C87F0A,color:#fff
    style E2E fill:#3498DB,stroke:#2874A6,color:#fff
```

**Test Coverage:**
- Unit tests: 60+ tests for core components
- Integration tests: TDD loop, end-to-end flows
- E2E tests: Full UI workflows with Playwright
- Manual tests: Complex verification scenarios

**Continuous Integration:**
- Git Flow: feature branches → develop → main
- Automated testing on PR (future)
- Semantic versioning (v1.7.5)
- GitHub Releases with detailed notes

### Documentation Standards

**Code Documentation:**
- Docstrings for all public functions/classes
- Type hints for all parameters/returns
- Inline comments for complex logic
- README files in each module

**Architecture Documentation:**
- This document (ARCHITECTURE.md)
- Prompt engineering analysis (PROMPT_ENGINEERING_ANALYSIS.md)
- Sprint reports (docs/sprints/)
- UI/UX documentation (docs/ui-ux/)

**Release Documentation:**
- Detailed release notes for each version
- Migration guides for breaking changes
- Test verification reports
- PDF examples in reports/

---

## Deployment Architecture

### Current Deployment (Local Development)

```mermaid
graph TD
    Dev[Developer Machine] --> Git[Git Repository<br/>GitHub]
    Dev --> Local[Local Streamlit<br/>Port 8501]
    Local --> CVC5Local[Local cvc5 Binary<br/>bin/cvc5]
    Local --> ClaudeLocal[Claude API<br/>via CLI]

    style Local fill:#4A90E2,stroke:#2E5C8A,color:#fff
```

### Target Production Deployment (AWS Example)

```mermaid
graph TB
    subgraph "CDN & DNS"
        R53[Route 53<br/>DNS]
        CF[CloudFront<br/>CDN]
    end

    subgraph "VPC - Public Subnet"
        ALB[Application Load Balancer]
        NAT[NAT Gateway]
    end

    subgraph "VPC - Private Subnet - AZ1"
        ECS1[ECS Fargate<br/>API Container 1]
        RDS1[RDS Read Replica 1]
    end

    subgraph "VPC - Private Subnet - AZ2"
        ECS2[ECS Fargate<br/>API Container 2]
        RDS2[RDS Read Replica 2]
    end

    subgraph "VPC - Private Subnet - AZ3"
        RDSMaster[(RDS PostgreSQL<br/>Master)]
        Redis[(ElastiCache<br/>Redis Cluster)]
        SQS[SQS Queue<br/>Job Processing]
    end

    subgraph "Storage"
        S3Reports[S3 Bucket<br/>PDF Reports]
        S3Logs[S3 Bucket<br/>Application Logs]
    end

    subgraph "Monitoring"
        CW[CloudWatch<br/>Metrics & Logs]
        XRay[X-Ray<br/>Distributed Tracing]
    end

    Users[Users] --> R53
    R53 --> CF
    CF --> ALB
    ALB --> ECS1
    ALB --> ECS2

    ECS1 --> RDSMaster
    ECS2 --> RDSMaster
    ECS1 --> RDS1
    ECS2 --> RDS2

    ECS1 --> Redis
    ECS2 --> Redis

    ECS1 --> SQS
    ECS2 --> SQS

    ECS1 --> S3Reports
    ECS2 --> S3Reports

    ECS1 --> CW
    ECS2 --> CW
    ECS1 --> XRay
    ECS2 --> XRay

    ECS1 --> S3Logs
    ECS2 --> S3Logs

    style ALB fill:#E74C3C,stroke:#C0392B,color:#fff
    style ECS1 fill:#50C878,stroke:#3A9B5C,color:#fff
    style ECS2 fill:#50C878,stroke:#3A9B5C,color:#fff
    style RDSMaster fill:#3498DB,stroke:#2874A6,color:#fff
```

**Infrastructure as Code:**
- Terraform for infrastructure provisioning
- Docker for containerization
- GitHub Actions for CI/CD
- Helm charts for Kubernetes (alternative)

---

## Roadmap & Future Enhancements

### Short-Term (Q1 2026)

**API Development:**
- Extract business logic into FastAPI
- Define RESTful endpoints
- Implement async job processing
- Add OpenAPI/Swagger documentation

**Testing & Quality:**
- Increase unit test coverage to 80%
- Add performance benchmarks
- Implement load testing (Locust)
- Add integration test suite

### Medium-Term (Q2-Q3 2026)

**Multi-Tenancy:**
- User authentication (JWT)
- Organization/team support
- Usage metering and billing
- Admin dashboard

**Advanced Features:**
- Batch verification API
- Webhook notifications
- Custom solver configurations
- Multi-solver support (Z3, MathSAT)

**UI/UX:**
- React-based web UI
- Visualization of verification results
- Interactive proof exploration
- Shared verification links

### Long-Term (Q4 2026+)

**Platform Expansion:**
- Mobile applications (iOS, Android)
- VS Code extension
- Python SDK for programmatic access
- Integration marketplace (Zapier, Make)

**Enterprise Features:**
- On-premise deployment option
- SSO integration (SAML, OAuth)
- Audit logging and compliance
- SLA guarantees (99.9% uptime)

**AI Enhancements:**
- Fine-tuned models for domain-specific verification
- Multi-modal input (diagrams, tables)
- Automated test case generation
- Proof optimization suggestions

---

## Business Model & Pricing Strategy

### Target Customer Segments

1. **Enterprise Compliance:** Organizations needing formal verification of policies, access control, temporal constraints
2. **Academic Research:** Universities and research labs using formal methods
3. **Software Verification:** Teams verifying system properties, protocol correctness
4. **Blockchain/Crypto:** Smart contract verification and formal proofs

### Pricing Tiers (Proposed)

| Tier | Price | Queries/Month | Models | Support |
|------|-------|---------------|--------|---------|
| Free | $0 | 100 | Haiku only | Community |
| Pro | $99/mo | 1,000 | All models | Email |
| Team | $499/mo | 10,000 | All models | Priority |
| Enterprise | Custom | Unlimited | Custom | Dedicated |

### Unit Economics

**Cost Structure:**
- Claude API: $0.01-$0.15 per query (model-dependent)
- Compute: $0.001-$0.01 per query (cvc5 execution)
- Storage: $0.001 per report
- Infrastructure: ~$500/month (base)

**Target Margins:**
- Gross margin: 70-80%
- CAC payback: 6 months
- LTV/CAC ratio: 3:1

---

## Competitive Advantage

### Unique Value Propositions

1. **AI + Formal Methods Convergence:** Only platform combining LLM natural language understanding with rigorous SMT verification
2. **5-Phase Structured Approach:** Proprietary prompt engineering for reliable SMT-LIB generation
3. **TDD Loop:** Automatic error recovery increases success rate
4. **Multi-Domain:** Not limited to one verification domain (temporal, data, mathematical, graph theory)
5. **Developer-Friendly:** Simple API, comprehensive documentation, multiple client options

### Barriers to Entry

**Technical Moats:**
- 18+ months of prompt engineering refinement
- Domain expertise in both AI and formal methods
- Production-tested error handling and edge cases
- Comprehensive test suite and quality assurance

**Network Effects:**
- Shared verification templates
- Community-contributed examples
- Integration ecosystem

**Data Moat:**
- Query patterns and optimization data
- Error correction patterns
- Fine-tuning datasets (future)

---

## Risk Analysis & Mitigation

### Technical Risks

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Claude API changes | High | Medium | Abstract API, support multiple providers |
| cvc5 solver bugs | Medium | Low | Multi-solver support, extensive testing |
| Prompt drift | Medium | Medium | Version control prompts, regression testing |
| Scaling bottlenecks | High | Medium | Async processing, caching, horizontal scaling |

### Business Risks

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Competitor entry | High | Medium | Build moat quickly, focus on UX |
| AI cost inflation | Medium | High | Support cheaper models, optimize prompts |
| Market adoption | High | Medium | Free tier, education, partnerships |
| Compliance requirements | Medium | Low | SOC 2, GDPR compliance from start |

### Operational Risks

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Key person dependency | High | Medium | Documentation, knowledge sharing |
| Infrastructure outages | High | Low | Multi-region deployment, DR plan |
| Security breach | Critical | Low | Pen testing, security audits, bug bounty |

---

## Team & Expertise Required

### Current Team (Solo Developer)

**Skills Demonstrated:**
- AI/ML: Prompt engineering, Claude API integration
- Formal Methods: SMT-LIB, cvc5, constraint solving
- Software Engineering: Python, testing, architecture
- Product: UI/UX, documentation, release management

### Recommended Team Expansion

**Phase 1 (2-3 people):**
- **Backend Engineer:** FastAPI, PostgreSQL, async processing
- **DevOps Engineer:** AWS/GCP, Terraform, monitoring

**Phase 2 (5-7 people):**
- **Frontend Engineer:** React, TypeScript, UI/UX
- **AI/ML Engineer:** Fine-tuning, prompt optimization
- **Sales Engineer:** Customer onboarding, demos
- **Product Manager:** Roadmap, customer feedback

**Phase 3 (10-15 people):**
- **Engineering Team:** 4-5 engineers (backend, frontend, ML)
- **Operations:** 2-3 (DevOps, SRE, security)
- **Go-to-Market:** 3-4 (sales, marketing, customer success)
- **Leadership:** CTO, VP Product

---

## Financial Projections (3-Year)

### Revenue Projections

| Metric | Year 1 | Year 2 | Year 3 |
|--------|--------|--------|--------|
| Free users | 1,000 | 5,000 | 20,000 |
| Pro subscribers | 50 | 300 | 1,200 |
| Team subscribers | 10 | 100 | 500 |
| Enterprise customers | 2 | 10 | 30 |
| **MRR** | **$6K** | **$70K** | **$350K** |
| **ARR** | **$72K** | **$840K** | **$4.2M** |

### Cost Projections

| Category | Year 1 | Year 2 | Year 3 |
|----------|--------|--------|--------|
| Salaries | $200K | $600K | $1.2M |
| AI/Compute | $20K | $100K | $300K |
| Infrastructure | $10K | $50K | $150K |
| Sales/Marketing | $30K | $150K | $400K |
| **Total Costs** | **$260K** | **$900K** | **$2.05M** |
| **Gross Margin** | -260% | 7% | 51% |

### Funding Requirements

**Seed Round (Year 1):** $500K
- 18 months runway
- Team expansion (2-3 people)
- Product-market fit validation

**Series A (Year 2):** $3M
- Scale go-to-market
- Engineering team expansion
- Multi-region deployment

---

## Conclusion

Hupyy Temporal represents a unique convergence of AI and formal methods, addressing a critical gap in the market for accessible, reliable formal verification. The current architecture demonstrates technical feasibility with a production-ready testbench, while the roadmap to a scalable SaaS platform is clear and achievable.

**Key Strengths:**
- Proven technology stack
- Proprietary 5-phase prompt engineering
- SOLID architecture ready for scaling
- Clear path to SaaS transformation
- Strong competitive moats

**Investment Opportunity:**
- Large addressable market (compliance, verification, academia)
- High gross margins (70-80%)
- Defensible technical moat
- Experienced solo founder with full-stack capabilities
- Clear 3-year path to $4M ARR

**Next Steps:**
1. Validate product-market fit with pilot customers
2. Extract API layer (Q1 2026)
3. Raise seed funding ($500K)
4. Hire 2-3 key team members
5. Launch public beta with free tier

---

**Document Metadata:**
- **Version:** 1.0
- **Author:** Hupyy Temporal Team
- **Last Updated:** November 4, 2025
- **Status:** Living Document
- **Next Review:** December 1, 2025

**Related Documents:**
- [Prompt Engineering Analysis](PROMPT_ENGINEERING_ANALYSIS.md)
- [Prompt Conciseness Analysis](PROMPT_CONCISENESS_ANALYSIS.md)
- [Test Documentation](../RUN_TESTS.md)
- [Sprint Reports](sprints/)

---

*Generated for investor and stakeholder review. For technical implementation details, see individual module documentation.*
