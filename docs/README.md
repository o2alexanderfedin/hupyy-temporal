# Documentation Directory

This directory contains all project documentation organized by category and version.

## 📁 Directory Structure

```
docs/
├── product-v2.0/          ⭐ Current product architecture (v2.0.0)
├── legacy/                📦 Older architecture versions
├── analysis/              📊 System analysis documents
├── investors/             💰 Investor materials
├── architecture/          📐 General architecture documents
├── research/              🔬 Research findings
├── proposals/             💡 Integration proposals
└── ui-ux/                 🎨 UI/UX designs
```

## 🎯 Quick Start

### For Developers
**Start here:** 📖 [product-v2.0/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md](./product-v2.0/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md)

This is the complete technical specification for the v2.0.0 multi-domain platform.

### For Product Managers
**Start here:** 📋 [product-v2.0/DOMAIN_INDEPENDENCE_ANALYSIS.md](./product-v2.0/DOMAIN_INDEPENDENCE_ANALYSIS.md)

Understand why we built v2.0 and what problems it solves.

### For Business/Investors
**Start here:** 📊 [ARCHITECTURE_FOR_INVESTORS.md](./ARCHITECTURE_FOR_INVESTORS.md)

High-level overview with business context and market opportunity.

## 📚 Main Documentation Sections

### 🚀 Product v2.0 (Current)

**Location:** `product-v2.0/`

The complete specification for the **multi-domain constraint solving platform**. Includes:

- ✅ Complete architecture specification (3,736 lines)
- ✅ Domain independence analysis
- ✅ Release notes v2.0.0
- ✅ Sprint 005 task documentation
- ✅ Migration guide from v1.0

**Key Features:**
- Multi-vertical platform (healthcare, finance, mechanical engineering, temporal logic)
- Domain Management Layer with plugin system
- Template-based LLM prompts
- RESTful domain-scoped API
- Complete isolation (database, vector DB, API)

**Status:** ✅ Specification Complete | 🔨 Implementation Pending

[→ Read Product v2.0 README](./product-v2.0/README.md)

---

### 📦 Legacy Architecture

**Location:** `legacy/`

Previous architecture versions (v1.0.x) - single-domain mechanical engineering system.

**Contents:**
- `ARCHITECTURE.md` - Original v1.0 specification
- Backup files

**Status:** 📚 Archived | ⚠️ Deprecated

---

### 📊 Analysis Documents

**Location:** `analysis/`

System analysis, performance studies, and technical deep-dives.

**Contents:**
- `PROMPT_ENGINEERING_ANALYSIS.md` - LLM prompt optimization study
- `TECHNICAL_DEBT_ANALYSIS.md` - Technical debt assessment
- `PROMPT_CONCISENESS_ANALYSIS.md` - Prompt efficiency analysis

**Use Cases:**
- Understanding system tradeoffs
- Performance optimization research
- Technical decision rationale

---

### 💰 Investor Materials

**Location:** `investors/`

Business-focused documentation and investor research.

**Contents:**
- Investor profiles (Heavybit, Hetz Ventures, NFX)
- Pitch preparation materials
- Market analysis

**Also See:**
- `ARCHITECTURE_FOR_INVESTORS.md` (root docs/)
- `ARCHITECTURE_FOR_INVESTORS.pdf` (root docs/)

---

### 📐 Architecture

**Location:** `architecture/`

General architecture patterns and design decisions.

**Contents:**
- `extending-to-multiple-theories.md` - Multi-theory SMT-LIB support

---

### 🔬 Research

**Location:** `research/`

External resource investigations and research findings.

**Contents:**
- `medical-databases-api-access.md` - Public medical database APIs

---

### 💡 Proposals

**Location:** `proposals/`

Integration approaches and discussion documents.

**Contents:**
- Medical database integration proposals
- Demo planning documents

---

### 🎨 UI/UX

**Location:** `ui-ux/`

User interface designs and user experience documentation.

---

## 🗺️ Navigation Guide

| I want to... | Go to... |
|--------------|----------|
| **Understand the current system** | [product-v2.0/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md](./product-v2.0/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md) |
| **Learn about v2.0 features** | [product-v2.0/RELEASE-NOTES-v2.0.0.md](./product-v2.0/RELEASE-NOTES-v2.0.0.md) |
| **Migrate from v1.0 to v2.0** | [product-v2.0/RELEASE-NOTES-v2.0.0.md#migration-guide](./product-v2.0/RELEASE-NOTES-v2.0.0.md#migration-guide) |
| **See what changed from v1.0** | [product-v2.0/DOMAIN_INDEPENDENCE_ANALYSIS.md](./product-v2.0/DOMAIN_INDEPENDENCE_ANALYSIS.md) |
| **Review sprint tasks** | [product-v2.0/sprint-005-domain-independence-specification/](./product-v2.0/sprint-005-domain-independence-specification/) |
| **Understand v1.0 (legacy)** | [legacy/ARCHITECTURE.md](./legacy/ARCHITECTURE.md) |
| **Read analysis documents** | [analysis/](./analysis/) |
| **Prepare investor pitch** | [ARCHITECTURE_FOR_INVESTORS.md](./ARCHITECTURE_FOR_INVESTORS.md) |

## 📈 Version History

| Version | Status | Documentation | Date |
|---------|--------|---------------|------|
| **v2.0.0** | ✅ Current | [product-v2.0/](./product-v2.0/) | Jan 2025 |
| v1.x | ⚠️ Deprecated | [legacy/](./legacy/) | 2024 |

## 🔧 Contributing

When adding new documentation:

1. **Product specifications** → `product-v2.0/` (or create `product-v3.0/` for major versions)
2. **Analysis documents** → `analysis/`
3. **Legacy/archived docs** → `legacy/`
4. **Investor materials** → `investors/`

## 📝 Documentation Standards

- Use Markdown (.md) format
- Include table of contents for documents > 200 lines
- Add Mermaid diagrams for architecture/flows
- Reference source code with file:line format
- Link to related documents with relative paths

## 🆘 Help

- **Questions about v2.0?** See [product-v2.0/README.md](./product-v2.0/README.md)
- **Can't find something?** Check the navigation guide above
- **Found an error?** Open an issue on GitHub

---

**Last Updated:** January 5, 2025
**Current Version:** v2.0.0
**Status:** 📖 Specification Phase
