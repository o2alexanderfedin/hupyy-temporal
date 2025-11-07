# Legacy Documentation

This directory contains archived documentation from previous versions of the system.

## ⚠️ Important Notice

**These documents are for historical reference only.**

- ❌ Do not use for current development
- ❌ May contain outdated information
- ✅ Useful for understanding system evolution
- ✅ Reference for migration decisions

## 📁 Directory Structure

```
legacy/
├── ARCHITECTURE.md              v1.0 architecture specification
├── ARCHITECTURE.md.backup       Backup of v1.0 architecture
├── demos/                       Sprint 003 demo and styling docs
│   ├── DEMO_ARCHITECTURE.md
│   ├── DEMO_STYLING_SUMMARY.txt
│   ├── STYLING_EXPLORATION_INDEX.md
│   ├── STYLING_INTEGRATION_GUIDE.md
│   └── SPRINT_003_STYLING_README.md
└── implementation/              Historical implementation notes
    └── IMPLEMENTATION_SUMMARY.md
```

## 📚 What's Here

### Architecture (v1.0.x)

**Files:**
- `ARCHITECTURE.md` - Original single-domain architecture
- `ARCHITECTURE.md.backup` - Backup copy

**Status:** ⚠️ Deprecated by v2.0.0

**Contents:**
- Mechanical engineering focused design
- Hardcoded entity types (Material, Beam, Environment)
- Single-domain constraint system

**Replaced By:**
- [Product v2.0 Architecture](../product-v2.0/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md)

---

### Demo & Styling Documents (Sprint 003)

**Directory:** `demos/`

**Status:** 📦 Archived - Sprint 003 deliverables

**Contents:**
- Demo application architecture
- Styling system exploration and decisions
- Sprint 003 UI/UX redesign documentation

**Historical Context:**
These documents capture the UI/UX redesign work from Sprint 003. While the styling implementations may still be in use, the documentation here represents the exploration and decision-making process.

**Files:**
- `DEMO_ARCHITECTURE.md` - Demo app structure
- `DEMO_STYLING_SUMMARY.txt` - Styling decisions summary
- `STYLING_EXPLORATION_INDEX.md` - Styling options explored
- `STYLING_INTEGRATION_GUIDE.md` - Integration guide
- `SPRINT_003_STYLING_README.md` - Sprint 003 overview

---

### Implementation Summaries

**Directory:** `implementation/`

**Status:** 📚 Historical notes

**Contents:**
- `IMPLEMENTATION_SUMMARY.md` - Historical implementation notes

---

## 🔍 When to Reference Legacy Docs

### ✅ Good Reasons

- **Understanding evolution:** "Why did we make this design decision?"
- **Migration planning:** "What changed from v1.0 to v2.0?"
- **Historical context:** "How did the styling system evolve?"
- **Learning:** "What approaches were tried and abandoned?"

### ❌ Bad Reasons

- **Current development:** Use [Product v2.0 docs](../product-v2.0/) instead
- **API integration:** Legacy APIs are deprecated
- **Architecture reference:** v2.0 has significant breaking changes

## 📖 Current Documentation

For up-to-date documentation, see:

| Purpose | Location |
|---------|----------|
| **Current Architecture** | [docs/product-v2.0/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md](../product-v2.0/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md) |
| **Migration Guide** | [docs/product-v2.0/RELEASE-NOTES-v2.0.0.md](../product-v2.0/RELEASE-NOTES-v2.0.0.md) |
| **Sprint History** | [sprints/README.md](../../sprints/README.md) |
| **Analysis Documents** | [docs/analysis/](../analysis/) |

## 📊 Version History

| Version | Status | Architecture | Notes |
|---------|--------|--------------|-------|
| **v1.0.x** | ⚠️ Deprecated | `ARCHITECTURE.md` | Single-domain mechanical engineering |
| **v2.0.0** | ✅ Current | [Product v2.0](../product-v2.0/) | Multi-domain platform |

## 🔗 Related Resources

- **What changed:** [Domain Independence Analysis](../product-v2.0/DOMAIN_INDEPENDENCE_ANALYSIS.md)
- **Breaking changes:** [Release Notes v2.0.0](../product-v2.0/RELEASE-NOTES-v2.0.0.md#breaking-changes)
- **New features:** [v2.0 README](../product-v2.0/README.md)

---

**Archived:** January 5, 2025
**Superseded By:** v2.0.0
**Current Version:** [Product v2.0](../product-v2.0/)
