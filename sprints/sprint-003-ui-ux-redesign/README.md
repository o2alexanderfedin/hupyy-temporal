# Sprint 003: UI/UX Redesign - HUPYY Visual Transformation

**Sprint Goal:** Transform the Hupyy Temporal UI to match the HUPYY design specification combining macOS Sonoma modernism, Salesforce Lightning polish, and subtle Aqua nostalgia.

**Duration:** 7-10 days
**Priority:** High
**Type:** User Experience & Visual Design

## Overview

This sprint reimagines the Hupyy Temporal UI following the comprehensive design specification in `docs/ui-ux/ui-ux-spec.md`. The goal is to create a beautiful, ultra-clean experience that feels like "the first computer that proves truth, not guesses" with calm confidence and technical integrity.

## Design Philosophy

From `docs/ui-ux/ui-ux-spec.md` (lines 1-4):
> "Create a beautiful, ultra-clean UI/UX experience that feels like the love child of Apple Design, Salesforce UI, and a touch of 2000s Aqua nostalgia — yet entirely futuristic, 2026-level fresh."

### Core Visual DNA (lines 5-12):
- **macOS Sonoma modernism** + **Salesforce Lightning polish** + **subtle Aqua nostalgia**
- Rounded corners, glassy gradients, gentle shadows, dynamic clarity
- Typography: SF Pro / Inter / Helvetica Neue
- Background: white → silver gradient with light vignette
- Buttons: sleek Salesforce-style 3D layering with smooth transitions

## Scope

### In Scope
- Custom CSS infrastructure for Streamlit
- Typography and color system implementation
- Button component redesign (Salesforce-style gradients)
- Input/form component styling (40px rounded corners, inner shadow)
- Result card component (soft drop shadow, centered layout)
- Background gradients and elevation system
- Animation and transition system
- Responsive layout with centered composition
- All pages: Main, Custom Problem, Benchmark

### Out of Scope
- Screen 1 ("Landing/Ask and You Shall Receive") - future sprint
- Screen 2 ("Processing/Huppy, Huppy, Joy, Joy") - future sprint
- Mobile/responsive breakpoints (focus on desktop first)
- Dark mode (future consideration)
- Performance optimization of animations

## Tasks Summary

| Task | Description | Story Points | Status |
|------|-------------|--------------|--------|
| TASK-001 | Setup custom CSS infrastructure | 3 | Not Started |
| TASK-002 | Implement typography and color system | 3 | Not Started |
| TASK-003 | Implement Salesforce-style button components | 5 | Not Started |
| TASK-004 | Implement input and form styling | 4 | Not Started |
| TASK-005 | Implement result card component | 5 | Not Started |
| TASK-006 | Implement background gradients and shadows | 3 | Not Started |
| TASK-007 | Implement animations and transitions | 4 | Not Started |
| TASK-008 | Update page layouts for centered composition | 5 | Not Started |
| **TOTAL** | | **32** | |

## Success Metrics

### Visual Quality
- [ ] Buttons match Salesforce Lightning gradient (#0176D3 → #0192FF) per `generated_image_november_03__2025_-_9_14pm_720.png`
- [ ] Input fields have 40px rounded corners and inner shadow per `screen2.png`
- [ ] Result cards match white card with soft shadow per `screen_3.png` and `screen_3_720.png`
- [ ] Background gradient matches spec (#F9FAFB → #EAECEE)
- [ ] Typography uses SF Pro/Inter/Helvetica Neue hierarchy

### Interaction Quality
- [ ] Button hover effects: brightness +8%, glow +4%, 2px lift
- [ ] Transitions are "buttery smooth" at 300ms ease-in-out
- [ ] Input focus shows blue halo glow (#0176D3)
- [ ] All animations follow timing specs (lines 67-71)

### Consistency
- [ ] All pages use same design system
- [ ] Color tokens match spec (lines 57-66)
- [ ] Shadows use consistent elevation system
- [ ] Typography hierarchy consistent across app

## Technical Approach

### Streamlit Custom Styling
Since Streamlit doesn't natively support advanced CSS customization, we'll use:
1. **`st.markdown()` with unsafe HTML**: Inject `<style>` tags
2. **CSS classes via `st.container()`**: Apply custom classes to sections
3. **Custom components**: For complex interactions (if needed)

### CSS Architecture
```
static/
└── css/
    ├── main.css              # Main stylesheet
    ├── colors.css            # Color tokens from spec
    ├── typography.css        # SF Pro/Inter fonts
    ├── buttons.css           # Salesforce-style buttons
    ├── inputs.css            # Form components
    ├── cards.css             # Result cards
    ├── animations.css        # Transitions and effects
    └── backgrounds.css       # Gradients and shadows
```

### Design Tokens
All design tokens extracted from `docs/ui-ux/ui-ux-spec.md`:

**Colors** (lines 57-66):
```css
--bg-gradient-start: #F9FAFB;
--bg-gradient-end: #EAECEE;
--text-primary: #111111;
--text-secondary: #555555;
--border-input: #C8D4E2;
--primary-blue-start: #0176D3;
--primary-blue-end: #0192FF;
--status-true: #128C7E;
--status-false: #C62828;
--status-unknown: #FFC300;
--shadow-soft: rgba(0,0,0,0.1);
```

**Spacing & Borders**:
- Input border radius: 40px (line 17)
- Button border radius: 10px (line 24)
- Button border radius (result): Per `screen_3.png`

**Typography**:
- Header: 2.5rem bold (line 15)
- Font family: SF Pro, Inter, Helvetica Neue (line 8)

## Dependencies

### Prerequisites
- Playwright MCP server installed ✅
- Streamlit application running ✅
- `docs/ui-ux/ui-ux-spec.md` reviewed
- Design mockups reviewed:
  - `docs/ui-ux/screen2.png` (Processing state)
  - `docs/ui-ux/screen_3.png` (Result card - full res)
  - `docs/ui-ux/screen_3_720.png` (Result card - 720p)
  - `docs/ui-ux/generated_image_november_03__2025_-_9_14pm_720.png` (Button library)

### External Dependencies
- Web fonts (SF Pro/Inter) via CDN or local
- Browser support for CSS gradients, shadows, transitions

## Implementation Strategy

### Phase 1: Foundation (Days 1-3)
1. **TASK-001**: Setup CSS infrastructure
2. **TASK-002**: Implement color system and typography
3. **TASK-003**: Implement button components

### Phase 2: Components (Days 4-6)
4. **TASK-004**: Implement input/form styling
5. **TASK-005**: Implement result card component
6. **TASK-006**: Implement backgrounds and shadows

### Phase 3: Polish (Days 7-10)
7. **TASK-007**: Implement animations and transitions
8. **TASK-008**: Update page layouts

Each task MUST:
1. **Start with Playwright inspection** of current UI state
2. **Reference specific sections** from `docs/ui-ux/ui-ux-spec.md`
3. **Reference specific images** from `docs/ui-ux/`
4. **Implement changes** using custom CSS
5. **Verify with Playwright** that changes match design

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Streamlit CSS limitations | Medium | High | Use unsafe HTML injection, custom components |
| Font loading issues | Low | Medium | Host fonts locally, provide fallbacks |
| Animation performance | Low | Medium | Use CSS transforms, avoid layout thrashing |
| Cross-browser inconsistencies | Medium | Low | Test in Chromium (primary target) |
| Design spec ambiguity | Low | Medium | Use Playwright to capture screenshots for review |

## Verification Process

Each task must include:
1. **Before screenshot** (using Playwright MCP)
2. **Implementation** with clear CSS
3. **After screenshot** (using Playwright MCP)
4. **Side-by-side comparison** with design mockups

Example verification command:
```python
# Via Playwright MCP
mcp__playwright__browser_take_screenshot(
    filename="before_task_003_buttons.png"
)
```

## References

### Design Specification
- **Main spec**: `docs/ui-ux/ui-ux-spec.md`
- **Screen 2 (Processing)**: `docs/ui-ux/screen2.png`
- **Screen 3 (Result - full)**: `docs/ui-ux/screen_3.png`
- **Screen 3 (Result - 720p)**: `docs/ui-ux/screen_3_720.png`
- **Button Library**: `docs/ui-ux/generated_image_november_03__2025_-_9_14pm_720.png`

### Technical Resources
- [Streamlit Custom Components](https://docs.streamlit.io/develop/concepts/custom-components)
- [Streamlit Theming](https://docs.streamlit.io/develop/concepts/configuration/theming)
- [CSS Gradient Generator](https://cssgradient.io/)
- [Salesforce Lightning Design System](https://www.lightningdesignsystem.com/)

## Notes

- **DO NOT copy-paste** from design spec - reference sections by line numbers
- **USE Playwright MCP** to inspect actual UI before and after changes
- All changes must be committed following git flow
- Each task creates a feature branch: `feature/sprint-003-task-XXX`
- Visual regression testing recommended (future sprint)

## Definition of Done

- [ ] All 8 tasks completed
- [ ] UI matches design specification per Playwright screenshots
- [ ] All pages (Main, Custom Problem, Benchmark) updated
- [ ] CSS organized in modular files
- [ ] Design tokens documented
- [ ] Before/after screenshots captured
- [ ] Code committed and pushed
- [ ] Sprint retrospective completed
- [ ] v0.4.0 release tagged
