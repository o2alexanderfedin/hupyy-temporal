PROJECT: HUPYY — The Verification Engine
 OBJECTIVE: Create a beautiful, ultra-clean UI/UX experience that feels like the love child of Apple Design, Salesforce UI, and a touch of 2000s Aqua nostalgia — yet entirely futuristic, 2026-level fresh.
HUPYY should feel like the first computer that proves truth, not guesses.
 Every detail should inspire calm confidence and technical integrity.
:art: CORE DESIGN LANGUAGE
Visual DNA: macOS Sonoma modernism + Salesforce Lightning polish + subtle Aqua nostalgia.
Rounded corners, glassy gradients, gentle shadows, dynamic clarity.
Typography: SF Pro / Inter / Helvetica Neue.
Layout grid: centered composition, breathing space, balanced whitespace.
Background: white → silver gradient with light vignette, Apple-glass subtlety.
Buttons: no skeuomorphism; sleek Salesforce-style 3D layering with smooth transitions.
General tone: Truth made tangible.
:compass: SCREEN FLOW
SCREEN 1 — Landing (“Ask and You Shall Receive”)
Header: HUPYY (bold black, center top, 2.5rem).
Subheader: “What are we proving today?” (#555 gray, medium weight).
Search input: rounded edges (40px radius), inner shadow, placeholder = “Ask and you shall receive.”
Small magnifying glass icon on right.
Border: 1px #D2D8DF.
Buttons (horizontal layout, centered):
Don’t Worry Be Huppy
Prove Me
Use Salesforce-style gradient blues (#0176D3 → #0192FF) with light elevation and hover brightness +8%.
Corners: 10px radius.
Hover: subtle glow and upward motion (2px lift).
Overall background: soft gradient (#F9FAFB → #EAECEE).
Micro reflections and shadows evoke “Mac meets cloud enterprise.”
Transition: Smooth fade + gentle scale-up to Screen 2.
SCREEN 2 — Processing (“Huppy, Huppy, Joy, Joy…“)
Keep same base layout.
Input now filled with: “Can we approve this $1M loan to John Smith?”
Buttons disabled (opacity 60%, inactive state).
Replace with animated text:
“Huppy, Huppy, Joy, Joy…” (pulsing soft blue, #2E95FF, repeating every 1.5s).
Add light blue halo glow around input to signal verification process.
Subtle shimmer animation across background — faint moving light band.
Duration: 2–3 seconds before auto-transition.
SCREEN 3 — Output (“Show Me The Proof”)
Center card: rounded rectangle, soft drop shadow (#00000015).
Query repeated on top line with green checkmark.
Large central verdict text: TRUE, FALSE, or UNKNOWN.
Typeface: SF Pro Display Bold.
TRUE → WhatsApp-style green but slightly darker (#128C7E).
FALSE → Deep red (#C62828).
UNKNOWN → Warm amber yellow (#FFC300).
Below: large rounded button with Salesforce-style gradient (#0176D3 → #0192FF).
Label: “SHOW ME THE PROOF ↓”
Hover: subtle gloss overlay, inner shadow fade-in, arrow slides 4px right.
Optional proof section: when expanded, reveals translucent logic panel with monospaced proof text (dark gray #333 on frosted white background).
Proof panel slides down smoothly (250ms ease-out).
:jigsaw: INTERACTION SPEC
Screen transitions: fade/cross-dissolve (300ms ease-in-out).
Buttons: responsive scaling + elevation (Salesforce Lightning interaction model).
Input focus: blue halo glow (#0176D3).
Proof dropdown: slide + fade.
All transitions feel “buttery smooth,” no harsh motion.
:rainbow: COLOR SYSTEM
Background gradient: #F9FAFB → #EAECEE.
Text primary: #111111.
Text secondary: #555555.
Input border: #C8D4E2.
Primary blue: #0176D3 → #0192FF (Salesforce Lightning Blue).
TRUE green: #128C7E.
FALSE red: #C62828.
UNKNOWN yellow: #FFC300.
Shadows: rgba(0,0,0,0.1) soft and elevated.
:brain: ANIMATION GUIDELINES
“Processing” pulsing text opacity: 0.5 → 1 → 0.5, 1.5s loop.
Proof panel drop: 250ms ease-in-out slide + fade.
Button hover: brightness +8%, glow intensity +4%.
Transition fade between screens: 300ms ease-in-out.
:toolbox: EXPORT DELIVERABLES
3 screens with full states (Idle, Loading, Verified).
Figma components with shared styles (buttons, inputs, results).
Color tokens, shadows, gradients mapped to Salesforce Lightning standards.
React/HTML/CSS exports with responsive layout specs.
Include interaction map showing flow between screens.
:sparkles: FINAL NOTE
The final look should merge:
The playful warmth of early Apple design,
The clarity and enterprise confidence of Salesforce,
And the aesthetic freshness of 2026 digital minimalism.
Buttons, shadows, and typography must lean slightly more Salesforce than Aqua, giving the product a “trusted enterprise-grade cloud” aesthetic while preserving the light, futuristic soul of HUPYY.
It should feel like truth made elegant — the UI of the world’s first computer that proves.