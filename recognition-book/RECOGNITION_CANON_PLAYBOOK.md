## Recognition Canon Playbook (v1)

**Target manuscript:** `book/docs/Recognition-book.tex`  
**Purpose of this document:** One unified, operational plan for structure, voice, trust, and editing workflow.

**This playbook synthesizes:**
- **House style:** `book/docs/THEORY_OF_US_STYLE_CONSTITUTION.md`
- **Scripture mode:** `book/docs/SCRIPTURE_MODE_EDITORIAL_PROMPT.md`
- **Beauty pass:** `book/docs/BEAUTY_POETRY_PROMPT.md`

If guidance conflicts between documents, follow this playbook.

---

## Mission (non negotiable)

This book should be encountered like scripture: revelatory, authoritative, uncanny clear, and rereadable for life.

Assume the science is culturally accepted. Do not argue for it. Do not sell it. Do not defend it. Name what is true, define the mechanism, show what follows.

This is not a field guide. This is a canon.

---

## Reader contract

- **Target reader:** a curious, intelligent high school senior can follow the main narrative without prior physics or math.
- **Dual audience:** the main flow stays plain. Formalism is optional and clearly marked.
- **Momentum:** no “manual mode” for more than about two pages at a time.
- **Trust:** the reader always knows what is **Derived**, **Measured**, **Predicted**, or **Speculative**.
- **Timelessness:** minimize trendy references. Prefer durable images and durable language.

---

## Book level architecture (current order and why)

The book is a single arc with six movements. The order is deliberate: recognition first, mechanism second, consequences thereafter.

- **Part I: The Language (Logos)**: hook fast. Start where the reader already lives: meaning, feeling, connection.
- **Part II: The Architecture (Genesis)**: reveal the machine beneath the signal so the signal cannot be mistaken for metaphor.
- **Part III: The Moral Architecture (Deuteronomy)**: ethics as conservation, not preference.
- **Part IV: The Soul**: identity, threshold, death, persistence, choice.
- **Part V: The Healing**: repair as physics with boundaries and tests.
- **Part VI: The Future**: AI, living inside the knowledge, and appendices.

Rule: each part must end with a clear bridge that makes the next part feel inevitable.

---

## Canonical stack inside chapters (Pillars, Tables, Bridges)

Prefer a canonical stack when introducing new material:

- **Pillars:** name the novel Recognition primitives first (what the world is in this framework).
- **Tables:** collect invariants, constants, and equations in tables or end matter so the main text stays timeless.
- **Bridges:** treat classical science as channels and projections, not as the foundation being argued against.

Special: octaves, resonance, and “universe as music” must be treated as literal architecture, not vibe.

---

## Layering rule (keep it accessible without shrinking the claims)

Use three layers consistently:

- **Layer 1, main narrative:** plain English claim → one human anchor image → “what changed” → bridge forward.
- **Layer 2, optional deep dive:** put math and derivations in `mathinsert` boxes.
- **Layer 3, boundaries and safety:** put objections, limits, and anti abuse guidance in `bigquestion` boxes.

If a section becomes list heavy or technical, move the catalog into a box or appendix table and keep the main flow as a guided tour.

---

## Terminology strategy (make new names land)

The reader should not have to memorize new terms to keep reading. Use a naming ladder.

### The 3 layer naming ladder

When a construct first appears, present it in three faces:

- **Plain phrase:** what it does in ordinary words.
- **Named mechanism:** the capitalized Recognition name.
- **Formal label:** symbol or technical term, only when needed.

Example pattern:
- **Reality keeps books** (the Ledger), with a minimal tick \((\tau)\) and a mismatch price \Jcost.

### Term placement rules

- **First use:** Plain phrase first. Then the name in parentheses. Symbol last.
- **Second use:** Use the name confidently. Only re show the plain phrase when needed for clarity.
- **Later:** Prefer the name alone. Do not re define unless the chapter changes the meaning.

### Definition discipline

- **One meaning per name:** a term should not drift across chapters.
- **No synonym clutter:** pick one primary word and one backup synonym maximum.
- **Avoid abstraction stacking:** if a sentence introduces more than two new named things, split it.

---

## Trust labels (Derived, Measured, Predicted, Speculative)

Use explicit trust labels when a reader might wonder “is this proof or belief.”

- **Derived:** forced by constraints already stated.
- **Measured:** calibrated from observation or unit fixing.
- **Predicted:** falsifiable forward claim.
- **Speculative:** flagged as such, with the reason it is included.

Rule: trust labels are not apologetic. They are structure. One clean line is enough.

---

## Voice rules (scripture mode, house style)

- **Default voice:** declarative discovery language. “Time is counting.” “Meaning is structure.”
- **Tone:** calm, luminous, confident but humble. No hype.
- **No debate posture:** remove courtroom energy and strawmen.
- **No manual language:** avoid recipe, how to, instruction set, tomorrow morning framing.
- **Paragraphs as breath units:** keep them short by default. Use a long paragraph only for deliberate current.
- **Read aloud rule:** if a sentence makes you stumble, it is not finished.
- **Filler purge:** delete “just,” “really,” “very,” “quite,” “actually” unless they change meaning.
- **House bans:** no em dashes and no double dashes in book prose.

---

## Beauty beats (poetry without new claims)

Beauty is polish, not camouflage. Add controlled “high point” passages only where they serve the argument.

### Where beauty beats belong

- Chapter openings.
- After a major derivation or definition.
- Before and after catalogs.
- Part bridges.
- Chapter endings and seals.

### Beauty beat constraints

- **Length:** 4 to 10 lines.
- **Imagery:** one concrete image maximum.
- **Diction:** plain words, concrete nouns, active verbs. Minimal adjectives.
- **Cadence:** one flowing sentence is allowed. End on a strong word.
- **No new claims:** do not add constants, derivations, or empirical assertions.
- **No fabricated quotes:** if a precise quote is desired, insert `[QUOTE TBD - user will supply exact text + source]`.

---

## Chapter template (default, not rigid)

Every chapter should usually do the following:

- **Hook:** a scene, puzzle, or bold testable claim.
- **Promise:** 1 to 3 sentences naming what will be built.
- **Deliver:** guided steps, frequent “what changed” micro summaries, minimal new nouns per paragraph.
- **Seal:** 3 to 7 lines, engraving style. Not summary, not pep talk.
- **Bridge:** a forward lean that makes the next chapter feel required.

For dense chapters, add a short `\section*{Reader-map}` early.

---

## Editing workflow (one section at a time, deeply)

Work in small contiguous chunks, usually 150 to 400 lines or up to about 5,000 words.

- **Diagnose (private):** where it argues, repeats, turns manual, loses the reader, or blurs trust.
- **Edit in place:** convert argument posture to naming and consequence. Compress repetition. Improve rhythm.
- **Protect momentum:** move formalism into `mathinsert` and boundaries into `bigquestion`.
- **Seal:** rewrite the ending so it closes like canon.
- **Integrity checks:** no new notation unless necessary; compile safe; trust clarity preserved.

---

## LaTeX constraints (do not break the build)

- Do not introduce new packages unless strictly required.
- Keep labels, refs, environments, and custom commands intact.
- Prefer moving math into `mathinsert` rather than adding inline symbol density.
- Use `bigquestion` for safety and boundary sections, especially in Healing.

---

## Current high ROI strategy (where improvement tends to come from)

- **Reduce defensive repetition:** explain once, then speak with authority.
- **Convert catalogs to guided tours:** keep tables in appendices.
- **Strengthen bridges:** every section should end by making the next section necessary.
- **Enforce the naming ladder:** plain phrase → name → symbol.
- **Use trust labels strategically:** especially in Soul, Healing, Validation, and Anomalies.


