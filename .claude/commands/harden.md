---
description: Assess and auto-refactor if confident, then re-run tests (project)
---

Steps:
1. Before starting -> If there are uncommitted git changes, ask if I would like to commit
2. Do the Assess command: Review the recent changes in the thread holistically and make a refactor/cleanup plan:
  - Consolidate code
  - Fix implementation inconsistencies
  - Fix anything hacky/bloated/redundant
  - DRY up code / extract out a common component (do NOT go overboard)
  - Remove dead/unused/obsolete code
  - Add missing test coverage
  - Think deeper about architectural improvements, not just surface-level fixes
  - (BUT do NOT go overboard here; do not make performative suggestions)

3. Write the plan to the lore folder (filename: "%Y%m%d-%H%M-lowercase-name.md" format with leading zeros)
   Include an **Effort/Impact Assessment Table** (summary) with ALL identified opportunities:

   | # | Opportunity | Effort | Impact | Recommendation |
   |---|-------------|--------|--------|----------------|
   | 1 | Description | Quick/Low/Medium/High | Low/Medium/High | Auto-fix / Ask first / Skip |

   **Effort categories:**
   - **Quick**: <5 min, mechanical change, zero risk. This includes:
     - Code duplication (same logic in multiple places) → consolidate into single source of truth
     - Inconsistent naming (same concept with different names) → pick one name, use everywhere
     - Unused methods/constants → remove
     - Dead code paths → remove
   - **Easy**: 5-15 min, straightforward, minimal risk
   - **Moderate**: 15-60 min, requires some thought, some risk
   - **Hard**: 1+ hours, architectural change, higher risk

   **Impact categories:**
   - **High**: Fixes bugs, improves performance, significantly improves maintainability
   - **Medium**: Improves readability, reduces duplication, better patterns
   - **Low**: Minor cleanup, stylistic improvement

   Sort the table by effort (quick first, then easy, moderate, hard).
   Number each opportunity so the user can refer to them (e.g., "do #3 and #5").

   **Below the summary table**, include a "Opportunity Details" section with each numbered item explained:
   - **What**: Functional description of the change
   - **Where**: Files/classes/methods that would be touched
   - **Why**: The value it provides (maintainability, performance, DX, etc.)
   - **Trade-offs**: Any downsides or risks (if applicable)

4. **Interactive execution:**
   a. Create a **TodoWrite** task list with ALL identified opportunities
   b. For each opportunity (in order by effort), use the **AskUserQuestion tool** to prompt:
      - Header: opportunity number + [difficulty] (e.g., "#3 [Easy]")
      - Question: opportunity title + brief What/Where/Why summary
      - Options:
        1. "Implement" - proceed with the change
        2. "Skip (add to TODO.md)" - skip for now, add to TODO.md for future
        3. "Do not implement" - skip permanently
      - Ask about quick items (if any) first, do those, then ask about the others.
   c. Based on response: implement, add to TODO.md, or remove from task list.

5. After completing refactors -> re-run tests:
   ```bash
   cd client && bun run typecheck
   cd server && mix test
   ```
