---
description: Run tests and fix all issues/warnings (project)
---

Run tests for both client and server:

## Client (TypeScript)
```bash
cd client && bun run typecheck
```

## Server (Elixir)
```bash
cd server && mix test
```

Fix all issues and warnings in the output (do not suppress them).
