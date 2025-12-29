---
description: Fix linting issues and warnings, then re-run tests (project)
---

Run linters:

## Client (TypeScript)
```bash
cd client && bun run typecheck
```

## Server (Elixir)
```bash
cd server && source ~/.asdf/asdf.sh && mix format
```

Fix all issues and all warnings in the output (do not suppress them).

Ignore any line-ending (CR-LF) warnings; these are just because we are using a Windows filesystem locally, but Git will handle them when we commit.

After linting is complete, re-run tests if there have been significant changes.
