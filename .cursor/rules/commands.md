## User Commands

- "Refactor" - Hard, aggressive refactor which does not preserve backwards compatibility
- "Lore" - Add implementation summary to `lore` folder in Markdown format
  - Filename: `%Y%m%d-%H%M-lowercase-name.md`
- "Lore Context" (alias "Compact") - Summarize AI's current context window to lore
- "Test" means:
  - **Client**: `bun run typecheck`
  - **Server**: `cd server && mix test`
- "Assess" means:
  - Review recent changes holistically
  - Make a plan to refactor/cleanup
  - Write plan to Lore
- "Harden" means:
  - Do "Assess" command
  - Apply obvious improvements automatically
  - Ask before complex changes
  - Re-run tests after

## Development Commands

### Client
```bash
cd client
bun run dev           # Start Vite dev server (port 4100)
bun run build         # Production build
bun run typecheck     # TypeScript type check
```

### Server
```bash
cd server
source ~/.asdf/asdf.sh  # Load Elixir/Erlang
mix deps.get            # Install dependencies
mix phx.server          # Start Phoenix (port 4200)
mix test                # Run tests
iex -S mix phx.server   # Interactive mode
```

## Shell Execution
- WSL2/Linux environment -> Use Bash
- Always `source ~/.asdf/asdf.sh` before Elixir commands
