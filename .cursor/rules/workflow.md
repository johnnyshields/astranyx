## Workflow

- After implementing a major feature fully, consider it a "Milestone". At each milestone:
    1. Write "Lore" automatically (see command below)
    2. Ask if I would like to "Harden" (see command below)
    3. Ask if I would like to run tests

## Testing Rules

### Client (TypeScript)
- Type check with `bun run typecheck`
- Future: Add Vitest for unit tests

### Server (Elixir)
- Run tests with `mix test`
- Future: Add ExUnit tests for channels

## Documentation
- Implementation summaries: Save to `/lore` folder (see "Lore" command)
- Filename format: `YYYYMMDD-HHMM-lowercase-name.md`

## Code Style

### TypeScript
- Strict mode enabled
- Explicit types for function parameters
- No `any` types
- Use `const` over `let`

### Elixir
- Follow standard Elixir style
- Use pattern matching
- Prefer pipe operator
- Keep functions small and focused

## Determinism Rules (CRITICAL for Simulation)

The game simulation must be 100% deterministic for P2P lockstep to work:

1. **No Math.random()** - Use `SeededRandom` class
2. **No Date.now()** - Use frame counter
3. **Fixed-point math** - Avoid floating point accumulation errors
4. **Consistent iteration** - Use arrays, not objects/maps for entities
5. **No async** - Simulation must be synchronous
