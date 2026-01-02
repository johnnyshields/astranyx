# Production Dockerfile for Phoenix server
# Multi-stage build for minimal image size

# =============================================================================
# Stage 1: Build
# =============================================================================
FROM elixir:1.19-otp-28-alpine AS build

WORKDIR /app

# Install build dependencies
RUN apk add --no-cache git build-base

# Install hex + rebar
RUN mix local.hex --force && \
    mix local.rebar --force

# Set build environment
ENV MIX_ENV=prod

# Copy dependency files
COPY mix.exs mix.lock ./

# Install and compile dependencies
RUN mix deps.get --only prod && \
    mix deps.compile

# Copy application code
COPY config config
COPY lib lib
COPY priv priv

# Compile application
RUN mix compile

# Build release
RUN mix release

# =============================================================================
# Stage 2: Runtime
# =============================================================================
FROM alpine:3.21 AS runtime

# Install runtime dependencies
RUN apk add --no-cache \
    libstdc++ \
    openssl \
    ncurses-libs \
    ca-certificates

WORKDIR /app

# Create non-root user
RUN addgroup -S astranyx && adduser -S astranyx -G astranyx
USER astranyx

# Copy release from build stage
COPY --from=build --chown=astranyx:astranyx /app/_build/prod/rel/astranyx ./

# Set runtime environment
ENV PHX_SERVER=true
ENV PHX_HOST=localhost
ENV PORT=4200

EXPOSE 4200

# Health check
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:4200/health || exit 1

CMD ["bin/astranyx", "start"]
