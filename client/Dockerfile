# Build Dockerfile for client static assets
# Outputs to /app/dist for deployment to CDN

FROM oven/bun:1.2-alpine AS build

WORKDIR /app

# Copy dependency files
COPY package.json bun.lock ./

# Install dependencies
RUN bun install --frozen-lockfile

# Copy source code
COPY . .

# Type check
RUN bun run typecheck

# Build for production
RUN bun run build

# =============================================================================
# Stage 2: Serve with nginx (optional, for self-hosted)
# =============================================================================
FROM nginx:alpine AS serve

COPY --from=build /app/dist /usr/share/nginx/html

# Custom nginx config for SPA routing
RUN echo 'server { \
    listen 80; \
    root /usr/share/nginx/html; \
    index index.html; \
    location / { \
        try_files $uri $uri/ /index.html; \
    } \
    location /assets { \
        expires 1y; \
        add_header Cache-Control "public, immutable"; \
    } \
}' > /etc/nginx/conf.d/default.conf

EXPOSE 80

CMD ["nginx", "-g", "daemon off;"]

# =============================================================================
# Stage 3: Export static files only (for CDN deployment)
# =============================================================================
FROM scratch AS static

COPY --from=build /app/dist /
