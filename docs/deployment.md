# Astranyx Deployment Guide

This guide covers deploying Astranyx to production.

## Security Model

TURN credentials are **ephemeral** and only provided when a game starts:
- Credentials are generated server-side using HMAC-SHA1
- Shared secret between Phoenix and Coturn (never exposed to clients)
- Credentials expire after 1 hour (configurable via `TURN_TTL`)
- Credentials are tied to room ID and timestamp
- No public endpoint to request credentials
- **Auto-refresh**: Client automatically refreshes credentials every 45 minutes for long games
- Refresh endpoint only available to players already in a room

## Architecture Overview

```
                    ┌─────────────────┐
                    │   Load Balancer │
                    │  (nginx/caddy)  │
                    └────────┬────────┘
                             │
           ┌─────────────────┼─────────────────┐
           │                 │                 │
           ▼                 ▼                 ▼
    ┌─────────────┐   ┌─────────────┐   ┌─────────────┐
    │   Client    │   │   Phoenix   │   │   Coturn    │
    │   (Static)  │   │   Server    │   │   (TURN)    │
    │   :443      │   │   :4200     │   │   :3478     │
    └─────────────┘   └─────────────┘   └─────────────┘
```

## Components

| Component | Purpose | Port(s) |
|-----------|---------|---------|
| Client (Vite build) | Static game files | 443 (via reverse proxy) |
| Phoenix Server | Lobby, matchmaking, signaling | 4200 |
| Coturn | TURN/STUN for WebRTC NAT traversal | 3478, 5349, 49152-65535 |

---

## 1. Client Deployment

### Build

```bash
cd client
bun install
bun run build
```

Output is in `client/dist/`.

### Environment Variables

Create `.env.production` before building:

```bash
# Phoenix server WebSocket URL
VITE_SERVER_URL=wss://your-domain.com/socket
```

Note: TURN credentials are **not** configured on the client. They are securely
provided by the Phoenix server when a game starts (ephemeral credentials).

### Hosting Options

**Static hosting (recommended):**
- Cloudflare Pages
- Vercel
- Netlify
- AWS S3 + CloudFront

**Self-hosted:**
- nginx serving `dist/` folder
- Caddy with automatic HTTPS

---

## 2. Phoenix Server Deployment

### Prerequisites

- Erlang/OTP 28+
- Elixir 1.19+

### Build Release

```bash
cd server

# Set environment
export MIX_ENV=prod
export SECRET_KEY_BASE=$(mix phx.gen.secret)

# Build
mix deps.get --only prod
mix compile
mix release
```

### Environment Variables

```bash
# Required
SECRET_KEY_BASE=<64-char-secret>    # mix phx.gen.secret
PHX_HOST=your-domain.com
PORT=4200

# TURN server (required for WebRTC)
TURN_SECRET=YOUR_SHARED_SECRET_HERE  # Must match Coturn static-auth-secret
TURN_URLS=turn:your-domain.com:3478,turn:your-domain.com:3478?transport=tcp

# Optional
PHX_SERVER=true                      # Enable server in release
DATABASE_URL=...                     # If using database
```

### Running

```bash
# Direct
_build/prod/rel/astranyx/bin/astranyx start

# Or with systemd (see below)
```

### Systemd Service

Create `/etc/systemd/system/astranyx.service`:

```ini
[Unit]
Description=Astranyx Game Server
After=network.target

[Service]
Type=simple
User=astranyx
Group=astranyx
WorkingDirectory=/opt/astranyx/server
Environment=MIX_ENV=prod
Environment=SECRET_KEY_BASE=your-secret-key
Environment=PHX_HOST=your-domain.com
Environment=PORT=4200
ExecStart=/opt/astranyx/server/_build/prod/rel/astranyx/bin/astranyx start
ExecStop=/opt/astranyx/server/_build/prod/rel/astranyx/bin/astranyx stop
Restart=on-failure
RestartSec=5

[Install]
WantedBy=multi-user.target
```

```bash
sudo systemctl enable astranyx
sudo systemctl start astranyx
```

---

## 3. Coturn (TURN Server) Deployment

TURN is required for WebRTC when players are behind symmetric NAT.

### Option A: Docker (Recommended)

**Important:** Use `use-auth-secret` instead of `user=` for ephemeral credentials.

```bash
docker run -d \
  --name coturn \
  --network=host \
  --restart=unless-stopped \
  coturn/coturn \
  -n \
  --log-file=stdout \
  --listening-port=3478 \
  --tls-listening-port=5349 \
  --min-port=49152 \
  --max-port=65535 \
  --realm=your-domain.com \
  --server-name=your-domain.com \
  --use-auth-secret \
  --static-auth-secret=YOUR_SHARED_SECRET_HERE \
  --fingerprint \
  --no-cli
```

The `static-auth-secret` must match `TURN_SECRET` in Phoenix.

### Option B: Native Install

**Ubuntu/Debian:**

```bash
sudo apt update
sudo apt install coturn
```

Edit `/etc/turnserver.conf`:

```ini
# Network
listening-port=3478
tls-listening-port=5349
min-port=49152
max-port=65535

# Server identification
realm=your-domain.com
server-name=your-domain.com

# Authentication - use shared secret for ephemeral credentials
use-auth-secret
static-auth-secret=YOUR_SHARED_SECRET_HERE

# Security
fingerprint
no-cli

# Logging
log-file=/var/log/turnserver.log

# TLS (optional but recommended)
# cert=/etc/letsencrypt/live/your-domain.com/fullchain.pem
# pkey=/etc/letsencrypt/live/your-domain.com/privkey.pem
```

**Important:** The `static-auth-secret` must match `TURN_SECRET` in Phoenix.

Enable and start:

```bash
# Edit /etc/default/coturn, set TURNSERVER_ENABLED=1
sudo systemctl enable coturn
sudo systemctl start coturn
```

### Firewall Rules

Open these ports:

| Port | Protocol | Purpose |
|------|----------|---------|
| 3478 | TCP/UDP | STUN/TURN |
| 5349 | TCP/UDP | STUN/TURN over TLS |
| 49152-65535 | UDP | TURN relay ports |

```bash
# UFW example
sudo ufw allow 3478/tcp
sudo ufw allow 3478/udp
sudo ufw allow 5349/tcp
sudo ufw allow 5349/udp
sudo ufw allow 49152:65535/udp
```

### Testing TURN Server

Use [Trickle ICE](https://webrtc.github.io/samples/src/content/peerconnection/trickle-ice/):

1. Add your TURN server: `turn:your-domain.com:3478`
2. Enter username and password
3. Click "Gather candidates"
4. You should see `relay` candidates if TURN is working

---

## 4. Reverse Proxy (nginx)

Example nginx config for all services:

```nginx
# /etc/nginx/sites-available/astranyx

# Redirect HTTP to HTTPS
server {
    listen 80;
    server_name your-domain.com;
    return 301 https://$server_name$request_uri;
}

server {
    listen 443 ssl http2;
    server_name your-domain.com;

    # SSL certificates (Let's Encrypt)
    ssl_certificate /etc/letsencrypt/live/your-domain.com/fullchain.pem;
    ssl_certificate_key /etc/letsencrypt/live/your-domain.com/privkey.pem;

    # Static client files
    root /var/www/astranyx;
    index index.html;

    location / {
        try_files $uri $uri/ /index.html;
    }

    # Phoenix WebSocket
    location /socket {
        proxy_pass http://127.0.0.1:4200;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection "upgrade";
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;

        # WebSocket timeouts
        proxy_connect_timeout 7d;
        proxy_send_timeout 7d;
        proxy_read_timeout 7d;
    }

    # Phoenix API (if needed)
    location /api {
        proxy_pass http://127.0.0.1:4200;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
    }
}
```

```bash
sudo ln -s /etc/nginx/sites-available/astranyx /etc/nginx/sites-enabled/
sudo nginx -t
sudo systemctl reload nginx
```

---

## 5. SSL Certificates

Use Let's Encrypt with certbot:

```bash
sudo apt install certbot python3-certbot-nginx
sudo certbot --nginx -d your-domain.com
```

For Coturn TLS, copy certificates:

```bash
sudo cp /etc/letsencrypt/live/your-domain.com/fullchain.pem /etc/coturn/
sudo cp /etc/letsencrypt/live/your-domain.com/privkey.pem /etc/coturn/
sudo chown turnserver:turnserver /etc/coturn/*.pem
```

---

## 6. Docker Compose (All-in-One)

For simpler deployment, use Docker Compose:

```yaml
# docker-compose.yml
version: '3.8'

services:
  phoenix:
    build: ./server
    ports:
      - "4200:4200"
    environment:
      - SECRET_KEY_BASE=${SECRET_KEY_BASE}
      - PHX_HOST=${PHX_HOST}
      - PORT=4200
    restart: unless-stopped

  coturn:
    image: coturn/coturn
    network_mode: host
    command: >
      -n
      --log-file=stdout
      --realm=${PHX_HOST}
      --user=astranyx:${TURN_PASSWORD}
      --lt-cred-mech
      --fingerprint
    restart: unless-stopped

  nginx:
    image: nginx:alpine
    ports:
      - "80:80"
      - "443:443"
    volumes:
      - ./client/dist:/usr/share/nginx/html:ro
      - ./nginx.conf:/etc/nginx/nginx.conf:ro
      - /etc/letsencrypt:/etc/letsencrypt:ro
    depends_on:
      - phoenix
    restart: unless-stopped
```

```bash
# .env
SECRET_KEY_BASE=your-64-char-secret
PHX_HOST=your-domain.com
TURN_PASSWORD=your-secure-password
```

```bash
docker-compose up -d
```

---

## 7. Monitoring

### Phoenix Telemetry

Phoenix has built-in telemetry. Add to your endpoint for metrics:

```elixir
# lib/astranyx_web/telemetry.ex
```

### Health Checks

Phoenix endpoint for load balancer health checks:

```elixir
# Add to router.ex
get "/health", HealthController, :index
```

### Logs

```bash
# Phoenix logs
journalctl -u astranyx -f

# Coturn logs
docker logs -f coturn

# nginx logs
tail -f /var/log/nginx/access.log
```

---

## 8. Scaling Considerations

### Single Server (< 1000 concurrent players)
- All components on one server
- Coturn handles ~500 simultaneous TURN connections per core

### Multi-Server
- **Client**: CDN (Cloudflare, AWS CloudFront)
- **Phoenix**: Multiple nodes with distributed Erlang or Redis PubSub
- **Coturn**: Multiple TURN servers with DNS load balancing

### Phoenix Clustering

For multiple Phoenix nodes sharing lobby state:

```elixir
# config/runtime.exs
config :astranyx, AstranyxWeb.Endpoint,
  pubsub_server: Astranyx.PubSub

# Use Redis adapter for cross-node PubSub
config :astranyx, Astranyx.PubSub,
  adapter: Phoenix.PubSub.Redis,
  url: System.get_env("REDIS_URL")
```

---

## Quick Start Checklist

1. [ ] Build client: `bun run build`
2. [ ] Build Phoenix release: `MIX_ENV=prod mix release`
3. [ ] Set up Coturn with secure password
4. [ ] Configure nginx reverse proxy
5. [ ] Set up SSL certificates
6. [ ] Configure firewall (3478, 5349, 49152-65535)
7. [ ] Set environment variables
8. [ ] Start all services
9. [ ] Test WebRTC with Trickle ICE tool
10. [ ] Test full game flow in production
