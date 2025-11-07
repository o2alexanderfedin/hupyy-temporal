# Docker Deployment Guide - Hupyy Temporal

Complete guide for deploying Hupyy Temporal using Docker containers.

---

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Quick Start](#quick-start)
3. [Docker Build](#docker-build)
4. [Docker Compose](#docker-compose)
5. [Configuration](#configuration)
6. [Production Deployment](#production-deployment)
7. [Troubleshooting](#troubleshooting)
8. [Advanced Topics](#advanced-topics)

---

## Prerequisites

### Required Software

- **Docker**: Version 20.10 or later
- **Docker Compose**: Version 2.0 or later (included with Docker Desktop)

### Verify Installation

```bash
docker --version
# Docker version 24.0.0 or later

docker compose version
# Docker Compose version v2.20.0 or later
```

### System Requirements

- **CPU**: 2+ cores recommended
- **RAM**: 2GB minimum, 4GB recommended
- **Disk**: 5GB free space (for image + data)
- **Network**: Internet access for building image

---

## Quick Start

### Option 1: Docker Compose (Recommended)

```bash
# 1. Clone repository
git clone https://github.com/o2alexanderfedin/hupyy-temporal.git
cd hupyy-temporal

# 2. Build and run
docker compose up -d

# 3. Access application
open http://localhost:8501
```

### Option 2: Docker CLI

```bash
# 1. Build image
docker build -t hupyy-temporal:latest .

# 2. Run container
docker run -d \
  --name hupyy-temporal \
  -p 8501:8501 \
  -v $(pwd)/reports:/app/reports \
  -v $(pwd)/logs:/app/logs \
  hupyy-temporal:latest

# 3. Access application
open http://localhost:8501
```

---

## Docker Build

### Standard Build

```bash
docker build -t hupyy-temporal:latest .
```

### Build with Custom Tag

```bash
docker build -t hupyy-temporal:v2.2.0 .
```

### Build Arguments

```bash
# Build without cache (full rebuild)
docker build --no-cache -t hupyy-temporal:latest .

# Build with specific platform
docker build --platform linux/amd64 -t hupyy-temporal:latest .

# Build multi-platform (requires buildx)
docker buildx build --platform linux/amd64,linux/arm64 -t hupyy-temporal:latest .
```

### Image Size Optimization

The Dockerfile uses multi-stage builds to minimize image size:

- **Builder stage**: Installs build dependencies
- **Runtime stage**: Only includes runtime dependencies
- **Result**: ~500MB final image (vs ~1.5GB without optimization)

---

## Docker Compose

### Start Services

```bash
# Start in background (detached mode)
docker compose up -d

# Start with logs visible
docker compose up

# Start specific service
docker compose up hupyy-temporal
```

### Stop Services

```bash
# Stop all services
docker compose stop

# Stop and remove containers
docker compose down

# Stop and remove containers + volumes
docker compose down -v
```

### View Logs

```bash
# View all logs
docker compose logs

# Follow logs in real-time
docker compose logs -f

# View logs for specific service
docker compose logs hupyy-temporal

# View last 100 lines
docker compose logs --tail=100 -f
```

### Rebuild After Code Changes

```bash
# Rebuild and restart
docker compose up -d --build

# Force rebuild without cache
docker compose build --no-cache
docker compose up -d
```

---

## Configuration

### Environment Variables

Create a `.env` file in the project root:

```bash
# .env file

# Optional: Claude API configuration
ANTHROPIC_API_KEY=your_api_key_here
CLAUDE_MODEL=claude-sonnet-3-5-20241022

# Optional: Timezone
TZ=America/New_York

# Optional: Resource limits
DOCKER_CPU_LIMIT=2
DOCKER_MEMORY_LIMIT=2G
```

### Volume Mounts

The following volumes are configured by default:

| Host Path | Container Path | Purpose |
|-----------|----------------|---------|
| `./reports` | `/app/reports` | Generated PDF reports |
| `./logs` | `/app/logs` | Application logs |

### Port Configuration

Change the host port if 8501 is already in use:

```yaml
# docker-compose.yml
ports:
  - "8080:8501"  # Access on http://localhost:8080
```

Or via Docker CLI:

```bash
docker run -d -p 8080:8501 hupyy-temporal:latest
```

---

## Production Deployment

### Security Best Practices

1. **Use specific version tags**:
   ```bash
   docker build -t hupyy-temporal:v2.2.0 .
   ```

2. **Run as non-root user** (already configured in Dockerfile):
   ```dockerfile
   USER hupyy  # Non-root user
   ```

3. **Enable read-only root filesystem**:
   ```yaml
   # docker-compose.yml
   read_only: true
   tmpfs:
     - /tmp
     - /app/reports
     - /app/logs
   ```

4. **Use secrets for sensitive data**:
   ```bash
   # Store API key in Docker secret
   echo "your_api_key" | docker secret create anthropic_api_key -
   ```

### Resource Limits

Configure resource limits in `docker-compose.yml`:

```yaml
deploy:
  resources:
    limits:
      cpus: '2'
      memory: 2G
    reservations:
      cpus: '0.5'
      memory: 512M
```

### Health Checks

The container includes a health check:

```bash
# Check container health
docker inspect --format='{{.State.Health.Status}}' hupyy-temporal

# View health check logs
docker inspect hupyy-temporal | jq '.[0].State.Health'
```

### Reverse Proxy (Nginx)

For production, use a reverse proxy:

1. Uncomment nginx service in `docker-compose.yml`
2. Create `nginx/nginx.conf`:

```nginx
server {
    listen 80;
    server_name yourdomain.com;

    location / {
        proxy_pass http://hupyy-temporal:8501;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection "upgrade";
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;
    }
}
```

3. Add SSL/TLS:
```nginx
listen 443 ssl;
ssl_certificate /etc/nginx/ssl/cert.pem;
ssl_certificate_key /etc/nginx/ssl/key.pem;
```

---

## Troubleshooting

### Container Won't Start

```bash
# Check logs
docker logs hupyy-temporal

# Check container status
docker ps -a | grep hupyy-temporal

# Inspect container
docker inspect hupyy-temporal
```

### Port Already in Use

```bash
# Find process using port 8501
lsof -i :8501

# Kill process
kill -9 <PID>

# Or use different port
docker run -p 8080:8501 hupyy-temporal:latest
```

### Permission Issues with Volumes

```bash
# Fix ownership on host
sudo chown -R $(id -u):$(id -g) reports/ logs/

# Or run container with your user ID
docker run --user $(id -u):$(id -g) hupyy-temporal:latest
```

### cvc5 Binary Not Found

```bash
# Verify cvc5 is in image
docker run --rm hupyy-temporal:latest ls -la /app/bin/

# Check cvc5 permissions
docker run --rm hupyy-temporal:latest /app/bin/cvc5 --version
```

### Application Not Responding

```bash
# Check health status
docker exec hupyy-temporal curl http://localhost:8501/_stcore/health

# Restart container
docker restart hupyy-temporal

# View Streamlit logs
docker logs -f hupyy-temporal | grep streamlit
```

### Out of Memory

```bash
# Check memory usage
docker stats hupyy-temporal

# Increase memory limit
docker update --memory 4G hupyy-temporal

# Or in docker-compose.yml
deploy:
  resources:
    limits:
      memory: 4G
```

---

## Advanced Topics

### Multi-Architecture Builds

Build for multiple platforms (Mac M1/M2, Intel, ARM):

```bash
# Create buildx builder
docker buildx create --name multiarch --use

# Build for multiple platforms
docker buildx build \
  --platform linux/amd64,linux/arm64 \
  -t hupyy-temporal:latest \
  --push \
  .
```

### Docker Registry

Push to Docker Hub or private registry:

```bash
# Login to Docker Hub
docker login

# Tag image
docker tag hupyy-temporal:latest yourusername/hupyy-temporal:latest

# Push to registry
docker push yourusername/hupyy-temporal:latest

# Pull from registry
docker pull yourusername/hupyy-temporal:latest
```

### Kubernetes Deployment

Example Kubernetes manifests:

```yaml
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: hupyy-temporal
spec:
  replicas: 2
  selector:
    matchLabels:
      app: hupyy-temporal
  template:
    metadata:
      labels:
        app: hupyy-temporal
    spec:
      containers:
      - name: hupyy-temporal
        image: hupyy-temporal:latest
        ports:
        - containerPort: 8501
        resources:
          limits:
            memory: "2Gi"
            cpu: "2"
          requests:
            memory: "512Mi"
            cpu: "500m"
        volumeMounts:
        - name: reports
          mountPath: /app/reports
      volumes:
      - name: reports
        persistentVolumeClaim:
          claimName: hupyy-reports-pvc
```

### CI/CD Integration

Example GitHub Actions workflow:

```yaml
# .github/workflows/docker-build.yml
name: Docker Build

on:
  push:
    tags:
      - 'v*'

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Build Docker image
        run: docker build -t hupyy-temporal:${{ github.ref_name }} .

      - name: Push to registry
        run: docker push hupyy-temporal:${{ github.ref_name }}
```

---

## Docker Commands Cheatsheet

```bash
# Build
docker build -t hupyy-temporal:latest .

# Run
docker run -d -p 8501:8501 --name hupyy-temporal hupyy-temporal:latest

# Stop/Start
docker stop hupyy-temporal
docker start hupyy-temporal

# Restart
docker restart hupyy-temporal

# View logs
docker logs -f hupyy-temporal

# Execute command in container
docker exec -it hupyy-temporal bash

# View resource usage
docker stats hupyy-temporal

# Remove container
docker rm -f hupyy-temporal

# Remove image
docker rmi hupyy-temporal:latest

# Prune unused resources
docker system prune -a
```

---

## Support

For issues or questions:
- **GitHub Issues**: https://github.com/o2alexanderfedin/hupyy-temporal/issues
- **Documentation**: See `docs/` directory
- **Health Check**: http://localhost:8501/_stcore/health

---

**Last Updated**: November 2025
**Docker Version**: 24.0+
**Compose Version**: v2.20+
