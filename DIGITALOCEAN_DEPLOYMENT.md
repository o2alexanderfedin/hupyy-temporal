# Digital Ocean Deployment Guide - Hupyy Temporal

Complete guide for deploying Hupyy Temporal to Digital Ocean using Docker.

---

## Table of Contents

1. [Current Application Profile](#current-application-profile)
2. [Deployment Options Comparison](#deployment-options-comparison)
3. [Recommended Approach](#recommended-approach)
4. [Option 1: Droplet Deployment (Recommended)](#option-1-droplet-deployment-recommended)
5. [Option 2: App Platform Deployment](#option-2-app-platform-deployment)
6. [Security Configuration](#security-configuration)
7. [Domain & SSL Setup](#domain--ssl-setup)
8. [Monitoring & Maintenance](#monitoring--maintenance)
9. [Cost Estimates](#cost-estimates)
10. [Troubleshooting](#troubleshooting)

---

## Current Application Profile

### Technical Specifications

- **Docker Image**: `hupyy-temporal:latest`
- **Image Size**: 1.12GB
- **Platform**: linux/arm64 (also compatible with linux/amd64)
- **Port**: 8501 (Streamlit)
- **Dependencies**:
  - Python 3.11
  - Node.js 20.x (for Claude CLI)
  - cvc5 1.1.2 (SMT solver)
  - Claude CLI

### Resource Requirements

**Minimum**:
- CPU: 0.5 cores
- RAM: 512MB
- Disk: 5GB

**Recommended**:
- CPU: 2 cores
- RAM: 2GB
- Disk: 10GB

### Environment Variables

Required:
- `ANTHROPIC_API_KEY` (Claude API key)
- `CLAUDE_MODEL` (optional, default: claude-sonnet-3-5-20241022)
- `TZ` (optional, default: UTC)

### Persistent Storage

- `/app/reports` - Generated PDF reports
- `/app/logs` - Application logs

---

## Deployment Options Comparison

### Option 1: Droplets (Virtual Machines)

**Pros**:
✅ Full control over infrastructure
✅ Easy Docker Compose deployment
✅ Direct SSH access for debugging
✅ Can use Docker volumes for persistence
✅ More cost-effective for 24/7 operation
✅ Supports custom networking (VPN, load balancers)
✅ No platform-specific limitations

**Cons**:
❌ Manual security updates required
❌ Need to configure monitoring yourself
❌ Manual scaling (vertical/horizontal)
❌ You manage OS and Docker

**Best For**:
- Production deployments requiring full control
- Applications needing custom configurations
- Teams comfortable with Linux administration
- Long-running services

### Option 2: App Platform (Managed PaaS)

**Pros**:
✅ Fully managed (auto-scaling, security, updates)
✅ Built-in CI/CD from GitHub
✅ Automatic SSL certificates
✅ Zero infrastructure management
✅ Easy rollbacks and deployments

**Cons**:
❌ More expensive for always-on services
❌ Limited networking configuration
❌ Cannot use docker-compose.yml directly
❌ May require code changes for stateful storage
❌ Less control over runtime environment

**Best For**:
- Proof-of-concept / MVP deployments
- Teams without DevOps expertise
- Applications with variable traffic
- Quick deployments without infrastructure setup

---

## Recommended Approach

**For Hupyy Temporal: Use Droplets (Option 1)**

**Reasoning**:
1. Application is stateful (generates reports, logs)
2. Requires persistent storage for reports/logs
3. Already have docker-compose.yml configured
4. More cost-effective for 24/7 operation
5. Full control over cvc5 binary and environment
6. Easier debugging with SSH access

---

## Option 1: Droplet Deployment (Recommended)

### Step 1: Create Droplet

#### Via Digital Ocean Dashboard

1. **Login to Digital Ocean**: https://cloud.digitalocean.com
2. **Create Droplet**:
   - Click "Create" → "Droplets"
   - Choose image: **Docker on Ubuntu 24.04** (Marketplace → Apps)
   - Plan: **Basic** → **$12/month** (2GB RAM, 1 vCPU, 50GB SSD)
   - Datacenter: Choose closest to your users
   - Authentication: **SSH Key** (recommended) or Password
   - Hostname: `hupyy-temporal-prod`
   - Advanced: Enable **Monitoring** (free)

3. **Wait for Creation**: ~60 seconds

#### Via CLI (doctl)

```bash
# Install doctl
brew install doctl  # macOS
# or: sudo snap install doctl  # Linux

# Authenticate
doctl auth init

# Create droplet with Docker pre-installed
doctl compute droplet create hupyy-temporal-prod \
  --image docker-20-04 \
  --size s-2vcpu-2gb \
  --region sfo3 \
  --ssh-keys YOUR_SSH_KEY_ID \
  --enable-monitoring \
  --wait

# Get droplet IP
doctl compute droplet list
```

### Step 2: Initial Server Setup

```bash
# SSH into droplet
ssh root@YOUR_DROPLET_IP

# Update system
apt update && apt upgrade -y

# Install additional tools
apt install -y curl git htop

# Create non-root user (recommended)
adduser hupyy
usermod -aG sudo hupyy
usermod -aG docker hupyy

# Set up firewall
ufw allow OpenSSH
ufw allow 80/tcp      # HTTP
ufw allow 443/tcp     # HTTPS
ufw allow 8501/tcp    # Streamlit (temporary for testing)
ufw enable

# Switch to hupyy user
su - hupyy
```

### Step 3: Deploy Application

```bash
# Clone repository
git clone https://github.com/o2alexanderfedin/hupyy-temporal.git
cd hupyy-temporal

# Create .env file with API key
cat > .env <<EOF
ANTHROPIC_API_KEY=your_api_key_here
CLAUDE_MODEL=claude-sonnet-3-5-20241022
TZ=America/New_York
EOF

# Create persistent directories
mkdir -p reports logs

# Pull and build image
docker compose pull || docker compose build

# Start services
docker compose up -d

# Check status
docker compose ps
docker compose logs -f
```

### Step 4: Verify Deployment

```bash
# Check container health
docker inspect hupyy-temporal | grep -A 5 Health

# Test application
curl http://localhost:8501/_stcore/health

# View logs
docker compose logs --tail 50 hupyy-temporal

# Check cvc5
docker exec hupyy-temporal cvc5 --version
```

### Step 5: Set Up Nginx Reverse Proxy (Production)

```bash
# Install Nginx
sudo apt install -y nginx certbot python3-certbot-nginx

# Create Nginx config
sudo nano /etc/nginx/sites-available/hupyy-temporal
```

Add configuration:

```nginx
upstream hupyy_temporal {
    server localhost:8501;
}

server {
    listen 80;
    server_name yourdomain.com www.yourdomain.com;

    location / {
        proxy_pass http://hupyy_temporal;
        proxy_http_version 1.1;

        # WebSocket support (required for Streamlit)
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection "upgrade";

        # Headers
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;

        # Timeouts for long-running operations
        proxy_connect_timeout 300s;
        proxy_send_timeout 300s;
        proxy_read_timeout 300s;
    }

    # Serve static files efficiently
    location /_stcore/static {
        proxy_pass http://hupyy_temporal/_stcore/static;
        proxy_cache_valid 200 1d;
        proxy_cache_bypass $http_pragma $http_authorization;
    }
}
```

Enable and test:

```bash
# Enable site
sudo ln -s /etc/nginx/sites-available/hupyy-temporal /etc/nginx/sites-enabled/

# Test configuration
sudo nginx -t

# Restart Nginx
sudo systemctl restart nginx

# Enable auto-start
sudo systemctl enable nginx
```

### Step 6: Set Up SSL Certificate (Let's Encrypt)

```bash
# Obtain certificate (automatic)
sudo certbot --nginx -d yourdomain.com -d www.yourdomain.com

# Test auto-renewal
sudo certbot renew --dry-run

# Certificates auto-renew via cron
```

### Step 7: Set Up Auto-Restart on Boot

```bash
# Create systemd service
sudo nano /etc/systemd/system/hupyy-temporal.service
```

Add service configuration:

```ini
[Unit]
Description=Hupyy Temporal Docker Service
Requires=docker.service
After=docker.service

[Service]
Type=oneshot
RemainAfterExit=yes
WorkingDirectory=/home/hupyy/hupyy-temporal
ExecStart=/usr/bin/docker compose up -d
ExecStop=/usr/bin/docker compose down
User=hupyy
Group=hupyy

[Install]
WantedBy=multi-user.target
```

Enable service:

```bash
sudo systemctl daemon-reload
sudo systemctl enable hupyy-temporal.service
sudo systemctl start hupyy-temporal.service

# Check status
sudo systemctl status hupyy-temporal.service
```

### Step 8: Set Up Log Rotation

```bash
# Create logrotate config
sudo nano /etc/logrotate.d/hupyy-temporal
```

Add configuration:

```
/home/hupyy/hupyy-temporal/logs/*.log {
    daily
    rotate 7
    compress
    delaycompress
    notifempty
    missingok
    create 0644 hupyy hupyy
}
```

### Step 9: Set Up Monitoring

```bash
# Install monitoring script
cat > /home/hupyy/monitor-hupyy.sh <<'EOF'
#!/bin/bash
# Check if container is healthy
HEALTH=$(docker inspect --format='{{.State.Health.Status}}' hupyy-temporal 2>/dev/null)

if [ "$HEALTH" != "healthy" ]; then
    echo "$(date): Container unhealthy, restarting..."
    cd /home/hupyy/hupyy-temporal
    docker compose restart

    # Send alert (optional - configure with your email)
    # echo "Hupyy Temporal restarted" | mail -s "Container Alert" your@email.com
fi
EOF

chmod +x /home/hupyy/monitor-hupyy.sh

# Add to crontab (check every 5 minutes)
crontab -e
# Add line: */5 * * * * /home/hupyy/monitor-hupyy.sh >> /home/hupyy/monitor.log 2>&1
```

---

## Option 2: App Platform Deployment

### Prerequisites

- GitHub repository with code
- Digital Ocean account
- ANTHROPIC_API_KEY

### Step 1: Prepare Repository

App Platform requires specific configuration:

```yaml
# .do/app.yaml
name: hupyy-temporal
region: sfo

services:
  - name: web
    dockerfile_path: Dockerfile
    source_dir: /
    github:
      repo: o2alexanderfedin/hupyy-temporal
      branch: main
      deploy_on_push: true

    http_port: 8501

    instance_count: 1
    instance_size_slug: basic-xs  # $5/month

    envs:
      - key: ANTHROPIC_API_KEY
        scope: RUN_TIME
        type: SECRET
      - key: CLAUDE_MODEL
        value: claude-sonnet-3-5-20241022
      - key: TZ
        value: UTC

    health_check:
      http_path: /_stcore/health
      initial_delay_seconds: 60
      period_seconds: 30
      timeout_seconds: 10
```

### Step 2: Deploy via Dashboard

1. Login to Digital Ocean: https://cloud.digitalocean.com
2. Navigate to "Apps" → "Create App"
3. Choose "GitHub" as source
4. Select repository: `o2alexanderfedin/hupyy-temporal`
5. App Platform auto-detects Dockerfile
6. Configure:
   - **Name**: `hupyy-temporal`
   - **Region**: Choose closest to users
   - **Plan**: Basic ($5/month for 512MB RAM)
7. Add environment variables:
   - `ANTHROPIC_API_KEY` (encrypted)
   - `CLAUDE_MODEL`
   - `TZ`
8. Review and deploy

### Step 3: Deploy via CLI

```bash
# Install doctl
brew install doctl

# Authenticate
doctl auth init

# Create app from spec
doctl apps create --spec .do/app.yaml

# Get app ID
doctl apps list

# Monitor deployment
doctl apps logs <APP_ID> --follow
```

### Limitations for App Platform

- **Persistent storage**: Use Digital Ocean Spaces for reports (requires code changes)
- **No docker-compose**: Must use app.yaml spec
- **Cost**: More expensive for 24/7 operation ($5-12/month vs $12/month droplet)
- **Less control**: Cannot SSH or debug directly

---

## Security Configuration

### 1. Environment Variables

**Never commit .env to Git**:

```bash
# Verify .env is in .gitignore
grep -q "^\.env$" .gitignore || echo ".env" >> .gitignore

# Store secrets securely
# Option 1: Digital Ocean Secrets (App Platform)
# Option 2: Use environment variables (Droplet)
```

### 2. Firewall Rules

```bash
# Droplet firewall
ufw status

# Only allow necessary ports:
# - 22 (SSH)
# - 80 (HTTP)
# - 443 (HTTPS)
# Close 8501 after Nginx is set up
ufw delete allow 8501/tcp
```

### 3. SSH Hardening

```bash
# Disable root login
sudo nano /etc/ssh/sshd_config
# Set: PermitRootLogin no
# Set: PasswordAuthentication no  # Force SSH keys

sudo systemctl restart sshd
```

### 4. Docker Security

```bash
# Run as non-root user (already configured in Dockerfile)
docker exec hupyy-temporal whoami  # Should show: hupyy

# Limit resources (already in docker-compose.yml)
# Check: deploy.resources.limits

# Enable Docker Content Trust (optional)
export DOCKER_CONTENT_TRUST=1
```

### 5. API Key Rotation

```bash
# Update API key
cd /home/hupyy/hupyy-temporal
nano .env  # Update ANTHROPIC_API_KEY

# Restart without downtime
docker compose up -d --force-recreate
```

---

## Domain & SSL Setup

### Option A: Using Digital Ocean Nameservers

1. **Add Domain to Digital Ocean**:
   - Dashboard → "Networking" → "Domains"
   - Add domain: `yourdomain.com`

2. **Update Nameservers at Registrar**:
   - Point to Digital Ocean nameservers:
     - `ns1.digitalocean.com`
     - `ns2.digitalocean.com`
     - `ns3.digitalocean.com`

3. **Create DNS Records**:
   ```
   A Record:     @           → YOUR_DROPLET_IP
   A Record:     www         → YOUR_DROPLET_IP
   CNAME:        hupyy       → @
   ```

4. **Install SSL Certificate**:
   ```bash
   sudo certbot --nginx -d yourdomain.com -d www.yourdomain.com
   ```

### Option B: Using External DNS

1. **Create A Record at DNS Provider**:
   ```
   yourdomain.com    →  YOUR_DROPLET_IP
   www.yourdomain.com → YOUR_DROPLET_IP
   ```

2. **Install SSL Certificate**:
   ```bash
   sudo certbot --nginx -d yourdomain.com -d www.yourdomain.com
   ```

---

## Monitoring & Maintenance

### Built-in Monitoring

**Digital Ocean Droplet Monitoring** (Free):
- CPU usage
- Memory usage
- Disk I/O
- Network bandwidth

Access: Dashboard → Droplets → Monitoring tab

### Application Monitoring

```bash
# View logs in real-time
cd /home/hupyy/hupyy-temporal
./scripts/logs.sh follow

# Check container stats
docker stats hupyy-temporal

# Check disk usage
df -h
du -sh /home/hupyy/hupyy-temporal/logs
du -sh /home/hupyy/hupyy-temporal/reports

# Check memory usage
free -h
```

### Automated Alerts (Optional)

Install monitoring agent:

```bash
# Using Netdata (free, lightweight)
bash <(curl -Ss https://my-netdata.io/kickstart.sh)

# Access dashboard at: http://YOUR_IP:19999
```

### Backup Strategy

**Automated Daily Backups**:

```bash
# Create backup script
cat > /home/hupyy/backup-hupyy.sh <<'EOF'
#!/bin/bash
DATE=$(date +%Y%m%d)
BACKUP_DIR="/home/hupyy/backups"
mkdir -p $BACKUP_DIR

# Backup reports and logs
tar -czf $BACKUP_DIR/hupyy-data-$DATE.tar.gz \
    /home/hupyy/hupyy-temporal/reports \
    /home/hupyy/hupyy-temporal/logs \
    /home/hupyy/hupyy-temporal/.env

# Keep only last 7 days
find $BACKUP_DIR -name "hupyy-data-*.tar.gz" -mtime +7 -delete

# Optional: Upload to Digital Ocean Spaces
# s3cmd put $BACKUP_DIR/hupyy-data-$DATE.tar.gz s3://your-bucket/
EOF

chmod +x /home/hupyy/backup-hupyy.sh

# Add to crontab (daily at 2 AM)
crontab -e
# Add: 0 2 * * * /home/hupyy/backup-hupyy.sh
```

**Digital Ocean Snapshots**:
- Dashboard → Droplets → Your Droplet → "Snapshots"
- Manual or weekly automated snapshots ($0.05/GB/month)

### Update Strategy

```bash
# Update application
cd /home/hupyy/hupyy-temporal
git pull origin main
docker compose build --no-cache
docker compose up -d

# Update system packages
sudo apt update && sudo apt upgrade -y
sudo reboot  # If kernel updates
```

---

## Cost Estimates

### Droplet Deployment (24/7 Operation)

| Component | Plan | Monthly Cost |
|-----------|------|--------------|
| Droplet | 2GB RAM, 1 vCPU | **$12** |
| Bandwidth | 2TB included | **$0** |
| Monitoring | Basic (free) | **$0** |
| Backups | Snapshot (5GB) | **$0.25** |
| Domain | External registrar | **$10-15/year** |
| SSL Certificate | Let's Encrypt | **$0** |
| **Total** | | **~$12.25/month** |

**Recommended Droplet Tiers**:
- **Development**: $6/month (1GB RAM, 1 vCPU) - Basic testing
- **Production Small**: $12/month (2GB RAM, 1 vCPU) - Recommended start
- **Production Medium**: $24/month (4GB RAM, 2 vCPU) - High traffic
- **Production Large**: $48/month (8GB RAM, 4 vCPU) - Very high traffic

### App Platform Deployment (24/7 Operation)

| Component | Plan | Monthly Cost |
|-----------|------|--------------|
| App Platform | 512MB RAM | **$5** |
| Bandwidth | 40GB included | **$0** |
| Additional RAM | 1GB upgrade | **+$7** |
| Spaces (storage) | 250GB | **$5** |
| Domain | Included | **$0** |
| SSL Certificate | Auto | **$0** |
| **Total** | | **$10-17/month** |

**App Platform Limitations**:
- Must handle stateful data differently (requires code changes)
- Less control over environment
- Automatic scaling can increase costs

### Cost Comparison

**Winner: Droplets** ($12/month) - Better value for:
- 24/7 operation
- Full control
- Direct Docker Compose deployment
- No code changes needed

---

## Troubleshooting

### Container Won't Start

```bash
# Check logs
docker compose logs hupyy-temporal

# Check specific issues
docker inspect hupyy-temporal

# Verify image built correctly
docker images | grep hupyy-temporal

# Rebuild from scratch
docker compose down
docker compose build --no-cache
docker compose up -d
```

### cvc5 Binary Issues

```bash
# Verify cvc5 is installed
docker exec hupyy-temporal which cvc5
docker exec hupyy-temporal cvc5 --version

# Test cvc5
docker exec hupyy-temporal bash -c 'echo -e "(set-logic QF_LIA)\n(assert true)\n(check-sat)" | cvc5 --incremental'
```

### Out of Memory

```bash
# Check memory usage
free -h
docker stats hupyy-temporal

# Solution: Upgrade droplet
# Dashboard → Droplets → Resize → Increase RAM
```

### High Disk Usage

```bash
# Check disk usage
df -h
du -sh /home/hupyy/hupyy-temporal/*

# Clean old logs
cd /home/hupyy/hupyy-temporal
./scripts/logs.sh clean

# Clean old Docker images
docker system prune -a
```

### SSL Certificate Issues

```bash
# Renew certificate manually
sudo certbot renew

# Check certificate status
sudo certbot certificates

# Test auto-renewal
sudo certbot renew --dry-run
```

### Application Not Accessible

```bash
# Check Nginx status
sudo systemctl status nginx
sudo nginx -t

# Check firewall
sudo ufw status

# Check container health
docker inspect hupyy-temporal | grep -A 5 Health

# Test locally
curl http://localhost:8501/_stcore/health
```

### Claude API Issues

```bash
# Verify API key is set
docker exec hupyy-temporal env | grep ANTHROPIC

# Test Claude CLI
docker exec hupyy-temporal claude --version

# Check Claude Code logs
docker compose logs hupyy-temporal | grep -i claude
```

---

## Quick Commands Reference

```bash
# Application Management
docker compose up -d              # Start application
docker compose down               # Stop application
docker compose restart            # Restart application
docker compose logs -f            # View logs
docker compose ps                 # Check status

# Updates
git pull origin main              # Pull latest code
docker compose build --no-cache   # Rebuild image
docker compose up -d              # Apply updates

# Monitoring
docker stats hupyy-temporal       # Resource usage
./scripts/logs.sh follow          # Follow logs
curl http://localhost:8501/_stcore/health  # Health check

# Maintenance
docker system prune -a            # Clean up Docker
./scripts/logs.sh clean           # Clean old logs
sudo apt update && sudo apt upgrade -y  # Update system

# Backups
tar -czf backup.tar.gz reports/ logs/ .env  # Manual backup
```

---

## Next Steps

1. ✅ Choose deployment option (Droplets recommended)
2. ✅ Create Digital Ocean account
3. ✅ Set up domain (optional but recommended)
4. ✅ Follow deployment steps above
5. ✅ Configure monitoring and backups
6. ✅ Test application thoroughly
7. ✅ Set up alerts for production

---

## Support & Resources

- **Digital Ocean Docs**: https://docs.digitalocean.com
- **Docker Docs**: https://docs.docker.com
- **Hupyy Temporal Docs**: See `DOCKER_DEPLOYMENT.md`
- **Digital Ocean Community**: https://www.digitalocean.com/community

---

**Last Updated**: November 2025
**Recommended Provider**: Digital Ocean Droplets
**Recommended Plan**: $12/month (2GB RAM, 1 vCPU)
