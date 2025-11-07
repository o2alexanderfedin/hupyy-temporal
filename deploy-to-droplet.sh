#!/bin/bash
# Hupyy Temporal - Digital Ocean Droplet Deployment Script
# This script sets up and deploys the application on a fresh Ubuntu 24.04 Droplet

set -e  # Exit on any error

echo "=================================================="
echo "  Hupyy Temporal - Droplet Deployment"
echo "=================================================="
echo ""

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Step 1: Update system
echo -e "${GREEN}[1/8] Updating system packages...${NC}"
apt-get update
apt-get upgrade -y

# Step 2: Install Docker
echo -e "${GREEN}[2/8] Installing Docker...${NC}"
apt-get install -y ca-certificates curl gnupg
install -m 0755 -d /etc/apt/keyrings
curl -fsSL https://download.docker.com/linux/ubuntu/gpg | gpg --dearmor -o /etc/apt/keyrings/docker.gpg
chmod a+r /etc/apt/keyrings/docker.gpg

echo \
  "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/ubuntu \
  $(. /etc/os-release && echo "$VERSION_CODENAME") stable" | \
  tee /etc/apt/sources.list.d/docker.list > /dev/null

apt-get update
apt-get install -y docker-ce docker-ce-cli containerd.io docker-buildx-plugin docker-compose-plugin

# Step 3: Configure UFW Firewall
echo -e "${GREEN}[3/8] Configuring firewall...${NC}"
ufw --force enable
ufw allow 22/tcp   # SSH
ufw allow 8501/tcp # Streamlit app
ufw status

# Step 4: Create application directory
echo -e "${GREEN}[4/8] Creating application directory...${NC}"
mkdir -p /opt/hupyy-temporal
cd /opt/hupyy-temporal

# Step 5: Create .env file with OAuth token
echo -e "${GREEN}[5/8] Creating environment configuration...${NC}"
cat > .env <<'EOF'
# Claude Subscription OAuth Token
CLAUDE_CODE_OAUTH_TOKEN=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

# Claude Model
CLAUDE_MODEL=claude-sonnet-3-5-20241022

# Timezone
TZ=UTC
EOF

chmod 600 .env

# Step 6: Create docker-compose.yml
echo -e "${GREEN}[6/8] Creating Docker Compose configuration...${NC}"
cat > docker-compose.yml <<'EOF'
version: '3.8'

services:
  hupyy-temporal:
    build:
      context: .
      dockerfile: Dockerfile
    image: hupyy-temporal:latest
    container_name: hupyy-temporal
    restart: unless-stopped
    ports:
      - "8501:8501"
    environment:
      - STREAMLIT_SERVER_HEADLESS=true
      - STREAMLIT_BROWSER_GATHERUSAGESTATS=false
      - STREAMLIT_SERVER_PORT=8501
      - STREAMLIT_SERVER_ADDRESS=0.0.0.0
      - PYTHONUNBUFFERED=1
      - TZ=UTC
      - CLAUDE_CODE_OAUTH_TOKEN=${CLAUDE_CODE_OAUTH_TOKEN}
      - CLAUDE_MODEL=${CLAUDE_MODEL:-claude-sonnet-3-5-20241022}
    volumes:
      - ./reports:/app/reports
      - ./logs:/app/logs
    deploy:
      resources:
        limits:
          cpus: '1'
          memory: 1G
        reservations:
          cpus: '0.25'
          memory: 256M
    healthcheck:
      test: ["CMD", "python", "-c", "import requests; requests.get('http://localhost:8501/_stcore/health')"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s
    logging:
      driver: "json-file"
      options:
        max-size: "10m"
        max-file: "3"

networks:
  default:
    name: hupyy-network
EOF

# Create directories
mkdir -p logs reports

echo -e "${GREEN}[7/8] Application structure ready!${NC}"
echo ""
echo -e "${YELLOW}Next steps:${NC}"
echo "1. Copy your application code to /opt/hupyy-temporal/"
echo "2. Run: docker compose build"
echo "3. Run: docker compose up -d"
echo ""
echo -e "${GREEN}[8/8] Deployment script completed!${NC}"
echo ""
echo "Your Droplet IP: $(curl -s ifconfig.me)"
echo "Application will be available at: http://$(curl -s ifconfig.me):8501"
echo ""
echo "=================================================="
EOF
