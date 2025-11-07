# Quick Deployment to Digital Ocean

Your Droplet is ready! Here's how to deploy in 5 minutes:

## Droplet Information

- **IP Address**: `209.38.65.54`
- **Name**: hupyy-temporal-prod
- **Size**: 1GB RAM, 1 CPU ($6/month)
- **Region**: San Francisco (sfo3)

## Step 1: Get Root Password

Digital Ocean has emailed your root password to your account email. Check your inbox for an email from Digital Ocean with subject "Your new Droplet".

## Step 2: SSH into Droplet

```bash
ssh root@209.38.65.54
# Enter the password from the email when prompted
```

## Step 3: Run Deployment Script

Once connected via SSH, run these commands:

```bash
# Download and run the setup script
curl -sSL https://raw.githubusercontent.com/o2alexanderfedin/hupyy-temporal/develop/deploy-to-droplet.sh | bash

# Or if you prefer to review first:
curl -sSL https://raw.githubusercontent.com/o2alexanderfedin/hupyy-temporal/develop/deploy-to-droplet.sh > deploy.sh
chmod +x deploy.sh
./deploy.sh
```

## Step 4: Copy Your Code

From your local machine, copy the code to the Droplet:

```bash
# On your Mac:
cd /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal

# Copy all files (will prompt for password)
scp -r $(ls -A | grep -v '.git\|node_modules\|__pycache__\|*.pyc\|.DS_Store\|logs\|reports') root@209.38.65.54:/opt/hupyy-temporal/

# Or use rsync (better for large transfers):
rsync -avz --exclude='.git' --exclude='node_modules' --exclude='__pycache__' --exclude='*.pyc' --exclude='.DS_Store' --exclude='logs/*' --exclude='reports/*' . root@209.38.65.54:/opt/hupyy-temporal/
```

## Step 5: Build and Run

Back in your SSH session on the Droplet:

```bash
cd /opt/hupyy-temporal

# Build the Docker image (takes 5-10 minutes)
docker compose build

# Start the application
docker compose up -d

# Check status
docker compose ps
docker compose logs -f
```

## Step 6: Access Your Application

Open in your browser:
```
http://209.38.65.54:8501
```

## Quick Commands

```bash
# Check application status
docker compose ps

# View logs
docker compose logs -f

# Restart application
docker compose restart

# Stop application
docker compose down

# Update and redeploy
git pull
docker compose build
docker compose up -d
```

## Troubleshooting

### Can't connect via SSH?
- Wait 1-2 minutes for Droplet to fully initialize
- Check your email for the root password
- Try: `ssh -v root@209.38.65.54` for verbose output

### Application not accessible?
```bash
# Check if Docker is running
docker compose ps

# Check firewall
ufw status

# Check logs
docker compose logs
```

### Out of memory?
The basic Droplet (1GB RAM) might struggle. Consider upgrading:
```bash
# Stop the app first
docker compose down

# Then resize via Digital Ocean dashboard to:
# - s-2vcpu-2gb ($18/month) - Recommended
```

## Next Steps

Once deployed:

1. **Set up monitoring** (optional):
   ```bash
   ./scripts/logs.sh follow
   ```

2. **Add SSL/HTTPS** (optional):
   - Point a domain to 209.38.65.54
   - Follow SSL setup in DIGITALOCEAN_DEPLOYMENT.md

3. **Enable automated backups** via Digital Ocean dashboard

## Cost Summary

- Droplet: $6/month (basic) or $18/month (recommended)
- Bandwidth: Included (1TB)
- Backups: $1.20/month (optional, 20% of Droplet cost)
- **Total**: ~$7-20/month

---

## Alternative: One-Command Deploy

If you want to deploy everything automatically:

```bash
# From your Mac, run:
./scripts/deploy-full.sh 209.38.65.54
```

(This script will be created if you need it)

---

**Support**: Check DIGITALOCEAN_DEPLOYMENT.md for detailed documentation.
