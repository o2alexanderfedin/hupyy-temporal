# CI/CD Pipeline Guide

## Overview

This project uses a fully automated CI/CD pipeline that deploys to Digital Ocean App Platform. Every push to the `develop` branch automatically triggers testing, building, and deployment.

## Pipeline Architecture

```
┌─────────────────┐
│  Git Push       │
│  to develop     │
└────────┬────────┘
         │
         ├─────────────────────────────────┐
         │                                 │
         v                                 v
┌─────────────────┐              ┌─────────────────┐
│ GitHub Actions  │              │ DO App Platform │
│                 │              │                 │
│ • Lint Code     │              │ • Pull Repo     │
│ • Type Check    │              │ • Build Docker  │
│ • Build Docker  │              │ • Deploy        │
│ • Run Tests     │              │ • Health Check  │
└────────┬────────┘              └────────┬────────┘
         │                                │
         v                                v
   ✅ Quality Gates               🚀 Production
```

## Components

### 1. GitHub Actions Workflow

**Location**: `.github/workflows/ci-cd.yml`

**Triggers**:
- Push to `develop` or `main` branches
- Pull requests to `develop` or `main`

**Jobs**:

1. **Lint and Type Check**
   - Sets up Python 3.11
   - Installs dependencies from requirements.txt
   - Runs flake8 for code style checking
   - Runs mypy for static type checking

2. **Build and Verify**
   - Builds Docker image using Buildx
   - Uses layer caching for faster builds
   - Tests the built image by verifying Python, Node.js, and Claude CLI

3. **Deploy Notification**
   - Runs only on push to `develop`
   - Confirms all checks passed
   - Notifies that App Platform will deploy automatically

### 2. Digital Ocean App Platform

**Location**: `.do/app.yaml`

**Configuration**:
- **Auto-deploy**: Enabled via `deploy_on_push: true`
- **Source**: GitHub repo `o2alexanderfedin/hupyy-temporal`, branch `develop`
- **Build**: Uses Dockerfile in repository root
- **Instance**: basic-xxs (smallest instance, can be upgraded)
- **Region**: San Francisco (sfo)

**Environment Variables**:
- Streamlit configuration (port 8501, headless mode)
- Claude model configuration
- Secure OAuth token (stored as DO secret)

**Health Check**:
- Path: `/_stcore/health`
- Initial delay: 60 seconds
- Check interval: 30 seconds
- Timeout: 10 seconds

## How It Works

### Automatic Deployment Flow

1. **Developer pushes code** to `develop` branch
   ```bash
   git add .
   git commit -m "feat: Add new feature"
   git push origin develop
   ```

2. **GitHub Actions starts** (runs in parallel):
   - Linting and type checking (~2-3 minutes)
   - Docker build and verification (~5-7 minutes)

3. **If all checks pass**, App Platform receives webhook from GitHub

4. **App Platform deploys**:
   - Clones latest code from GitHub
   - Builds Docker image (using cached layers when possible)
   - Deploys new container
   - Performs health check
   - Routes traffic to new version (~10-15 minutes total)

5. **Old version** is kept running until new version is healthy (zero-downtime deployment)

### Manual Deployment

If you need to manually trigger a deployment:

```bash
# Via App Platform dashboard
open https://cloud.digitalocean.com/apps

# Via CLI
doctl apps create-deployment <app-id>
```

## Monitoring Deployments

### Via Web Dashboard

1. Visit: https://cloud.digitalocean.com/apps
2. Select your app: `hupyy-temporal`
3. View:
   - Current deployment status
   - Build logs
   - Runtime logs
   - Performance metrics

### Via CLI

```bash
# List all apps
doctl apps list

# Get app details
doctl apps get <app-id>

# View deployment logs
doctl apps logs <app-id> --type build
doctl apps logs <app-id> --type run

# List deployments
doctl apps list-deployments <app-id>
```

### GitHub Actions Status

1. Visit: https://github.com/o2alexanderfedin/hupyy-temporal/actions
2. Click on the latest workflow run
3. View detailed logs for each job

## Rollback Process

### Via Dashboard

1. Go to https://cloud.digitalocean.com/apps
2. Select your app
3. Go to "Deployments" tab
4. Click "Rollback" on a previous successful deployment

### Via CLI

```bash
# List deployments
doctl apps list-deployments <app-id>

# Rollback to specific deployment
doctl apps create-deployment <app-id> --deployment-id <deployment-id>
```

### Via Git

If you need to revert code changes:

```bash
# Revert the last commit
git revert HEAD
git push origin develop

# Or reset to a previous commit (use with caution!)
git reset --hard <commit-hash>
git push --force origin develop
```

## Troubleshooting

### Build Fails in GitHub Actions

**Problem**: Linting or type checking fails

**Solution**:
```bash
# Run locally before pushing
flake8 . --count --select=E9,F63,F7,F82 --show-source --statistics
mypy . --ignore-missing-imports

# Fix issues and push again
```

### Build Fails in App Platform

**Problem**: Docker build fails

**Solution**:
1. Check build logs in App Platform dashboard
2. Test Docker build locally:
   ```bash
   docker build -t test-image .
   docker run --rm test-image python --version
   ```
3. Fix Dockerfile and push

### Deployment Health Check Fails

**Problem**: App Platform shows "Health check failed"

**Solution**:
1. Check that health check endpoint is responding:
   ```bash
   curl https://your-app-url/_stcore/health
   ```
2. Increase `initial_delay_seconds` in `.do/app.yaml` if app needs more startup time
3. Check runtime logs for errors:
   ```bash
   doctl apps logs <app-id> --type run
   ```

### GitHub Authorization Required

**Problem**: "GitHub user not authenticated" error

**Solution**:
1. Visit https://cloud.digitalocean.com/apps
2. Click "Create App"
3. Select "GitHub" as source
4. Authorize Digital Ocean to access your GitHub account
5. Cancel the app creation (not needed, just authorization)
6. Try deployment again

## Environment Variables

### Adding New Environment Variables

1. **Via Dashboard**:
   - Go to App Platform dashboard
   - Select your app
   - Go to "Settings" → "App-Level Environment Variables"
   - Add new variable
   - Deploy to apply changes

2. **Via app.yaml**:
   ```yaml
   envs:
     - key: NEW_VARIABLE
       value: "some-value"
     # For secrets:
     - key: SECRET_VARIABLE
       scope: RUN_TIME
       type: SECRET
       value: "${SECRET_VARIABLE}"
   ```
   - Commit and push to GitHub

3. **Via CLI**:
   ```bash
   doctl apps update <app-id> --spec .do/app.yaml
   ```

## Scaling

### Vertical Scaling (More Resources)

Edit `.do/app.yaml`:
```yaml
instance_size_slug: basic-xxs  # Change to:
# basic-xs  ($12/mo)  - 1GB RAM, 1 vCPU
# basic-s   ($18/mo)  - 2GB RAM, 1 vCPU
# basic-m   ($42/mo)  - 4GB RAM, 2 vCPU
```

### Horizontal Scaling (More Instances)

Edit `.do/app.yaml`:
```yaml
instance_count: 1  # Change to 2, 3, etc.
```

Push changes to trigger redeployment.

## Cost Optimization

**Current Setup**: ~$6-7/month
- basic-xxs instance: $6/month
- Bandwidth: Included (1TB)
- Builds: Free

**Optimization Tips**:
1. Use Docker layer caching (already configured)
2. Minimize build dependencies
3. Use `.dockerignore` to exclude unnecessary files
4. Consider using build-time vs runtime dependencies

## Security Best Practices

1. **Secrets Management**:
   - Never commit secrets to Git
   - Use App Platform's secret management
   - Rotate secrets regularly

2. **Dependencies**:
   - Regularly update dependencies
   - Use `pip audit` to check for vulnerabilities
   - Pin versions in requirements.txt

3. **Access Control**:
   - Limit GitHub repository access
   - Use Digital Ocean teams for collaboration
   - Enable 2FA on both GitHub and Digital Ocean

## Further Reading

- [Digital Ocean App Platform Docs](https://docs.digitalocean.com/products/app-platform/)
- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Docker Best Practices](https://docs.docker.com/develop/dev-best-practices/)
- [Streamlit Deployment Guide](https://docs.streamlit.io/knowledge-base/deploy)

## Getting Help

- **App Platform Issues**: https://www.digitalocean.com/community/tags/app-platform
- **GitHub Actions**: https://github.community/
- **Project Issues**: https://github.com/o2alexanderfedin/hupyy-temporal/issues
