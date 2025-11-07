# Using Claude Subscription Authentication in Docker

Guide for using your $200/month Claude subscription instead of pay-as-you-go API in Docker deployments.

---

## Current Situation

**Current Setup (Expensive):**
- Using `ANTHROPIC_API_KEY` (API key: `sk-ant-api03-...`)
- Pay-as-you-go pricing: ~$3 per million input tokens, $15 per million output tokens
- **Cost**: Variable, potentially hundreds of dollars per month for heavy usage

**Your Subscription (Better Value):**
- Claude Pro: $20/month (or $17/month if paid annually = $200/year)
- Claude Max: $200/month (5x higher limits than Pro)
- **Cost**: Fixed monthly fee, unlimited usage within limits
- Same models available (Sonnet 4.5, Opus, etc.)

---

## Cost Comparison Example

### Scenario: 100M tokens/month usage

**Pay-as-you-go API:**
- Input: 100M tokens × $3/M = $300
- Output: 20M tokens × $15/M = $300
- **Total: $600/month**

**Claude Max Subscription:**
- **Total: $200/month (fixed)**
- **Savings: $400/month** 💰

Even with moderate usage (20M tokens/month), the subscription is cheaper than API!

---

## How It Works

### Authentication Methods in Claude CLI

Claude CLI supports two authentication methods:

1. **API Key** (Pay-as-you-go)
   - Environment variable: `ANTHROPIC_API_KEY`
   - Format: `sk-ant-api03-...`
   - Billing: Per token usage

2. **Subscription Token** (Fixed monthly cost) ✅ RECOMMENDED
   - Environment variable: `CLAUDE_CODE_OAUTH_TOKEN`
   - Format: `sk-ant-oat01-...` (OAuth token)
   - Billing: Your existing subscription

**Important**: If both are set, `ANTHROPIC_API_KEY` takes priority! Remove it to use subscription.

---

## Step-by-Step Setup

### Step 1: Generate OAuth Token (One-time)

Run this command on your **local machine** (macOS/Linux):

```bash
# This will open your browser to authenticate with Claude subscription
claude setup-token
```

**What happens:**
1. Opens browser to claude.ai
2. Logs in with your Claude Pro/Max subscription
3. Generates long-lived OAuth token
4. Saves token to `~/.claude/local/` directory

**Output example:**
```
✓ Token generated successfully!
Token: sk-ant-oat01-XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

This token has been saved and will be used by Claude CLI.
```

### Step 2: Copy Your OAuth Token

```bash
# Find your OAuth token
cat ~/.claude/local/credentials

# Or if stored elsewhere, check settings
cat ~/.claude/settings.json
```

**Save this token securely** - you'll need it for Docker!

---

## Docker Configuration

### Option A: Update Environment Variables (Recommended)

**Update your `.env` file:**

```bash
# OLD - Remove this line (pay-as-you-go API)
# ANTHROPIC_API_KEY=sk-ant-api03-...

# NEW - Use subscription OAuth token
CLAUDE_CODE_OAUTH_TOKEN=sk-ant-oat01-XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
CLAUDE_MODEL=claude-sonnet-3-5-20241022
TZ=UTC
```

**Update `docker-compose.yml`:**

```yaml
services:
  hupyy-temporal:
    image: hupyy-temporal:latest
    environment:
      # Use subscription OAuth token instead of API key
      - CLAUDE_CODE_OAUTH_TOKEN=${CLAUDE_CODE_OAUTH_TOKEN}
      - CLAUDE_MODEL=${CLAUDE_MODEL:-claude-sonnet-3-5-20241022}
      - TZ=${TZ:-UTC}
    # ... rest of config
```

**Restart container:**

```bash
docker compose down
docker compose up -d
```

### Option B: Pass Token Directly

For quick testing:

```bash
docker run -e CLAUDE_CODE_OAUTH_TOKEN="sk-ant-oat01-..." hupyy-temporal:latest
```

---

## Verification

### Test 1: Check Environment Variable

```bash
# Verify OAuth token is set
docker exec hupyy-temporal env | grep CLAUDE_CODE_OAUTH_TOKEN

# Verify API key is NOT set (should return nothing)
docker exec hupyy-temporal env | grep ANTHROPIC_API_KEY
```

### Test 2: Test Claude CLI

```bash
# Test subscription authentication
docker exec hupyy-temporal claude --print "Hello, test message"

# Should see response without any authentication errors
```

### Test 3: Check Application Logs

```bash
# Watch for authentication messages
docker logs hupyy-temporal -f

# Look for:
# ✓ "Using subscription authentication"
# ✗ "Using API key authentication" (old method)
```

---

## Token Management

### Token Lifecycle

- **Validity**: Long-lived (months, not days)
- **Regeneration**: Run `claude setup-token` again if expired
- **Security**: Treat like a password - never commit to git

### Token Expiration

If you see authentication errors:

```bash
# Regenerate token on local machine
claude setup-token

# Copy new token to .env file
nano .env  # Update CLAUDE_CODE_OAUTH_TOKEN

# Restart container
docker compose restart
```

### Security Best Practices

1. **Never commit tokens to git**
   ```bash
   # Verify .env is in .gitignore
   grep "^\.env$" .gitignore
   ```

2. **Restrict file permissions**
   ```bash
   chmod 600 .env
   ```

3. **Use different tokens for different environments**
   - Development: One token
   - Production: Another token
   - Rotate regularly (every 3-6 months)

4. **Monitor usage**
   - Check claude.ai dashboard for usage stats
   - Watch for unusual activity

---

## Comparison: API Key vs Subscription Token

| Feature | API Key (Current) | Subscription Token (Recommended) |
|---------|-------------------|----------------------------------|
| **Cost** | Pay per token | Fixed $200/month |
| **Billing** | Variable | Predictable |
| **Format** | `sk-ant-api03-...` | `sk-ant-oat01-...` |
| **Environment Variable** | `ANTHROPIC_API_KEY` | `CLAUDE_CODE_OAUTH_TOKEN` |
| **Usage Limits** | No limit (pay more) | Subscription limits |
| **Best For** | Variable/light usage | Heavy/consistent usage |
| **Setup Complexity** | Simple (just API key) | Medium (browser auth) |
| **Token Lifespan** | Permanent (until revoked) | Long-lived (months) |

---

## Digital Ocean Deployment

### Update Deployment Guide

When deploying to Digital Ocean, use subscription authentication:

```bash
# On Digital Ocean Droplet
cd /opt/hupyy-temporal

# Edit .env file
nano .env

# Replace ANTHROPIC_API_KEY with CLAUDE_CODE_OAUTH_TOKEN
CLAUDE_CODE_OAUTH_TOKEN=sk-ant-oat01-XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
CLAUDE_MODEL=claude-sonnet-3-5-20241022
TZ=UTC

# Save and restart
docker compose down
docker compose pull
docker compose up -d
```

### Secure Storage Options

For production, consider using Digital Ocean secrets management:

1. **Environment Variables in Droplet**
   ```bash
   # Add to /etc/environment (system-wide)
   echo 'CLAUDE_CODE_OAUTH_TOKEN="sk-ant-oat01-..."' >> /etc/environment
   ```

2. **Docker Secrets** (Docker Swarm)
   ```bash
   echo "sk-ant-oat01-..." | docker secret create claude_token -
   ```

3. **External Secrets Manager**
   - HashiCorp Vault
   - AWS Secrets Manager
   - 1Password Secrets Automation

---

## Troubleshooting

### Error: "Authentication failed"

**Cause**: Token expired or invalid

**Solution**:
```bash
# Regenerate token locally
claude setup-token

# Update .env with new token
# Restart container
docker compose restart
```

### Error: "Rate limit exceeded"

**Cause**: Subscription limits reached

**Solutions**:
1. Check usage at claude.ai/account
2. Wait for limit reset (daily/hourly)
3. Upgrade to Claude Max ($200/month) for 20x higher limits
4. Temporarily switch to API key for burst needs

### Container Still Using API Key

**Cause**: Both variables set, API key takes priority

**Solution**:
```bash
# Remove API key from .env
sed -i '/ANTHROPIC_API_KEY/d' .env

# Or comment it out
# ANTHROPIC_API_KEY=sk-ant-api03-...

# Restart container
docker compose restart
```

### Token Not Found in Container

**Cause**: Environment variable not passed to container

**Solution**:
```bash
# Check docker-compose.yml has CLAUDE_CODE_OAUTH_TOKEN
grep "CLAUDE_CODE_OAUTH_TOKEN" docker-compose.yml

# Check .env file exists and has token
cat .env | grep CLAUDE_CODE_OAUTH_TOKEN

# Recreate container with new env vars
docker compose up -d --force-recreate
```

---

## Migration Checklist

### Pre-Migration

- [ ] Verify you have Claude Pro or Max subscription
- [ ] Run `claude setup-token` locally
- [ ] Save OAuth token securely
- [ ] Test token works locally: `claude --print "test"`

### Migration

- [ ] Update `.env` file with `CLAUDE_CODE_OAUTH_TOKEN`
- [ ] Remove or comment out `ANTHROPIC_API_KEY`
- [ ] Update `docker-compose.yml` if needed
- [ ] Restart container: `docker compose restart`

### Post-Migration

- [ ] Verify container uses subscription: Check logs
- [ ] Test application functionality
- [ ] Monitor usage at claude.ai/account
- [ ] Document token location securely
- [ ] Set calendar reminder to regenerate token (3 months)

---

## Cost Savings Summary

### Your Current Setup

**Subscription**: $200/month (Claude Max or Pro annual)
**API Usage**: Variable, potentially $0-1000+/month

### After Migration

**Subscription**: $200/month (same)
**API Usage**: $0/month ✅

**Potential Savings**: $200-1000+/month

### Break-Even Analysis

If your monthly API usage is:
- **< $20/month**: Keep API key, don't need subscription
- **> $20/month**: Use subscription, you're already saving money
- **> $200/month**: You MUST switch to subscription immediately! 🚨

---

## Quick Reference Commands

```bash
# Generate subscription token
claude setup-token

# Check current authentication method
docker exec hupyy-temporal env | grep -E "(CLAUDE_CODE_OAUTH_TOKEN|ANTHROPIC_API_KEY)"

# Test Claude CLI with subscription
docker exec hupyy-temporal claude --print "test message"

# View container logs for auth info
docker logs hupyy-temporal | grep -i auth

# Update .env and restart
nano .env
docker compose restart

# Force recreate with new environment
docker compose up -d --force-recreate
```

---

## Support Resources

- **Claude CLI Docs**: https://docs.claude.com/en/docs/claude-code
- **Subscription Plans**: https://claude.ai/settings/billing
- **Usage Dashboard**: https://claude.ai/account
- **Token Management**: `claude setup-token --help`

---

## Next Steps

1. **Generate your OAuth token** right now:
   ```bash
   claude setup-token
   ```

2. **Update your local Docker** to test:
   - Update `.env` with `CLAUDE_CODE_OAUTH_TOKEN`
   - Remove `ANTHROPIC_API_KEY`
   - Restart: `docker compose restart`

3. **Verify it works** before deploying to production

4. **Deploy to Digital Ocean** with subscription auth

5. **Monitor savings** - track your API usage dropping to $0

**Estimated Time**: 10-15 minutes
**Estimated Savings**: $200-1000+/month

---

**Document Version**: 1.0
**Last Updated**: 2025-11-07
**Maintained By**: Hupyy Temporal Team
