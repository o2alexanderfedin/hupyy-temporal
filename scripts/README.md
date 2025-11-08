# Scripts Directory

## Release Management

### `create-release.sh`

Wrapper script for creating GitHub releases with automatic CI/CD monitoring reminders.

**Usage:**

Instead of running `gh release create` directly, use this script:

```bash
./scripts/create-release.sh v2.5.1 --title "Release Title" --notes "Release notes" --target develop
```

**Features:**
- Passes all arguments to `gh release create`
- Displays CI/CD monitoring reminder after successful release creation
- Provides helpful commands for monitoring deployment
- Shows expected pipeline stages and duration

**Example:**

```bash
./scripts/create-release.sh v2.6.0 \
  --title "v2.6.0: New Feature" \
  --notes "Description of changes" \
  --target develop
```

After successful release creation, the script will remind you to:
1. Check workflow status
2. Watch deployment progress
3. Verify health endpoint after deployment

## Git Hooks

### `post-push.hook`

Automatically reminds you to monitor CI/CD when pushing tags manually.

**Installation:**

```bash
# Install the post-push hook
cp scripts/post-push.hook ../.git/modules/hupyy-temporal/hooks/post-push
chmod +x ../.git/modules/hupyy-temporal/hooks/post-push
```

**Triggered by:**
```bash
git tag v2.6.0
git push origin v2.6.0
```

When you push a tag, the hook will detect it and display a reminder to monitor the deployment.

**Note:** Git hooks are local and not tracked by version control. The hook source is kept in `scripts/post-push.hook` for reference and re-installation after cloning the repository.
