#!/bin/bash

# Wrapper script for creating GitHub releases with CI/CD monitoring reminder

# Check if gh is installed
if ! command -v gh &> /dev/null; then
    echo "Error: GitHub CLI (gh) is not installed"
    exit 1
fi

# Pass all arguments to gh release create
gh release create "$@"

RELEASE_EXIT_CODE=$?

if [ $RELEASE_EXIT_CODE -eq 0 ]; then
    echo ""
    echo "=========================================="
    echo "✅ Release created successfully!"
    echo "=========================================="
    echo ""
    echo "⚠️  REMINDER: Monitor CI/CD until deployment completes!"
    echo ""
    echo "Next steps:"
    echo "  1. Check workflow status:    gh run list --limit 5"
    echo "  2. Watch deployment:         gh run watch"
    echo "  3. View logs if needed:      gh run view --log"
    echo "  4. Verify health endpoint after deployment"
    echo ""
    echo "CI/CD Pipeline stages:"
    echo "  - Lint and Type Check"
    echo "  - Build Docker Image"
    echo "  - Deploy to Production"
    echo ""
    echo "Expected duration: ~5-6 minutes"
    echo "=========================================="
    echo ""
fi

exit $RELEASE_EXIT_CODE
