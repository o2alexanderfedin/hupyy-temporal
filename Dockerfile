# Hupyy Temporal - Production Docker Image
# Multi-stage build for optimal image size and security

# ============================================================================
# Stage 1: Builder - Install dependencies and prepare cvc5
# ============================================================================
FROM python:3.11-slim as builder

# Install build dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    ca-certificates \
    curl \
    wget \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /build

# Copy requirements and install Python dependencies
COPY requirements.txt ./
RUN pip install --no-cache-dir --user -r requirements.txt

# ============================================================================
# Stage 2: Runtime - Minimal production image
# ============================================================================
FROM python:3.11-slim

# Install runtime dependencies (Python, Node.js, cvc5, system libs)
# Note: cvc5 is installed from Debian repositories for ARM64 compatibility
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    libgmp10 \
    curl \
    gnupg \
    && mkdir -p /etc/apt/keyrings \
    && curl -fsSL https://deb.nodesource.com/gpgkey/nodesource-repo.gpg.key | gpg --dearmor -o /etc/apt/keyrings/nodesource.gpg \
    && echo "deb [signed-by=/etc/apt/keyrings/nodesource.gpg] https://deb.nodesource.com/node_20.x nodistro main" | tee /etc/apt/sources.list.d/nodesource.list \
    && apt-get update \
    && apt-get install -y --no-install-recommends nodejs cvc5 \
    && rm -rf /var/lib/apt/lists/*

# Install Claude CLI globally
RUN npm install -g @anthropic-ai/claude-code@^2.0.35

# Create non-root user for security
RUN useradd -m -u 1000 -s /bin/bash hupyy && \
    mkdir -p /app /app/reports /app/logs && \
    chown -R hupyy:hupyy /app

# Set working directory
WORKDIR /app

# Copy Python dependencies from builder
COPY --from=builder --chown=hupyy:hupyy /root/.local /home/hupyy/.local

# Copy application code (excluding bin/ directory which contains macOS binary)
COPY --chown=hupyy:hupyy . .

# Create reports and logs directories with correct permissions
RUN mkdir -p /app/reports /app/logs && \
    chown -R hupyy:hupyy /app/reports /app/logs

# Switch to non-root user
USER hupyy

# Add local bin and npm global bin to PATH
ENV PATH=/home/hupyy/.local/bin:/usr/local/bin:$PATH

# Set environment variables for Streamlit
ENV STREAMLIT_SERVER_HEADLESS=true \
    STREAMLIT_BROWSER_GATHERUSAGESTATS=false \
    STREAMLIT_SERVER_PORT=8501 \
    STREAMLIT_SERVER_ADDRESS=0.0.0.0 \
    STREAMLIT_SERVER_ENABLECORS=false \
    STREAMLIT_SERVER_ENABLEXSRFPROTECTION=true

# Note: cvc5 from Debian package is at /usr/bin/cvc5 (already in PATH)
# No custom library paths needed

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD python -c "import requests; requests.get('http://localhost:8501/_stcore/health')" || exit 1

# Expose Streamlit default port
EXPOSE 8501

# Run the application
CMD ["streamlit", "run", "demo/app.py", "--server.port=8501", "--server.address=0.0.0.0"]
