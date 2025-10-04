FROM python:3.11-slim

# system deps (tzdata for reproducible time, build tools if needed)
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential ca-certificates && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY requirements.txt ./
RUN pip install --no-cache-dir -r requirements.txt

COPY . ./

# good defaults for Streamlit in containers
ENV STREAMLIT_SERVER_HEADLESS=true \
    STREAMLIT_BROWSER_GATHERUSAGESTATS=false

EXPOSE 8501
CMD ["streamlit", "run", "demo/app.py"]
