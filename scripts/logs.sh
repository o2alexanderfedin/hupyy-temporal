#!/bin/bash
# Log viewing helper script for Hupyy Temporal Docker deployment

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_ROOT"

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

show_help() {
    echo "Hupyy Temporal Log Viewer"
    echo ""
    echo "Usage: $0 [command] [options]"
    echo ""
    echo "Commands:"
    echo "  docker        View Docker container logs (default)"
    echo "  app           View application logs from logs/ directory"
    echo "  follow        Follow Docker logs in real-time"
    echo "  tail [N]      Show last N lines of Docker logs (default: 100)"
    echo "  today         Show today's application log file"
    echo "  list          List all available log files"
    echo "  clean         Remove old log files (keeps last 7 days)"
    echo ""
    echo "Examples:"
    echo "  $0                    # View recent Docker logs"
    echo "  $0 follow             # Follow logs in real-time"
    echo "  $0 tail 200           # Show last 200 lines"
    echo "  $0 app                # View application logs"
    echo "  $0 today              # View today's application log"
}

view_docker_logs() {
    echo -e "${BLUE}📋 Docker Container Logs${NC}"
    docker compose logs --tail=100
}

follow_docker_logs() {
    echo -e "${BLUE}📋 Following Docker Logs (Ctrl+C to stop)${NC}"
    docker compose logs -f
}

tail_docker_logs() {
    local lines=${1:-100}
    echo -e "${BLUE}📋 Last ${lines} lines of Docker logs${NC}"
    docker compose logs --tail="$lines"
}

view_app_logs() {
    echo -e "${BLUE}📋 Application Logs Directory${NC}"
    if [ -d "./logs" ]; then
        ls -lh ./logs/*.log 2>/dev/null || echo "No log files found"
    else
        echo "Logs directory not found"
    fi
}

view_today_log() {
    local today=$(date +%Y%m%d)
    local logfile="./logs/hupyy_${today}.log"

    echo -e "${BLUE}📋 Today's Application Log: ${logfile}${NC}"
    if [ -f "$logfile" ]; then
        tail -100 "$logfile"
    else
        echo "No log file for today yet"
    fi
}

list_logs() {
    echo -e "${BLUE}📋 Available Log Files${NC}"
    echo ""
    echo -e "${YELLOW}Application Logs (./logs/):${NC}"
    ls -lh ./logs/*.log 2>/dev/null || echo "No application log files"
    echo ""
    echo -e "${YELLOW}Docker Logs:${NC}"
    docker compose ps
}

clean_old_logs() {
    echo -e "${BLUE}🧹 Cleaning old log files (keeping last 7 days)${NC}"
    find ./logs -name "*.log" -type f -mtime +7 -delete 2>/dev/null
    echo -e "${GREEN}✓ Cleanup complete${NC}"
}

# Main command dispatcher
case "${1:-docker}" in
    help|-h|--help)
        show_help
        ;;
    docker)
        view_docker_logs
        ;;
    follow|-f)
        follow_docker_logs
        ;;
    tail)
        tail_docker_logs "$2"
        ;;
    app)
        view_app_logs
        ;;
    today)
        view_today_log
        ;;
    list|ls)
        list_logs
        ;;
    clean)
        clean_old_logs
        ;;
    *)
        echo -e "${YELLOW}Unknown command: $1${NC}"
        echo ""
        show_help
        exit 1
        ;;
esac
