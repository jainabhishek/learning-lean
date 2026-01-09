#!/bin/bash
# Codex Coding Subagent Wrapper
# Usage: ./.codex-agent.sh "task description" [sandbox-mode]
# Sandbox modes: read-only (default), workspace-write, danger-full-access

set -e

PROMPT="$1"
SANDBOX="${2:-workspace-write}"

if [ -z "$PROMPT" ]; then
    echo "Usage: $0 \"task description\" [sandbox-mode]"
    echo "Sandbox modes: read-only, workspace-write, danger-full-access"
    exit 1
fi

echo "=== Codex Subagent ==="
echo "Task: $PROMPT"
echo "Sandbox: $SANDBOX"
echo "======================"

codex exec "$PROMPT" \
    --sandbox "$SANDBOX" \
    --full-auto \
    2>&1
