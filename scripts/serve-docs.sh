#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VENV="$ROOT/.venv-docs"

if [ ! -d "$VENV" ]; then
  python3 -m venv "$VENV"
fi

# shellcheck source=/dev/null
source "$VENV/bin/activate"

python -m pip install --upgrade pip
python -m pip install -r "$ROOT/requirements-docs.txt"

cd "$ROOT"
exec mkdocs serve "$@"
