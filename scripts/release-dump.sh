#!/usr/bin/env bash
#
# release-dump.sh — write a release manifest describing a Meridian dump.
#
# Usage:
#   ./scripts/release-dump.sh <dump.ttl> <manifest.json>
#
# The manifest captures: dump path, sizes (raw + gzip), SHA-256 (raw + gzip),
# Lean toolchain string, Mathlib commit (if available), git HEAD of this repo,
# triple count (extracted from the Lean log if accessible), and timestamp.

set -euo pipefail

DUMP="${1:?usage: $0 <dump.ttl> <manifest.json>}"
MANIFEST="${2:?usage: $0 <dump.ttl> <manifest.json>}"
DUMP_GZ="${DUMP}.gz"

if [[ ! -f "${DUMP}" ]]; then
  echo "error: dump not found: ${DUMP}" >&2
  exit 1
fi
if [[ ! -f "${DUMP_GZ}" ]]; then
  echo "error: gzip not found (run 'gzip -k ${DUMP}' first): ${DUMP_GZ}" >&2
  exit 1
fi

REPO="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"

raw_size="$(stat -c%s "${DUMP}")"
gz_size="$(stat -c%s "${DUMP_GZ}")"
raw_sha="$(sha256sum "${DUMP}" | awk '{print $1}')"
gz_sha="$(sha256sum "${DUMP_GZ}" | awk '{print $1}')"

git_head="$(git -C "${REPO}" rev-parse HEAD 2>/dev/null || echo "unknown")"
git_branch="$(git -C "${REPO}" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown")"

mathlib_commit="$(awk -F'"' '/^rev = /{print $2; exit}' "${REPO}/lakefile.toml" 2>/dev/null || echo "unknown")"
lean_toolchain="$(cat "${REPO}/lean-toolchain" 2>/dev/null || echo "unknown")"

iso_now="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"

cat > "${MANIFEST}" <<JSON
{
  "tool": "meridian-export-rdf",
  "generated_at": "${iso_now}",
  "lean_toolchain": "${lean_toolchain}",
  "mathlib_commit": "${mathlib_commit}",
  "meridian_git_head": "${git_head}",
  "meridian_git_branch": "${git_branch}",
  "dump": {
    "path": "$(basename "${DUMP}")",
    "size_bytes": ${raw_size},
    "sha256": "${raw_sha}"
  },
  "dump_gz": {
    "path": "$(basename "${DUMP_GZ}")",
    "size_bytes": ${gz_size},
    "sha256": "${gz_sha}"
  }
}
JSON

echo "wrote manifest: ${MANIFEST}"
cat "${MANIFEST}"
