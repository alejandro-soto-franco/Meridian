#!/usr/bin/env bash
#
# load-fuseki.sh — start an Apache Jena Fuseki container and load a Meridian
# Turtle dump into a TDB2 dataset, then leave the SPARQL endpoint listening.
#
# Usage:
#   ./scripts/load-fuseki.sh path/to/dump.ttl [dataset-name] [port]
#
# Defaults: dataset-name=meridian, port=3030
#
# Endpoints once running:
#   http://localhost:<port>/<dataset-name>/sparql   (SPARQL 1.1 query)
#   http://localhost:<port>/<dataset-name>/update   (SPARQL 1.1 update)
#   http://localhost:<port>/                        (web UI, admin/admin)
#
# Requires: docker (or podman aliased to docker).
#

set -euo pipefail

DUMP="${1:-}"
DATASET="${2:-meridian}"
PORT="${3:-3030}"
CONTAINER="meridian-fuseki"
IMAGE="stain/jena-fuseki:5.0.0"

if [[ -z "${DUMP}" || ! -f "${DUMP}" ]]; then
  echo "usage: $0 <dump.ttl> [dataset-name] [port]" >&2
  echo "error: dump file not found: ${DUMP}" >&2
  exit 1
fi

ABS_DUMP="$(readlink -f "${DUMP}")"
DUMP_DIR="$(dirname "${ABS_DUMP}")"
DUMP_FILE="$(basename "${ABS_DUMP}")"

echo "==> Stopping any existing container named ${CONTAINER}"
docker rm -f "${CONTAINER}" >/dev/null 2>&1 || true

echo "==> Starting Fuseki container on port ${PORT}, dataset ${DATASET}"
docker run -d \
  --name "${CONTAINER}" \
  -p "${PORT}:3030" \
  -e ADMIN_PASSWORD=admin \
  -e FUSEKI_DATASET_1="${DATASET}" \
  -v "${DUMP_DIR}:/staging:ro" \
  "${IMAGE}" \
  >/dev/null

echo "==> Waiting for Fuseki to come up"
for i in $(seq 1 30); do
  if curl -fsS "http://localhost:${PORT}/$/ping" >/dev/null 2>&1; then
    break
  fi
  sleep 1
done

echo "==> Loading ${DUMP_FILE} into dataset ${DATASET}"
curl -fsS \
  -u "admin:admin" \
  -H "Content-Type: text/turtle" \
  --data-binary "@${ABS_DUMP}" \
  "http://localhost:${PORT}/${DATASET}/data" \
  >/dev/null

echo
echo "Fuseki is ready."
echo "  SPARQL query: http://localhost:${PORT}/${DATASET}/sparql"
echo "  Web UI:       http://localhost:${PORT}/  (admin/admin)"
echo
echo "Try one of the example queries:"
echo "  curl -fsS -H 'Accept: application/sparql-results+json' \\"
echo "    --data-urlencode \"query=\$(cat examples/sparql/01-namespace-counts.sparql)\" \\"
echo "    http://localhost:${PORT}/${DATASET}/sparql | jq ."
