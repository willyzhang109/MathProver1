#!/usr/bin/env bash
# Compute Engine startup script.
#   gcloud compute instances create ... \
#     --metadata-from-file=startup-script=deploy/docker/vm-startup.sh
#
# Required instance metadata: image, domain, cors-origins, gemini-secret
# Optional:                   max-concurrent-jobs, prover-num-procs,
#                             checker-pool-size, mem-limit, cpus
#
# Output goes to the serial console:
#   gcloud compute instances get-serial-port-output mathprover --zone=...
set -euo pipefail
exec > >(tee -a /var/log/mathprover-startup.log | logger -t mathprover -s 2>/dev/console) 2>&1

say() { echo "=== [$(date -Is)] $*"; }

meta() {
  curl -sf -H "Metadata-Flavor: Google" \
    "http://metadata.google.internal/computeMetadata/v1/instance/attributes/$1" || true
}

IMAGE="$(meta image)"
DOMAIN="$(meta domain)"
CORS_ORIGINS="$(meta cors-origins)"
SECRET="$(meta gemini-secret)"

for v in IMAGE DOMAIN CORS_ORIGINS SECRET; do
  [ -n "${!v}" ] || { say "FATAL: instance metadata for $v is missing"; exit 1; }
done
say "image=$IMAGE domain=$DOMAIN"

# --- docker ------------------------------------------------------------------
if ! command -v docker >/dev/null; then
  say "installing docker"
  curl -fsSL https://get.docker.com | sh          # includes the compose plugin
fi
docker compose version >/dev/null || { say "FATAL: docker compose plugin missing"; exit 1; }

# --- gcloud ------------------------------------------------------------------
# Present on Google's Ubuntu/Debian images, but do not assume it.
if ! command -v gcloud >/dev/null; then
  say "installing google-cloud-cli"
  apt-get update -qq
  apt-get install -y -qq apt-transport-https ca-certificates gnupg curl
  curl -fsSL https://packages.cloud.google.com/apt/doc/apt-key.gpg \
    | gpg --dearmor -o /usr/share/keyrings/cloud.google.gpg
  echo "deb [signed-by=/usr/share/keyrings/cloud.google.gpg] \
https://packages.cloud.google.com/apt cloud-sdk main" \
    > /etc/apt/sources.list.d/google-cloud-sdk.list
  apt-get update -qq && apt-get install -y -qq google-cloud-cli
fi

# --- block the metadata server for containers --------------------------------
# Untrusted Lean runs inside the container. 169.254.169.254 hands out this VM's
# service-account tokens to anything that can make an HTTP request. Do this
# BEFORE starting any container.
say "blocking container egress to the metadata server"
iptables -C DOCKER-USER -d 169.254.169.254 -j DROP 2>/dev/null \
  || iptables -I DOCKER-USER -d 169.254.169.254 -j DROP 2>/dev/null \
  || iptables -I FORWARD -d 169.254.169.254 -j DROP

# --- secret ------------------------------------------------------------------
say "reading $SECRET from Secret Manager"
GEMINI_API_KEY="$(gcloud secrets versions access latest --secret="$SECRET")"
[ -n "$GEMINI_API_KEY" ] || { say "FATAL: secret $SECRET is empty"; exit 1; }

# --- image -------------------------------------------------------------------
install -d -m 0750 /opt/mathprover
cd /opt/mathprover
gcloud auth configure-docker "${IMAGE%%/*}" --quiet
say "pulling image (12-18 GB, several minutes)"
for attempt in 1 2 3; do
  docker pull "$IMAGE" && break
  say "pull failed (attempt $attempt), retrying in 20s"
  sleep 20
done

# compose.yaml and Caddyfile ship inside the image so the host needs no checkout
CID="$(docker create "$IMAGE")"
docker cp "$CID:/srv/mathprover/app/deploy/docker/compose.yaml" ./compose.yaml
docker cp "$CID:/srv/mathprover/app/deploy/docker/Caddyfile" ./Caddyfile
docker rm "$CID" >/dev/null

cat > .env <<ENVEOF
IMAGE=$IMAGE
DOMAIN=$DOMAIN
CORS_ORIGINS=$CORS_ORIGINS
GEMINI_API_KEY=$GEMINI_API_KEY
MAX_CONCURRENT_JOBS=$(meta max-concurrent-jobs || true)
PROVER_NUM_PROCS=$(meta prover-num-procs || true)
CHECKER_POOL_SIZE=$(meta checker-pool-size || true)
MEM_LIMIT=$(meta mem-limit || true)
CPUS=$(meta cpus || true)
ENVEOF
# Drop keys whose metadata was absent so compose falls back to its defaults.
sed -i '/=$/d' .env
chmod 0600 .env

say "starting containers"
docker compose --env-file .env up -d
docker compose ps
say "done. checkers need ~2 minutes to import Mathlib; watch /api/health"
