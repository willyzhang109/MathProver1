# Running the API in a container on GCP

## Use Compute Engine, not Cloud Run

Cloud Run is the obvious choice for "a container on GCP" and it is the wrong one
here. Four independent reasons, any one of which is fatal:

- **State is in memory.** Jobs, rate-limit counters and the checker pool live in
  the process. Cloud Run scales horizontally and recycles instances freely, so
  users would lose jobs mid-run and each replica would enforce its own separate
  3-per-hour limit.
- **Work continues between requests.** A job runs for up to 20 minutes after the
  POST that created it has returned. Cloud Run throttles CPU to near zero
  outside a request unless CPU is always allocated, which stalls the asyncio job
  workers and the tailer.
- **Memory ceiling.** Cloud Run tops out at 32 GiB per instance. Even a modest
  configuration wants more than that once several Mathlib-resident processes are
  live.
- **Cold start.** Each checker takes ~100 s to import Mathlib. Scale-to-zero
  means the first visitor after an idle period waits minutes.

GKE has the same in-memory-state problem plus more machinery. A single Compute
Engine VM running the container is the right shape: one long-lived instance,
large memory, no autoscaling.

## Prerequisites

- A domain name (the Pages site is HTTPS, so the API must be too).
- A GCP project with billing, and `gcloud` authenticated locally.
- A **fresh** Gemini key — the old one is in this repo's git history.

## 1. Artifact Registry

```bash
gcloud config set project YOUR_PROJECT
gcloud services enable artifactregistry.googleapis.com cloudbuild.googleapis.com \
                        secretmanager.googleapis.com compute.googleapis.com

gcloud artifacts repositories create mathprover \
  --repository-format=docker --location=us-central1
```

## 2. Build the image

Build in Cloud Build, not locally: the image is 12-18 GB (Mathlib's oleans are
baked in so the container boots without network fetches), and pushing that from
a laptop is painful.

```bash
gcloud builds submit --config deploy/docker/cloudbuild.yaml .
```

`.dockerignore` keeps the upload at ~164 MB instead of 15 GB by excluding
`.lake`, `.venv` and the scratch files. The build itself takes 30-60 minutes,
almost all of it `lake exe cache get` and `lake build safe_verify`; the config
requests a 250 GB build disk and a 90-minute timeout because the defaults are
far too small.

Layer order means later code-only changes rebuild in a minute or two — Mathlib
is built before any application code is copied.

## 3. Store the API key

```bash
printf '%s' 'YOUR_FRESH_GEMINI_KEY' | \
  gcloud secrets create gemini-api-key --data-file=-
```

## 4. Create the VM

Give it a service account with **no roles** beyond reading that secret and
pulling images. Untrusted Lean executes at elaboration time, so assume the
container is reachable by an attacker.

```bash
gcloud iam service-accounts create mathprover-vm
SA="mathprover-vm@$(gcloud config get-value project).iam.gserviceaccount.com"

gcloud secrets add-iam-policy-binding gemini-api-key \
  --member="serviceAccount:$SA" --role=roles/secretmanager.secretAccessor
gcloud projects add-iam-policy-binding "$(gcloud config get-value project)" \
  --member="serviceAccount:$SA" --role=roles/artifactregistry.reader

gcloud compute addresses create mathprover-ip --region=us-central1

IMAGE="us-central1-docker.pkg.dev/$(gcloud config get-value project)/mathprover/api:latest"

gcloud compute instances create mathprover \
  --zone=us-central1-a \
  --machine-type=n2-highmem-8 \
  --boot-disk-size=200GB --boot-disk-type=pd-balanced \
  --image-family=ubuntu-2204-lts --image-project=ubuntu-os-cloud \
  --address=mathprover-ip \
  --service-account="$SA" \
  --scopes=https://www.googleapis.com/auth/cloud-platform \
  --tags=https-server,http-server \
  --metadata=image="$IMAGE",domain=api.yourdomain.com,\
cors-origins=https://willyzhang109.github.io,gemini-secret=gemini-api-key \
  --metadata-from-file=startup-script=deploy/docker/vm-startup.sh

gcloud compute firewall-rules create allow-web \
  --allow=tcp:80,tcp:443 --target-tags=https-server,http-server
```

**If the create fails with `ZONE_RESOURCE_POOL_EXHAUSTED`**, the zone is simply
out of that machine type -- it is not a quota or configuration problem. The
reserved IP is regional, so any zone in the same region works unchanged. Loop
over zones and families until one lands:

```bash
for Z in us-central1-a us-central1-b us-central1-c us-central1-f; do
  for MT in n2-highmem-8 e2-highmem-8 n2d-highmem-8; do
    gcloud compute instances create mathprover --zone=$Z --machine-type=$MT ... \
      && { export ZONE=$Z; break 2; }
  done
done
```

All three types are 64 GB / 8 vCPU; `e2` draws from a separate, usually roomier
pool. Remember to re-export `ZONE` -- every later command needs the zone the
instance actually landed in.

**Sizing.** `n2-highmem-8` is 64 GB, which comfortably fits the defaults in
`compose.yaml` (`MAX_CONCURRENT_JOBS=2 × PROVER_NUM_PROCS=2` plus
`CHECKER_POOL_SIZE=2`, so six Mathlib-resident processes). Watch real usage
before raising those — `docker stats` and `ps -o rss` on the VM.

## 5. DNS, then wait for warm-up

Point an `A` record for `api.yourdomain.com` at the reserved IP. Caddy gets a
certificate automatically on first request.

```bash
curl https://api.yourdomain.com/api/health
```

Wait for `checkers_ready` to be non-zero — roughly two minutes after boot.
Until then `/api/lean/check` returns 503 `checker_warming`.

## 6. Deploy the site

Unchanged from the VM path: set the repository variable `API_BASE_URL` to
`https://api.yourdomain.com`, set Pages source to GitHub Actions, and run the
**Deploy site to Pages** workflow.

## Updating

```bash
gcloud builds submit --config deploy/docker/cloudbuild.yaml .
gcloud compute ssh mathprover --zone=us-central1-a --command \
  'cd /opt/mathprover && sudo docker compose pull && sudo docker compose up -d'
```

A redeploy drops running jobs — state is in memory by design. The container's
90-second stop grace period lets the shutdown hook kill child process groups
first, so no orphaned `pantograph-repl` survives.

## Container-specific details worth knowing

- **`TRUSTED_PROXIES` is `172.28.0.0/16`, not `127.0.0.1/32`.** Inside Docker the
  reverse proxy is another container on the bridge network. Leaving the default
  would make every request appear to come from Caddy, collapsing all users into
  a single rate-limit bucket. The subnet is pinned in `compose.yaml` so this
  stays deterministic.
- **`init: true` is required.** The prover forks `multiprocessing` children; with
  uvicorn as PID 1 nothing reaps them and defunct entries accumulate.
- **The metadata server is blocked** by an iptables rule in the startup script.
  `169.254.169.254` hands out this VM's service-account tokens to anything that
  can make an HTTP request, and the container runs untrusted Lean. The
  no-roles service account is the second layer.
- **Never scale to more than one `api` replica**, for the same in-memory-state
  reason Cloud Run is unsuitable.
- The container runs as uid 1000 (`prover`), with `cap_drop: ALL` and
  `no-new-privileges`. The root filesystem is left writable because Lean writes
  trace files into `.lake`.
