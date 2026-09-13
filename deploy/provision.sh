#!/usr/bin/env bash
# Provision a fresh Ubuntu VM for the MathProver API.
# Run as root. Re-runnable. Read it before running it.
set -euo pipefail

DOMAIN="${DOMAIN:-api.example.com}"
REPO="${REPO:-https://github.com/willyzhang109/MathProver.git}"
HOME_DIR=/srv/mathprover
APP="$HOME_DIR/MathProverProject"

echo "==> 1. system packages"
apt-get update
apt-get install -y git curl build-essential nginx certbot python3-certbot-nginx \
                   python3-venv python3-pip

echo "==> 2. unprivileged service account"
id -u mathprover >/dev/null 2>&1 || \
  adduser --system --group --home "$HOME_DIR" --shell /usr/sbin/nologin mathprover
mkdir -p "$HOME_DIR/cache" /etc/mathprover
chown -R mathprover:mathprover "$HOME_DIR"

echo "==> 3. clone"
if [ ! -d "$APP/.git" ]; then
  sudo -u mathprover git clone "$REPO" "$APP"
else
  sudo -u mathprover git -C "$APP" pull --ff-only
fi

echo "==> 4. elan + Lean toolchain (reads lean-toolchain: v4.27.0)"
sudo -u mathprover bash -lc "
  test -x $HOME_DIR/.elan/bin/lake || \
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
  export PATH=$HOME_DIR/.elan/bin:\$PATH
  cd $APP && lake --version
"

echo "==> 5. Mathlib cache + build (10-30 min, ~10 GB)"
# The existing CI workflow never does this -- it relies on the prover's
# compile_lean_file() prelude, which the server deliberately skips.
sudo -u mathprover bash -lc "
  export PATH=$HOME_DIR/.elan/bin:\$PATH
  cd $APP
  lake exe cache get
  lake build
"

echo "==> 6. build safe_verify (has never been built in this repo)"
sudo -u mathprover bash -lc "
  export PATH=$HOME_DIR/.elan/bin:\$PATH
  cd $APP && lake build safe_verify
"
test -x "$APP/SafeVerify/.lake/build/bin/safe_verify" \
  || { echo "FATAL: safe_verify was not produced"; exit 1; }
"$APP/SafeVerify/.lake/build/bin/safe_verify" --help >/dev/null \
  && echo "    safe_verify OK"

echo "==> 7. python environment"
sudo -u mathprover bash -lc "
  export PATH=$HOME_DIR/.elan/bin:\$PATH
  cd $APP
  python3 -m venv .venv
  .venv/bin/pip install -q --upgrade pip
  .venv/bin/pip install -q uv
  mkdir -p dist && cd PyPantograph && ../.venv/bin/uv build --wheel --out-dir ../dist && cd ..
  .venv/bin/pip install -q \$(find ./dist -name '*.whl' | head -1)
  .venv/bin/pip install -q -r requirements.txt -r requirements-server.txt
"

echo "==> 8. environment file"
if [ ! -f /etc/mathprover/server.env ]; then
  install -m 0600 -o root -g mathprover "$APP/deploy/server.env.example" \
    /etc/mathprover/server.env
  # Capture the Lean paths the API needs to invoke `lean` directly.
  sudo -u mathprover bash -lc "
    export PATH=$HOME_DIR/.elan/bin:\$PATH; cd $APP
    echo LEAN_PATH=\$(lake env printenv LEAN_PATH)
    echo PATH=$HOME_DIR/.elan/bin:/usr/local/bin:/usr/bin:/bin
  " >> /etc/mathprover/server.env
  echo "    !! edit /etc/mathprover/server.env and set a FRESH GEMINI_API_KEY"
fi

echo "==> 9. measure one Mathlib-resident process before choosing capacity"
sudo -u mathprover bash -lc "
  export PATH=$HOME_DIR/.elan/bin:\$PATH; cd $APP
  .venv/bin/python -c \"
import asyncio, os, resource, pantograph
async def m():
    s = await pantograph.Server.create(project_path='.', imports=['Init','Mathlib'])
    print('peak RSS of this process: %.1f GB' % (resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1e9))
asyncio.run(m())
\" || true
"
echo "    Size MemoryMax for (MAX_CONCURRENT_JOBS * PROVER_NUM_PROCS + CHECKER_POOL_SIZE)"
echo "    processes of roughly that size."

echo "==> 10. systemd"
install -m 0644 "$APP/deploy/mathprover-api.service" /etc/systemd/system/
systemctl daemon-reload
systemctl enable --now mathprover-api
sleep 5
systemctl --no-pager --lines=15 status mathprover-api || true

echo "==> 11. nginx + TLS"
sed "s/api\.example\.com/$DOMAIN/g" "$APP/deploy/nginx/mathprover.conf" \
  > /etc/nginx/sites-available/mathprover
ln -sf /etc/nginx/sites-available/mathprover /etc/nginx/sites-enabled/mathprover
rm -f /etc/nginx/sites-enabled/default
certbot --nginx -d "$DOMAIN" --non-interactive --agree-tos \
  -m "admin@$DOMAIN" --redirect || echo "    certbot failed; run it manually"
nginx -t && systemctl reload nginx

cat <<DONE

Done. Remaining manual steps:
  1. Put a FRESH Gemini key in /etc/mathprover/server.env, then
     systemctl restart mathprover-api
  2. Set the repository variable API_BASE_URL to https://$DOMAIN
     (Settings -> Secrets and variables -> Actions -> Variables), then run the
     "Deploy site to Pages" workflow.
  3. Checkers take ~100s each to import Mathlib. /api/health reports readiness:
       curl https://$DOMAIN/api/health
DONE
