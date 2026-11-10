#!/usr/bin/env bash
# run-A.sh: Run A of rsbounds-20261109-full, per LAPTOP-COMPARATOR.md steps 0 to 4.
#
# HOW TO RUN, from Windows PowerShell or cmd:
#   1. Keep everything on the Linux filesystem, NOT under /mnt/c. Lean on /mnt/c is many times
#      slower and file locking there is unreliable. Copy the tarball in once:
#        wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/ra-runA && cp /mnt~/ra/full.tgz ~/ra-runA/rsbounds-20261109-full.tar.gz && cp /mnt~/ra/out/run-A.sh ~/ra-runA/ && chmod +x ~/ra-runA/run-A.sh'
#   2. Start it, and leave this window open. Closing it lets WSL shut the VM down:
#        wsl -d Ubuntu-24.04 -- bash -lc '~/ra-runA/run-A.sh'
#      An explicit tarball path is accepted as the first argument, or as TARBALL=... in the env.
#   3. After a reboot or a kill, run the same command again. Finished steps are skipped,
#      the build is rerun and Lake resumes where it stopped.
#   Logs: ~/ra-runA/logs/  (from Windows: \\wsl$\Ubuntu-24.04\home\<user>\ra-runA\logs)
#
# Needs: elan, git, curl, bubblewrap, and GNU time (sudo apt install bubblewrap time).
# This script deletes nothing.

set -u
set -o pipefail

RUNA="${RUNA:-$HOME/ra-runA}"
TARBALL="${1:-${TARBALL:-$RUNA/rsbounds-20261109-full.tar.gz}}"
EXPECTED_SHA="b7d5c861bb1a7045d2a7b896ab9dd5a1d873cca4e463b739bbb140ffad71e8ed"
WORK="$RUNA/work"                                  # fresh dir the tarball is unpacked into
PROJ="$WORK/rsbounds-20261109-full/RSBounds-project"
LOGS="$RUNA/logs"
MARK="$RUNA/markers"
JOBS="${JOBS:-10}"

mkdir -p "$RUNA" "$LOGS" "$MARK"

export LEAN_NUM_THREADS=$JOBS

# Pin all work to 10 of the 12 logical CPUs. This holds whether or not Lake honours a job limit.
PIN=()
if command -v taskset >/dev/null 2>&1 && [ "$(nproc --all)" -gt "$JOBS" ]; then
  PIN=(taskset -c "0-$((JOBS - 1))")
fi

ts()  { date '+%Y-%m-%d %H:%M:%S %Z'; }
say() { echo "[$(ts)] $*" | tee -a "$LOGS/run-A.log"; }

sysinfo() {
  {
    echo "=== $(ts)"
    uname -a
    echo "nproc: $(nproc) (all: $(nproc --all))"
    free -g
    df -h "$RUNA"
  } >> "$LOGS/sysinfo.log" 2>&1
}

oom_report() {
  {
    echo "=== $(ts) dmesg OOM lines"
    { dmesg 2>/dev/null || sudo -n dmesg 2>/dev/null || echo "(dmesg not readable; run: sudo dmesg | grep -i -E 'oom|killed process')"; } \
      | grep -i -E 'oom|out of memory|killed process' | tail -40
    free -g
  } | tee -a "$LOGS/oom.log"
}

fail() {
  say "FAILED: $*"
  sysinfo
  oom_report
  summary
  exit 1
}

# run_step NAME LOGFILE cmd...  : nice 19, pinned, timed by /usr/bin/time -v into LOGS/NAME.time
run_step() {
  local name="$1" log="$2"; shift 2
  say "START $name  (log $log)"
  /usr/bin/time -v -o "$LOGS/$name.time" nice -n 19 "${PIN[@]}" "$@" 2>&1 | tee "$log"
  local rc=$?
  say "END $name exit=$rc  wall=$(grep 'Elapsed (wall' "$LOGS/$name.time" 2>/dev/null | awk '{print $NF}')  maxRSS_kB=$(grep 'Maximum resident' "$LOGS/$name.time" 2>/dev/null | awk '{print $NF}')"
  return $rc
}

summary() {
  echo
  echo "================ Run A summary $(ts) ================"
  for s in bwrap sha unpack cache build axioms comparator-moebius003 comparator-upstream-ramare; do
    if [ -f "$MARK/$s.done" ]; then st="done"; else st="NOT DONE"; fi
    w=$(grep 'Elapsed (wall' "$LOGS/$s.time" 2>/dev/null | awk '{print $NF}')
    r=$(grep 'Maximum resident' "$LOGS/$s.time" 2>/dev/null | awk '{printf "%.1f GB", $NF/1048576}')
    printf '  %-28s %-9s wall %-12s peak RSS of largest child %s\n' "$s" "$st" "${w:--}" "${r:--}"
  done
  echo "  Logs: $LOGS"
  echo "  Send Harald: build.log axioms.log comparator-*.log sysinfo.log (and oom.log if present)"
  echo "======================================================"
}

sysinfo

# ---- 0. tools, sandbox, location -------------------------------------------------------------
case "$RUNA" in /mnt/*) fail "RUNA=$RUNA is on the Windows filesystem. Use the Linux side, e.g. ~/ra-runA";; esac
[ -x /usr/bin/time ] || fail "/usr/bin/time missing: sudo apt install time"
for t in git curl bwrap tar sha256sum; do command -v "$t" >/dev/null 2>&1 || fail "missing tool: $t"; done
command -v lake >/dev/null 2>&1 || [ -x "$HOME/.elan/bin/lake" ] || fail "elan/lake missing: see https://github.com/leanprover/elan"
export PATH="$HOME/.elan/bin:$PATH"

# Sandbox check, every run (cheap, and it can change after an update).
if out=$(bwrap --unshare-user --ro-bind / / true 2>&1 && echo bwrap-ok); then
  echo "$out" | tee "$LOGS/bwrap.log"
  echo "$out" | grep -q '^bwrap-ok$' || fail "bwrap check did not print bwrap-ok"
  touch "$MARK/bwrap.done"
else
  echo "$out" | tee "$LOGS/bwrap.log"
  fail "bwrap check failed. Send Harald the error above. Do not use --inadvisably-no-sandbox."
fi

# ---- tarball checksum --------------------------------------------------------------------------
if [ ! -f "$MARK/sha.done" ]; then
  [ -f "$TARBALL" ] || fail "tarball not found: $TARBALL"
  got=$(sha256sum "$TARBALL" | awk '{print $1}')
  echo "$got  $TARBALL" | tee "$LOGS/sha.log"
  [ "$got" = "$EXPECTED_SHA" ] || fail "sha256 mismatch: got $got, expected $EXPECTED_SHA"
  touch "$MARK/sha.done"
fi

# ---- 1. unpack (only into a fresh dir) and fetch Mathlib ---------------------------------------
if [ ! -f "$MARK/unpack.done" ]; then
  if [ -e "$WORK" ] && [ -n "$(ls -A "$WORK" 2>/dev/null)" ]; then
    fail "$WORK exists and is not empty but unpack never finished. Move it aside (mv $WORK $WORK.old) and rerun."
  fi
  mkdir -p "$WORK"
  run_step unpack "$LOGS/unpack.log" tar -xzf "$TARBALL" -C "$WORK" || fail "tar"
  [ -f "$PROJ/lakefile.lean" ] || fail "unpacked tree lacks $PROJ/lakefile.lean"
  touch "$MARK/unpack.done"
fi

cd "$PROJ" || fail "cd $PROJ"

if [ ! -f "$MARK/cache.done" ]; then
  run_step cache "$LOGS/cache.log" lake exe cache get || fail "lake exe cache get"
  touch "$MARK/cache.done"
fi

# Lake job limit: use -j/--jobs only if this Lake advertises it. Otherwise taskset above caps CPUs.
LAKEJ=()
if lake --help 2>&1 | grep -q -E -- '(^|[ ,])(-j|--jobs)([ ,=]|$)'; then
  LAKEJ=(-j "$JOBS")
  say "lake advertises a jobs flag; using -j $JOBS"
else
  say "lake --help shows no jobs flag; relying on taskset ${PIN[*]:-none} and LEAN_NUM_THREADS=$JOBS"
fi

# ---- 2. build: always rerun, Lake resumes ------------------------------------------------------
# Exactly LAPTOP-COMPARATOR.md step 2 (plus the optional -j). Previous build.log is kept.
[ -f "$LOGS/build.log" ] && mv "$LOGS/build.log" "$LOGS/build.$(date +%Y%m%d-%H%M%S).log"
run_step build "$LOGS/build.log" lake build "${LAKEJ[@]}" RSBounds.Moebius003.Upstream UpstreamRamareChallenge \
  RSBounds.Moebius003.Complete RamareMoebiusChallenge || fail "build (rerun this script to resume)"
grep -q 'Build completed successfully' "$LOGS/build.log" || fail "build log lacks 'Build completed successfully'"
touch "$MARK/build.done"

# ---- 3. axioms ---------------------------------------------------------------------------------
if [ ! -f "$MARK/axioms.done" ]; then
  : > "$LOGS/axioms.log"
  run_step axioms-upstream "$LOGS/axioms-upstream.log" lake env lean logs-claude/UpstreamAudit.lean || fail "UpstreamAudit"
  run_step axioms-complete "$LOGS/axioms-complete.log" lake env lean logs-claude/MoebiusCompleteAudit.lean || fail "MoebiusCompleteAudit"
  cat "$LOGS/axioms-upstream.log" "$LOGS/axioms-complete.log" > "$LOGS/axioms.log"
  cp "$LOGS/axioms-complete.time" "$LOGS/axioms.time"
  flat=$(tr '\n' ' ' < "$LOGS/axioms.log" | tr -s ' ')
  ok=1
  for n in Moebius003.finiteRH_of_plattGRH Moebius003.ramareMoebius_of_plattGRH \
           MoebiusInputs.mertensSqrt MoebiusInputs.smallMoebiusSum Moebius003.ramareMoebius_of_finiteRH; do
    if echo "$flat" | grep -q -F "'TernaryGoldbach.RSBounds.$n' depends on axioms: [propext, Classical.choice, Quot.sound]"; then
      say "axioms OK: $n"
    else
      say "axioms MISSING or different: $n"; ok=0
    fi
  done
  grep -q -E 'sorryAx|error:' "$LOGS/axioms.log" && { say "axioms.log mentions sorryAx or error"; ok=0; }
  [ $ok = 1 ] || fail "axiom check"
  touch "$MARK/axioms.done"
fi

# ---- 4. Comparator: short run, then the main run -----------------------------------------------
comparator_run() {   # $1 = config basename without .json
  local c="$1"
  [ -f "$MARK/$c.done" ] && { say "skip $c (done)"; return 0; }
  [ -f "$LOGS/$c.log" ] && mv "$LOGS/$c.log" "$LOGS/$c.$(date +%Y%m%d-%H%M%S).log"
  run_step "$c" "$LOGS/$c.log" lake comparator --config "$c.json"
  local rc=$?
  if [ $rc = 0 ] && grep -q -F 'Lean default kernel accepts the solution' "$LOGS/$c.log" \
                 && grep -q -F 'Your solution is okay!' "$LOGS/$c.log"; then
    touch "$MARK/$c.done"; say "$c: accepted"
  else
    grep -q -F 'exited with 137' "$LOGS/$c.log" && say "$c: exit 137 is a killed process (likely OOM), not a verdict on the proof"
    fail "$c (exit $rc)"
  fi
}

comparator_run comparator-moebius003
comparator_run comparator-upstream-ramare

sysinfo
summary
say "Run A complete."
