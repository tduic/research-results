#!/bin/sh
# Resumable runner for the IdentityT0 kernel checks: builds the Lean modules listed in a module file one
# at a time and logs per-module wall time, CPU time and peak RSS.  Run from werner-three-copy-endpoint/lean.
#
#   sh layerD_t0/run_identity.sh [MODULE_LIST]       default MODULE_LIST: layerD_t0/identity_modules.txt
#
# MODULE_LIST has one Lean module name per line (blank lines and lines starting with # are skipped), in build
# order; the identity generator writes it.  Every finished module is appended to the log as
#   BENCH <module> rc=0 wall=..s cpu=..s maxrss=..MB
# and a module with a rc=0 line already in the log is skipped, so the run can be stopped (or killed, or the
# machine can sleep) and restarted with the same command.  Lake's own build cache also skips finished modules.
#
# Environment:
#   IDLOG       log file (default layerD_t0/identity_run.log)
#   LOCK        flock file serialising heavy Lean processes (default: none, i.e. no flock)
#   SHARD, NSHARDS  build only the modules whose line number n (0-based, counting module lines) has
#               n % NSHARDS == SHARD (for parallel CI jobs whose module sets are independent)
#   STOP_ON_FAIL=1  stop at the first failing module (default: log the failure and continue)
#   MINFREE_MB  before starting each module, wait until MINFREE_MB of memory is free (Linux: MemAvailable, or
#               the room left in this process's memory cgroup if that is less, as in a container), for running two
#               shards side by side on one small machine without the OOM killer taking one of them
# Exit code 137 in the log is the OOM killer, not a proof failure: rerun that module alone.
set -u
LIST=${1:-layerD_t0/identity_modules.txt}
IDLOG=${IDLOG:-layerD_t0/identity_run.log}
SHARD=${SHARD:-0}
NSHARDS=${NSHARDS:-1}
STOP_ON_FAIL=${STOP_ON_FAIL:-0}
[ -f "$LIST" ] || { echo "run_identity: no module list $LIST (run the identity generator first)"; exit 2; }
touch "$IDLOG"
# free memory in MB: MemAvailable, or less if this process's memory cgroup (a container's or sandbox's limit) has less
# room left; the cgroup's usage counts reclaimable page cache, so its inactive file pages are subtracted
avail_mb() {
  a=$(awk '/MemAvailable/ {print int($2/1024)}' /proc/meminfo)
  lim=; cur=; inact=0
  if [ -r /sys/fs/cgroup/memory.max ]; then
    lim=$(cat /sys/fs/cgroup/memory.max); cur=$(cat /sys/fs/cgroup/memory.current 2>/dev/null)
    inact=$(awk '$1 == "inactive_file" {print $2}' /sys/fs/cgroup/memory.stat 2>/dev/null)
  else
    cg=$(awk -F: '$2 == "memory" {print $3}' /proc/self/cgroup 2>/dev/null)
    d=/sys/fs/cgroup/memory$cg
    if [ -n "$cg" ] && [ -r "$d/memory.limit_in_bytes" ]; then
      lim=$(cat "$d/memory.limit_in_bytes"); cur=$(cat "$d/memory.usage_in_bytes")
      inact=$(awk '$1 == "total_inactive_file" {print $2}' "$d/memory.stat" 2>/dev/null)
    fi
  fi
  case "$lim" in ''|max) ;; *)
    if [ "$lim" -lt 1000000000000000 ] 2>/dev/null; then
      c=$(( (lim - cur + ${inact:-0}) / 1048576 )); [ "$c" -lt "$a" ] && a=$c
    fi ;;
  esac
  echo "$a"
}
n=0; done_n=0; fail_n=0; todo_n=0
for m in $(grep -v '^[[:space:]]*#' "$LIST" | grep -v '^[[:space:]]*$'); do
  i=$n; n=$((n + 1))
  [ $((i % NSHARDS)) -eq "$SHARD" ] || continue
  if grep -q "^BENCH $m rc=0 " "$IDLOG"; then done_n=$((done_n + 1)); continue; fi
  todo_n=$((todo_n + 1))
  # optional memory gate for parallel shards on one machine: wait until MemAvailable >= MINFREE_MB
  if [ -n "${MINFREE_MB:-}" ] && [ -r /proc/meminfo ]; then
    while [ "$(avail_mb)" -lt "$MINFREE_MB" ]; do sleep 20; done
  fi
  echo "$(date -u +%FT%TZ) start $m" >> "$IDLOG"
  if [ -n "${LOCK:-}" ]; then
    flock "$LOCK" python3 layerD_proto/timebench.py "$m" lake build "$m" > "$IDLOG.cur" 2>&1
  else
    python3 layerD_proto/timebench.py "$m" lake build "$m" > "$IDLOG.cur" 2>&1
  fi
  rc=$?
  f=$(echo "$m" | sed 's#^LayerDT0\.#layerD_t0/LayerDT0/#; s#\.#/#g').lean
  { grep -F "$f" "$IDLOG.cur" | grep -E "error|axioms" | head -40; grep "^BENCH" "$IDLOG.cur"; } >> "$IDLOG"
  if [ $rc -ne 0 ]; then
    fail_n=$((fail_n + 1))
    grep -q "^BENCH $m " "$IDLOG.cur" || echo "BENCH $m rc=$rc (no timing line)" >> "$IDLOG"
    [ "$STOP_ON_FAIL" = 1 ] && { echo "run_identity: $m failed (rc=$rc), stopping"; exit 1; }
  else
    done_n=$((done_n + 1))
  fi
done
rm -f "$IDLOG.cur"
echo "run_identity: shard $SHARD/$NSHARDS: $done_n done, $fail_n failed, $todo_n attempted this run" | tee -a "$IDLOG"
[ $fail_n -eq 0 ]
