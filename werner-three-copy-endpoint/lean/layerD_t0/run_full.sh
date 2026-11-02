#!/bin/sh
# The complete IdentityT0 kernel run and the final theorem, on one machine.  Run from werner-three-copy-endpoint/lean.
#
#   JOBS=3 sh layerD_t0/run_full.sh
#
# 1. Checks the generated identity modules against identity_manifest.json; regenerates them (about 30 min per family
#    cold) if they are missing or differ, and stops unless the manifest then matches.  So the run always checks
#    exactly the pinned modules, which were generated from the pinned v2 certificate.
# 2. Splits identity_modules.txt into prep (Pos/Orb/Tab), light part modules, heavy part modules (the largest blocks,
#    up to about 3.8 GB each) and final modules (CE, K, Fam, Core), and builds them in that order with
#    run_identity.sh: prep serially, light in JOBS parallel shards (each waits for MINFREE_MB of free memory before a
#    module), then one serial retry pass over light, heavy serially, final serially.
# 3. Builds LayerDT0.Final (identityT0 and werner3_endpoint_all_d) and prints its axioms.
# 4. Exits 0 only if every one of the modules of identity_modules.txt has an rc=0 line and LayerDT0.Final built.
# Resumable: logs live in $RUNLOGS (default layerD_t0/runlogs) and modules with rc=0 there are skipped.
set -u
export PATH="$HOME/.elan/bin:$PATH"
JOBS=${JOBS:-2}
MINFREE_MB=${MINFREE_MB:-3600}
HEAVY_MINFREE_MB=${HEAVY_MINFREE_MB:-4600}
RUNLOGS=${RUNLOGS:-layerD_t0/runlogs}
D=layerD_t0
mkdir -p "$RUNLOGS"
echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
say() { echo "run_full: $* ($(date -u +%FT%TZ))"; }

# identity_manifest.py prints OK on a match and MISMATCH <families> otherwise (its exit status is 0 either way)
manifest_ok() { [ "$(python3 $D/identity_manifest.py 2>&1 | tail -1)" = "OK" ]; }
if ! manifest_ok; then
  say "generated modules missing or different: regenerating"
  # per family: the grid modules (Pos, Orb) first, then the part modules; each generator gets its own scratch copy
  # of the module list, so the pinned identity_modules.txt is never rewritten (identity_manifest.py hashes it)
  for f in 31 13 22; do
    cp $D/identity_modules.txt "$RUNLOGS/l$f.txt"
    python3 $D/gen_totals.py $f --grid-only --list "$RUNLOGS/l$f.txt" > "$RUNLOGS/gen_grid_$f.log" 2>&1 || { tail "$RUNLOGS/gen_grid_$f.log"; exit 3; }
    python3 $D/gen_identity_t0.py $f --list "$RUNLOGS/l$f.txt" > "$RUNLOGS/gen_id_$f.log" 2>&1 || { tail "$RUNLOGS/gen_id_$f.log"; exit 3; }
    say "family $f generated"
  done
  manifest_ok || { say "regenerated modules do not match identity_manifest.json"; exit 3; }
fi

ALL="$RUNLOGS/all.txt"
grep -v '^[[:space:]]*#' $D/identity_modules.txt | grep -v '^[[:space:]]*$' > "$ALL"
HEAVY='F22\.P248|F22\.P249|F13\.P331|F31\.P339|F22\.P421'
grep -E '\.(Pos|Orb|Tab)$' "$ALL" > "$RUNLOGS/prep.txt"
grep -E '\.Gen\.Id\.F[0-9]+\.P[0-9]' "$ALL" | grep -Ev "($HEAVY)" > "$RUNLOGS/light.txt"
grep -E '\.Gen\.Id\.F[0-9]+\.P[0-9]' "$ALL" | grep -E "($HEAVY)" > "$RUNLOGS/heavy.txt"
grep -E '\.(CE[0-9]+|K|Fam|Core)$' "$ALL" > "$RUNLOGS/final.txt"
n_all=$(wc -l < "$ALL")
n_split=$(cat "$RUNLOGS/prep.txt" "$RUNLOGS/light.txt" "$RUNLOGS/heavy.txt" "$RUNLOGS/final.txt" | wc -l)
[ "$n_all" -eq "$n_split" ] || { say "module split lost modules ($n_split of $n_all)"; exit 4; }
say "$n_all modules: prep $(wc -l < $RUNLOGS/prep.txt), light $(wc -l < $RUNLOGS/light.txt), heavy $(wc -l < $RUNLOGS/heavy.txt), final $(wc -l < $RUNLOGS/final.txt); JOBS=$JOBS"

run() { IDLOG="$1" SHARD="${3:-0}" NSHARDS="${4:-1}" MINFREE_MB="${5:-$MINFREE_MB}" sh $D/run_identity.sh "$2"; }
run "$RUNLOGS/prep.log" "$RUNLOGS/prep.txt" || { say "a prep module (Pos/Orb/Tab) failed: stopping before the long run"; tail -20 "$RUNLOGS/prep.log"; exit 7; }
k=0; pids=""
while [ $k -lt "$JOBS" ]; do
  run "$RUNLOGS/light_$k.log" "$RUNLOGS/light.txt" $k "$JOBS" & pids="$pids $!"
  k=$((k + 1)); sleep 30
done
for p in $pids; do wait $p; done
# one serial retry pass over everything not yet rc=0 (OOM kills of a parallel shard land here)
cat "$RUNLOGS"/light_*.log > "$RUNLOGS/light_retry.log"
run "$RUNLOGS/light_retry.log" "$RUNLOGS/light.txt" 0 1 "$HEAVY_MINFREE_MB"
run "$RUNLOGS/heavy.log" "$RUNLOGS/heavy.txt" 0 1 "$HEAVY_MINFREE_MB"
run "$RUNLOGS/final.log" "$RUNLOGS/final.txt" 0 1 "$HEAVY_MINFREE_MB"

cat "$RUNLOGS"/*.log | grep '^BENCH .* rc=0 ' | awk '{print $2}' | sort -u > "$RUNLOGS/ok.txt"
missing=$(sort -u "$ALL" | comm -23 - "$RUNLOGS/ok.txt" | wc -l)
say "modules with rc=0: $(wc -l < $RUNLOGS/ok.txt) of $n_all; missing $missing"
[ "$missing" -eq 0 ] || { sort -u "$ALL" | comm -23 - "$RUNLOGS/ok.txt" | head -20; exit 5; }

python3 layerD_proto/timebench.py LayerDT0.Final lake build LayerDT0.Final > "$RUNLOGS/final_theorem.log" 2>&1
rc=$?
grep -E "axioms|error|BENCH" "$RUNLOGS/final_theorem.log"
[ $rc -eq 0 ] || { say "LayerDT0.Final failed (rc=$rc)"; exit 6; }
say "DONE: every module rc=0 and LayerDT0.Final built"
