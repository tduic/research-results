#!/bin/sh
# Layer D (t = 0) builds, one Lean process at a time (each <= about 3 GB).  Run from werner-three-copy-endpoint/lean.
#   sh layerD_t0/build.sh sound   # the soundness modules (no certificate data): per-push CI
#   sh layerD_t0/build.sh data    # regenerate from the certificate and kernel-check every instance (opt-in, ~1-2 h)
set -e
mode=${1:-sound}
b() { python3 layerD_proto/timebench.py "$1" lake build "$1"; }
SOUND="LayerDT0.Basic LayerDT0.XInt LayerDT0.Tables LayerDT0.Rows LayerDT0.Poly LayerDT0.Sites LayerDT0.PDCheck LayerDT0.PD LayerDT0.Assemble LayerDT0.Bridge LayerDT0.IdentityAsm LayerDT0.Totals LayerDT0.IdentityUnit LayerDT0.IdentityBlock LayerDT0.IdentityDec LayerDT0.IdentityFin LayerDT0.Recomp LayerDT0.IdentitySeg LayerDT0.RecompSlice LayerDT0.FamBound LayerDT0.StatSplit"
if [ "$mode" = sound ]; then
  for m in $SOUND; do b $m; done
  exit 0
fi
(cd layerD_t0 && python3 gen_small.py && python3 gen_sites.py && python3 gen_pd.py && python3 gen_assemble.py)
for m in $SOUND; do b $m; done
for m in Tables Qubit Rows SitesE SitesT3 SitesT0 SitesT01 SitesT2 SitesT02 SitesT23 Cuts Lam PD.Den; do
  b LayerDT0.Gen.$m
done
n=$(ls layerD_t0/LayerDT0/Gen/PD/G*.lean | wc -l)
c=0
while [ $c -lt $n ]; do b LayerDT0.Gen.PD.G$c; c=$((c+1)); done
b LayerDT0.Gen.PD.All
c=0
while [ $c -lt $n ]; do b LayerDT0.Gen.Blocks.G$c; c=$((c+1)); done
b LayerDT0.Gen.AllBC
b LayerDT0.Gen.LamOk
b LayerDT0.Gen.Endpoint
b LayerDT0.Gen.IdentityParts
