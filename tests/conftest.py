import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
for sub in ["dqi-finite-size/experiments/finite_size",
            "dqi-finite-size/experiments/dqi_verifiable"]:
    sys.path.insert(0, str(ROOT / sub))
