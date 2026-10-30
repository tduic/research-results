import sys
from pathlib import Path

PROJECT = Path(__file__).resolve().parent.parent
for sub in ["experiments/finite_size", "experiments/dqi_verifiable"]:
    sys.path.insert(0, str(PROJECT / sub))
