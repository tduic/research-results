#!/usr/bin/env python3
"""Run a command and report wall time and peak RSS of its descendants (a /usr/bin/time -v stand-in).

Usage: python3 timebench.py LABEL CMD...   -> prints 'BENCH LABEL rc=.. wall=..s maxrss=..MB' (stderr+stdout of CMD pass through)
"""
import resource, subprocess, sys, time
label, cmd = sys.argv[1], sys.argv[2:]
t = time.time()
rc = subprocess.run(cmd).returncode
w = time.time() - t
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
rss = ru.ru_maxrss / 1024
cpu = ru.ru_utime + ru.ru_stime
print(f"BENCH {label} rc={rc} wall={w:.1f}s cpu={cpu:.1f}s maxrss={rss:.0f}MB", flush=True)
sys.exit(rc)
