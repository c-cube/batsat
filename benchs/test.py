#!/usr/bin/env python

import os, subprocess, dataclasses, time

timeout=os.getenv('TIMEOUT','30')
print(f'timeout: {timeout}')
solvers = {
        'minisat': [f'-cpu-lim={timeout}'],
        './ratsat-bin': ['--cpu-lim', timeout],
        }

@dataclasses.dataclass
class Stats(object):
    unknown: int = 0
    sat: int = 0
    unsat: int = 0
    ctime: float = 0.

def test_dir(d):
    print(f"test {d}")
    failures = []
    stats = {name: Stats() for name, _ in solvers.items()}
    for (root, _, files) in os.walk(d):
        for file in files:
            file = os.path.join(root,file)
            print(f"test on {file}")
            per_solver = {}
            expect = None
            for s, args in solvers.items():
                start = time.time()
                code = subprocess.call([s] + args + [file], stdout=subprocess.DEVNULL)
                ctime = time.time() - start
                if code == 0: res = 'UNKNOWN'; stats[s].unknown += 1
                if code == 10: res = 'SAT'; stats[s].sat += 1; stats[s].ctime += ctime
                if code == 20: res = 'UNSAT'; stats[s].unsat += 1; stats[s].ctime += ctime
                if expect is not None:
                    if expect != res and res != 'UNKNOWN':
                        print(f"failure on {file}: {per_solver}")
                        failures.append((file, per_solver))
                else:
                    expect = res
                per_solver[s] = res
            print(f"on {file}: {per_solver}")
    return stats, failures

stats, fails = test_dir("benchs/basic")

print(stats)
if fails:
    print("SOME FAILURES")
    print(fails)
else:
    print("OK")

