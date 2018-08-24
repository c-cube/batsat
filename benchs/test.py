#!/usr/bin/env python

import os, subprocess
solvers = {
        'minisat': ['-cpu-lim=30'],
        './ratsat-bin': ['--cpu-lim', '30'],
        }

def test_dir(d):
    print(f"test {d}")
    failures = []
    for (root, _, files) in os.walk(d):
        for file in files:
            file = os.path.join(root,file)
            print(f"test on {file}")
            per_solver = {}
            expect = None
            for s, args in solvers.items():
                code = subprocess.call([s] + args + [file], stdout=subprocess.DEVNULL)
                if code == 0: res = 'UNKNOWN'
                if code == 10: res = 'SAT'
                if code == 20: res = 'UNSAT'
                if expect is not None:
                    if expect != res:
                        print(f"failure on {file}: {per_solver}")
                        failures.append((file, per_solver))
                else:
                    expect = res
                per_solver[s] = res
            print(f"on {file}: {per_solver}")
    return failures

fails = test_dir("benchs/basic")

if fails:
    print("SOME FAILURES")
    print(fails)
else:
    print("OK")

