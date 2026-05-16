import subprocess
import time
import statistics
import os
import re

BOOGIE = "boogie" 
TEST_DIR = "Test"
RUNS = 5

BENCHMARKS = ["arith", "counter", "stack", "test"]

def count_quantifiers(path):
    with open(path) as f:
        src = f.read()
    return len(re.findall(r'\bforall\b', src))

def time_boogie(path):
    """Run Boogie on path, return (wall_seconds, verified). -1 on error."""
    times = []
    for _ in range(RUNS):
        t0 = time.perf_counter()
        result = subprocess.run(
            [BOOGIE, path],
            capture_output=True,
            text=True
        )
        elapsed = time.perf_counter() - t0
        times.append(elapsed)

    return statistics.median(times), statistics.stdev(times)

def fmt(t):
    return f"{t*1000:7.1f} ms"

def fmt_speedup(orig, ours):
    if ours == 0:
        return "  N/A"
    return f"{orig/ours:5.2f}x"

print(f"\nBoogie timing harness  ({RUNS} runs, median reported)")
print(f"{'Benchmark':<12} {'Quant (orig)':>12} {'Quant (ours)':>12} "
      f"{'Time (orig)':>12} {'Time (ours)':>12} {'Speedup':>8}")
print("-" * 80)

for bench in BENCHMARKS:
    orig_path = os.path.join(TEST_DIR, f"{bench}_original.bpl")
    ours_path = os.path.join(TEST_DIR, f"{bench}.bpl")

    if not os.path.exists(orig_path) or not os.path.exists(ours_path):
        print(f"{bench:<12}  [files not found, skipping]")
        continue

    q_orig = count_quantifiers(orig_path)
    q_ours = count_quantifiers(ours_path)

    t_orig, sd_orig= time_boogie(orig_path)
    t_ours, sd_ours = time_boogie(ours_path)

    print(f"{bench:<12} {q_orig:>12} {q_ours:>12} "
          f"{fmt(t_orig):>12} (±{sd_orig*1000:.0f}) "
          f"{fmt(t_ours):>12} (±{sd_ours*1000:.0f}) "
          f"{fmt_speedup(t_orig, t_ours):>8}")

print()