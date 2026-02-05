#!/usr/bin/env python

import sys
import subprocess
from pathlib import Path

if __name__ == "__main__":
    script_dir = Path(__file__).resolve().parent
    runner_path = script_dir.parent.parent / "test-runner.py"
    test_dir = script_dir

    cmd = [
        sys.executable,
        str(runner_path),
        "-tests-dir", str(test_dir),
        "-common-args", "-O3 -DM=1 -fno-vectorize -fno-slp-vectorize",
        *sys.argv[1:]
    ]
    result = subprocess.run(cmd, cwd=str(script_dir))
    sys.exit(result.returncode)
