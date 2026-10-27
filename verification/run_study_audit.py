"""Run a package audit and require its complete theorem output."""
from pathlib import Path
import argparse
import os
import signal
import subprocess
from check_study_packages import PROFILES, check_audit


def stop_audit(_signal, _frame):
    raise InterruptedError("The audit was cancelled.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("study", choices=sorted(PROFILES))
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    package = root / "verification/additional-proofs" / args.study
    output = args.output.resolve()
    if root == output or root in output.parents or args.output.is_symlink():
        raise ValueError("The audit output must be outside the repository.")
    version, _, _, _, audit = PROFILES[args.study]
    flag = "-DwarningAsError=true" if version == "4.19.0" else "--error=warning"
    env = {k: v for k, v in os.environ.items() if not k.startswith(("LEAN_PATH", "LEAN_SRC_PATH"))}
    env["LEAN_NUM_THREADS"] = "1"
    process = None
    with output.open("w") as log:
        signal.signal(signal.SIGTERM, stop_audit)
        try:
            process = subprocess.Popen(["lake", "env", "lean", "-j1", flag, audit], cwd=package,
                                       env=env, text=True, stdout=log, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            code = process.wait(timeout=1800)
        except BaseException:
            log.write("\nerror: The audit process did not complete.\n")
            log.flush()
            raise
        finally:
            if process is not None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
        if code:
            log.write("\nerror: The Lean audit failed.\n")
            raise RuntimeError("The Lean audit failed. See its saved output.")
    count = check_audit(package, args.study, output.read_text())
    print(f"The {args.study} audit passed with {count} theorem reports.")


if __name__ == "__main__":
    main()
