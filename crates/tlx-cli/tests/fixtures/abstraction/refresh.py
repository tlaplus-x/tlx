"""Refresh the small abstraction oracles: python3 PATH/refresh.py PATH/TO/tlx."""
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(ROOT / "scripts"))

from spectest import normalize
from tempdirs import TemporaryDirectory
from tlc import parse, run_tlc_raw
from tlxlib import run_proc


def main():
    binary = str(Path(sys.argv[1]).resolve())
    fixtures = Path(__file__).resolve().parent
    pending = {}
    env = {k: v for k, v in os.environ.items() if not k.startswith("TLX_")}
    for name, code in [("cleanup", 0), ("empty-safe", 0), ("empty-violation", 12), ("reset", 0), ("violation", 12)]:
        case = fixtures / name
        with TemporaryDirectory(prefix="tlx-abstraction-oracle-") as tmp:
            work = Path(tmp)
            for file in ["Counter.tla", "Counter.cfg"]:
                (work / file).write_bytes((case / file).read_bytes())
            result = run_proc([binary, "abstract", "Counter.tla", "-output", "out"], cwd=work, env=env, timeout=60)
            if result.returncode != 0:
                raise RuntimeError(result.stdout + result.stderr)
            for module, directory in [("Counter", work), ("Abstract", work / "out")]:
                output, rc, wall = run_tlc_raw(str(directory / f"{module}.tla"), ["-tool", "-workers", "1", "-seed", "1", "-fp", "0"], timeout=60)
                expected = "success" if code == 0 else "safety failure"
                if rc != code or parse(output, wall, rc).get("result") != expected:
                    raise RuntimeError(f"{name}/{module}: unexpected TLC result {rc}\n{output}")
                pending[case / f"{module}.tlc.out"] = f"# exit {rc}\n" + normalize(output, [str(work.resolve()), str(work), str(ROOT.resolve()), str(ROOT)])
            for file in ["Abstract.tla", "Abstract.cfg"]:
                pending[case / file] = (work / "out" / file).read_text()
            print(f"{name}: original and generated TLC verdicts agree ({expected})")
    for path, content in pending.items():
        path.write_text(content)


if __name__ == "__main__":
    main()
