#!/usr/bin/env python3
"""TASK37: the host load of a timing stream, recorded beside its rounds.

Timing streams run concurrently (PROTOCOL.md, "TASK37 concurrency"). The
paired runner records the load averages before and after a cell
(`machine.load_average_before/after` of its manifest) but not per round,
and it is sealed; this recorder is the task-side hook. Run it beside a
stream, at the same priority class as no measurement (nice 19 is fine):

  task37_load.py record --output FILE [--interval SECONDS] [--stream NAME]

It appends one JSON line per sample to FILE (an absolute path below
.agent-files/evidence/task37/<stream>/): the wall time (UTC, ISO 8601 and
epoch seconds), the 1, 5 and 15 minute load averages, and the number of
runnable tasks and of CPUs, read from /proc/loadavg. It stops at SIGTERM or
SIGINT. `summarize FILE` prints the count and the maximum of each field. A
timing round is judged by its control and the second stage, never by this
record: the record only lets a reviewer tell interference from noise.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import signal
import sys
import time

sys.dont_write_bytecode = True
INTERVAL = 5.0


def read_loadavg(path="/proc/loadavg"):
    """(1, 5, 15 minute averages, runnable tasks) from /proc/loadavg."""
    fields = Path(path).read_text().split()
    runnable = int(fields[3].split("/")[0])
    return [float(x) for x in fields[:3]], runnable


def sample(stream, now=None, path="/proc/loadavg"):
    now = time.time() if now is None else now
    load, runnable = read_loadavg(path)
    stamp = datetime.fromtimestamp(now, timezone.utc).isoformat()
    return dict(stream=stream, epoch=round(now, 3), time=stamp, load=load,
                runnable=runnable, cpus=os.cpu_count())


def record(output, interval, stream, count=None, path="/proc/loadavg"):
    """Append samples to `output` until a signal or `count` samples."""
    if interval <= 0:
        raise ValueError("the interval is positive")
    stop = []
    for number in (signal.SIGTERM, signal.SIGINT):
        signal.signal(number, lambda *_: stop.append(1))
    done = 0
    with open(output, "a") as out:
        while not stop and (count is None or done < count):
            out.write(json.dumps(sample(stream, path=path)) + "\n")
            out.flush()
            done += 1
            if count is None or done < count:
                time.sleep(interval)
    return done


def summarize(output):
    rows = [json.loads(line) for line in Path(output).read_text().split("\n")
            if line]
    if not rows:
        raise ValueError("no samples in " + str(output))
    return dict(samples=len(rows), first=rows[0]["time"],
                last=rows[-1]["time"],
                max_load=[max(r["load"][i] for r in rows) for i in range(3)],
                max_runnable=max(r["runnable"] for r in rows),
                cpus=rows[0]["cpus"])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="action", required=True)
    rec = sub.add_parser("record")
    rec.add_argument("--output", type=Path, required=True)
    rec.add_argument("--interval", type=float, default=INTERVAL)
    rec.add_argument("--stream", default="unnamed")
    rec.add_argument("--count", type=int, help="stop after this many")
    summ = sub.add_parser("summarize")
    summ.add_argument("output", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.action == "record":
            record(args.output, args.interval, args.stream, args.count)
        else:
            print(json.dumps(summarize(args.output), indent=2))
    except (ValueError, OSError) as error:
        print("REFUSED: %s" % error, file=sys.stderr)
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
