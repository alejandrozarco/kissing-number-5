#!/bin/bash
# usage: ./run.sh <k5.py args...>
# nice 19, background QoS (taskpolicy -b), single thread; log appended to logs/; RSS watchdog: the job (this
# script's own child, by PID) is stopped if its RSS exceeds RSS_MAX_KB (default 3 GB, the Mac guideline).
cd "$(dirname "$0")"; mkdir -p logs
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 NUMEXPR_NUM_THREADS=1 RAYON_NUM_THREADS=1
LOG="logs/$(echo "$@ ${DEL:+del$DEL}" | tr ' ' '_').log"
RSS_MAX_KB=${RSS_MAX_KB:-3000000}
nice -n 19 taskpolicy -b python3 k5.py "$@" >> "$LOG" 2>&1 &
PID=$!
echo "pid $PID $(date '+%F %T') args: $*" >> "$LOG"
PEAK=0
while kill -0 "$PID" 2>/dev/null; do
  R=$(ps -o rss= -p "$PID" 2>/dev/null | tr -d ' '); R=${R:-0}
  [ "$R" -gt "$PEAK" ] && PEAK=$R
  if [ "$R" -gt "$RSS_MAX_KB" ]; then
    echo "WATCHDOG: RSS ${R} kB > ${RSS_MAX_KB} kB, stopping pid $PID" >> "$LOG"; kill "$PID"; break
  fi
  sleep 2
done
wait "$PID"; RC=$?
echo "rc $RC peak_rss_kB $PEAK $(date '+%F %T')" >> "$LOG"
