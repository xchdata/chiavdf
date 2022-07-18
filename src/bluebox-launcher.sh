#!/usr/bin/env bash
BIN="./bluebox_worker"

trap "echo Shutting down ...; pkill -f $BIN; exit 0" SIGINT SIGTERM

MINDELAY=1
MAXDELAY=512
DELAY=$MINDELAY
TAG=0
while :; do
    # Launch up to $VDF_CLIENT_PROCESS_COUNT workers in the background.
    ACTIVE_COUNT="$(pgrep -f $BIN | wc -l)"
    for C in $(seq $(($VDF_CLIENT_PROCESS_COUNT - $ACTIVE_COUNT))); do
        $BIN q 2>&1 | ts -s "[$TAG] %H:%M:%.S" &
        TAG=$(($TAG + 1))
    done

    # Wait until at least one finishes.
    if wait -n; then
        DELAY=$MINDELAY
    else
        if [ $DELAY -lt $MAXDELAY ]; then
            echo "Backing off for ${DELAY}s between relaunches due to worker failure."
            DELAY=$(($DELAY * 2))
        fi
    fi
    sleep $DELAY
done
