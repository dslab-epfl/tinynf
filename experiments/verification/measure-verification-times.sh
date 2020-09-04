#!/bin/sh

LOG_FILE='verif.log'

time_from_log()
{
  grep 'Elapsed (wall clock)' "$LOG_FILE" | sed 's/Elapsed (wall clock) time (h:mm:ss or m:ss)://' | tr -d '[:space:]'
}

time_to_seconds()
{
  if [ "$(echo $1 | cut -d ':' -f 3)" = '' ]; then
    # minutes and seconds in format 0:00.00
    hours='0'
    mins="$(echo $1 | cut -d ':' -f 1)"
    secs="$(echo $1 | cut -d ':' -f 2)"
  else
    # hours, minutes, and seconds in format h:mm:ss
    hours="$(echo $1 | cut -d ':' -f 1)"
    mins="$(echo $1 | cut -d ':' -f 2)"
    secs="$(echo $1 | cut -d ':' -f 3)"
  fi
  secs="$(echo "scale=0; $secs/1" | bc)" # round seconds
  echo "(($hours * 60) + $mins) * 60 + $secs" | bc
}


if [ -z "$1" ] || [ ! -d "$1" ]; then
  echo 'Please pass the path to the Vigor repository as a first argument'
fi
VIGOR_DIR="$1"

if [ -z "$2" ]; then
  export TINYNF_DIR="$(pwd)/../../"
  export RTE_SDK="$TINYNF_DIR/experiments/dpdk-shim"
  export RTE_TARGET='.'

  printf 'Measuring Vigor symbex and validation times with TinyNF. This should take less than an hour...\n\n'
elif [ "$2" = 'original' ]; then
  if [ -z "$RTE_SDK" ]; then
    echo "Please set RTE_SDK/RTE_TARGET yourself if you want to measure the original times."
    exit 1
  fi

  printf 'Measuring Vigor symbex and validation times with Vigor. This is going to take a few hours... hope you have a lot of cores...\n\n'
else
  echo "Please either pass no 2nd arg, to measure times with TinyNF, or 'original', to measure times with Vigor"
  exit 1
fi

if [ -z "$(which klee)" ]; then
  echo "It looks like KLEE is not in your PATH, did you forget to source the Vigor paths.sh file?"
  exit 1
fi


printf '\tSymbex\t#Paths\tValidation\n'

for nf in 'nat' 'bridge' 'lb' 'pol' 'fw'; do
  printf '%s\t' "$nf"

  make -C "$VIGOR_DIR/vig$nf/" symbex-withdpdk >"$LOG_FILE" 2>&1
  if [ $? -ne 0 ]; then
    echo "Error during symbex, please check $LOG_FILE"
    exit 1
  fi
  symbex_elapsed="$(time_to_seconds $(time_from_log))"
  symbex_paths="$(ls -1 "$VIGOR_DIR/vig$nf/klee-last/call-path"* | wc -l)"
  printf "%ds\t%d\t" "$symbex_elapsed" "$symbex_paths"

  make -C "$VIGOR_DIR/vig$nf/" validate >"$LOG_FILE" 2>&1
  if [ $? -ne 0 ]; then
    echo "Error during validation, please check $LOG_FILE"
    exit 1
  fi
  validation_elapsed="$(time_to_seconds $(time_from_log))"
  cores="$(nproc)"
  printf '%ds\n' "$(echo "$validation_elapsed * $cores / $symbex_paths" | bc)"
done

rm "$LOG_FILE"
