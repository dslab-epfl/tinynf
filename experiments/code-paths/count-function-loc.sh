#!/bin/sh
# $1 = file name
# $2 = function name

# From https://unix.stackexchange.com/a/277390
# -l9999 to avoid breaking any lines
indent -st -orig -l9999 "$1" | awk '
BEGIN { state = 0; last = ""; }
$0 ~ /^'$2'\(/ { print last; state = 1; }
        { if (state == 1) print; }
$0 ~ /^}/ { if (state) state = 2; }
        { last = $0; }
' | cpp | grep -v '^#' | cloc - --force-lang=C --quiet | tail -n 2 | head -n 1 | awk '{print $5}'
# above: cpp to deal with ifdefs, grep to remove the # annotations of cpp, then get the last number (lines of code)
