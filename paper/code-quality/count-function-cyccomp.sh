#!/bin/sh
# $1 = file name
# $2 = function name

file="$(mktemp)"
# From https://unix.stackexchange.com/a/277390
# -l9999 to avoid breaking any lines
indent -st -orig -l9999 "$1" | awk '
BEGIN { state = 0; last = ""; }
$0 ~ /^'$2'\(/ { print last; state = 1; }
        { if (state == 1) print; }
$0 ~ /^}/ { if (state) state = 2; }
        { last = $0; }
' | cpp > "$file"
# above: cpp to deal with ifdefs
cccc --lang=c "$file" >/dev/null 2>&1
grep 'McCabes_cyclomatic_complexity' .cccc/cccc.xml | head -n 1 | cut -d '"' -f 2
# above: 1st cyccomp is the total, the rest are irrelevant
rm -f "$file"
rm -rf '.cccc'
