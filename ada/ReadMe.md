To get the annotated source of agent run, use `gnatclean tinynf.adb >/dev/null; gnatmake -g -O3 tinynf.adb -cargs -Wa,-adhln 2>/dev/null | sed '0,/procedure Run/d' | sed -E '/end Run;/,$d'`

GNAT checks contain 'Check' in their name so you can grep that, e.g. `Range_Check`, `Overflow_Check`, `Access_Check`... Some of them disappear with -O3 since the compiler spends more time proving they aren't needed.
