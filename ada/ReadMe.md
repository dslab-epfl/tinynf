TODO: https://docs.adacore.com/gnat_ugn-docs/html/gnat_ugn/gnat_ugn/building_executable_programs_with_gnat.html#style-checking

TODO: audit use of 'Unchecked_Access (`grep -Fir Unchecked_Access *.ads *.adb`) (can we use 'access all' to avoid this somehow?)

TODO: move to subfolders like the rest

TODO: auto-format? or at least sort with/use and make them consistent (avoid duplication in adb if being in ads is enough as well)

TODO: combine the common "put_line; os_abort" pattern into something on e.g. environment?

TODO: use object-oriented syntax if possible? also avoid "This" as name it's a bit misleading (e.g. agents)

To get the annotated source of agent run, use `gnatclean tinynf.adb >/dev/null; gnatmake -g -O3 tinynf.adb -cargs -Wa,-adhln 2>/dev/null | sed '0,/procedure Run/d' | sed -E '/end Run;/,$d'`

GNAT checks contain 'Check' in their name so you can grep that, e.g. `Range_Check`, `Overflow_Check`, `Access_Check`... Some of them disappear with -O3 since the compiler spends more time proving they aren't needed.
