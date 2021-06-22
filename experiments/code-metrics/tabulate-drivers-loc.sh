#!/bin/sh

printf 'NOTE: C# includes two versions, normal and extended, which inflates the numbers...'

printf 'Lang\tLines\n'
for lang in c csharp rust; do
  ext="$lang"
  if [ "$lang" = 'csharp' ]; then ext='cs'; fi
  if [ "$lang" = 'rust' ]; then ext='rs'; fi
  lines=$(cloc "../../$lang" --include-ext="$ext" --quiet | tail -n 2 | head -n 1 | awk '{print $5}')
  printf '%s\t%s\n' "$lang" "$lines"
done
