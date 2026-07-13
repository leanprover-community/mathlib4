find ./Mathlib -name "*.lean" -print0 | xargs -0 sed -i -e "s/^--Komyyy0 \(.*\)/\1 --Komyyy0/g" -e "s/^\(.*\) --Komyyy1/--Komyyy1 \1/g"
