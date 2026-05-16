find ./Mathlib -name "*.lean" -print0 | xargs -0 sed -i -e "s/^\(.*\) --Komyyy0/--Komyyy0 \1/g" -e "s/^--Komyyy1 \(.*\)/\1 --Komyyy1/g"
