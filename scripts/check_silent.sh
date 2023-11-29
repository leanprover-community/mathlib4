tee "$1";
if [ -s "$1" ]; then
  echo "Error: output is not empty";
  rm -f "$1";
  exit 1;
fi
rm -f "$1";
