#!/bin/sh
debug=no
while [ $# -gt 0 ]
do
  case $1 in
    -h) echo "usage: configure.sh [-g]"; exit 0;;
    -g) debug=yes;;
    *) echo "*** configure.sh: invalid option '$1' (try '-h')"; exit 1;;
  esac
  shift
done
if [ $debug = yes ]
then
  COMPILE="gcc -Wall -g"
else
  COMPILE="gcc -Wall -O3 -DNDEBUG"
fi
echo "$COMPILE"
sed -e "s,@COMPILE@,$COMPILE," makefile.in > makefile
