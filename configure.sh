#!/bin/sh
mmap=yes
getcunlocked=yes
debug=no
usage () {
cat <<EOF
usage: configure.sh [ <option> ... ]

where <option> is one of the following:

-h                  print this command line option summary
-g                  include and compile with debugging support

--mmap              enable memory mapped I/O
--getc-unlocked     use 'getc_locked' instead of 'getc'

--no-mmap           disable fast memory mapped I/O
--no-getc-unlocked  use 'getc' instead of 'getc_unlocked'
EOF
}
while [ $# -gt 0 ]
do
  case $1 in
    -h)  usage; exit 0;;
    -g) debug=yes;;
    --mmap) mmap=yes;;
    --getc-unlocked) getcunlocked=yes;;
    --no-mmap) mmap=no;;
    --no-getc-unlocked) getcunlocked=no;;
    *)
      echo "*** configure.sh: invalid option '$1' (try '-h')"
      exit 1
      ;;
  esac
  shift
done
COMPILE="gcc -Wall"
if [ $debug = yes ]
then
  COMPILE="$COMPILE -g"
else
  COMPILE="$COMPILE -O3 -DNDEBUG"
fi
[ $mmap = no ] && COMPILE="$COMPILE -DNMMAP"
[ $getcunlocked = no ] && COMPILE="$COMPILE -DNGETCUNLOCKED"
echo "$COMPILE"
sed -e "s,@COMPILE@,$COMPILE," makefile.in > makefile
