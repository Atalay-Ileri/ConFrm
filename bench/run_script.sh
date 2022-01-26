#!/bin/bash
FSP=$1
TEST=$2
DEV=$3
I=$4

MK="mkfs"
FSCQ="ConFs"
MKFS="$FSP$MK"
FS="$FSCQ"
TMP="/tmp/"
DIR="$TMP$FS"

if [ $# -ne 4 ]; then
  echo "$0 fs-prefix test-name dev num-of-times"
  exit 1
fi

#echo "ensure sudo works first"
#( sudo true ) || exit 1

echo "=== Unmount $DIR ==="
if [[ $(findmnt $DIR) ]]; then fusermount -u $DIR; fi
while [[ $(findmnt $DIR) ]]; do :; done

#echo "=== $MKFS in $DEV ==="
#./fs/$MKFS $DEV

echo "=== Recreate $DIR ==="
rm -rf $DIR
mkdir $DIR

echo "=== Mount $FS at $DIR ==="
./fs/$FS $DEV -f -o big_writes,atomic_o_trunc,nonempty $DIR &
while ! [[ $(findmnt $DIR) ]]; do :; done
#rm -rf $DIR/d

echo "=== Starting Testing ==="

echo "=== $TEST Bench ==="
for i in $(seq 1 $I);
do
#    rm -rf $DIR/d;
    ./tests/$TEST $DIR
done

echo "=== Finished Testing ==="

echo "=== Unmount $DIR ==="
fusermount -u $DIR
while [[ $(findmnt $DIR) ]]; do :; done

echo "=== Delete $DIR ==="
rm -rf $DIR
