#!/bin/bash
FSP=$1
TEST=$2
DEV=$3
I=$4

MK="Mkfs"
FSB="Fs"
MKFS="$FSP$MK"
FS="$FSP$FSB"
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

dd if=/dev/zero of=$DEV bs=4096 count=$FSCQBLOCKS
echo "=== $MKFS in $DEV ==="
./fs/$MKFS $DEV

echo "=== Recreate $DIR ==="
rm -rf $DIR
mkdir $DIR

echo "=== Mount $FS at $DIR ==="
./fs/$FS $DEV -f  -o nonempty,default_permissions,big_writes,atomic_o_trunc $DIR &
while ! [[ $(findmnt $DIR) ]]; do :; done

echo "=== Starting Testing ==="

echo "=== $TEST Bench ==="
for i in $(seq 1 $I);
do
    rm -rf $DIR/*;
    ./tests/$TEST $DIR
done

echo "=== Finished Testing ==="

echo "=== Unmount $DIR ==="
fusermount -u $DIR
while [[ $(findmnt $DIR) ]]; do :; done

echo "=== Delete $DIR ==="
rm -rf $DIR
