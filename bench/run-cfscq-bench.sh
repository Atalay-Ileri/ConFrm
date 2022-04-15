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
TP="./tests/"
CMD="$TP$TEST"

FSCQBLOCKS=34310
TRACE="/tmp/blktrace.out"



if [ $# -ne 4 ]; then
  echo "$0 fs-name bench-name dev-path iter-count "
  exit 1
fi

## Just in case..
echo "=== Unmount $DIR ==="
if [[ $(findmnt $DIR) ]]; then fusermount -u $DIR; fi
while [[ $(findmnt $DIR) ]]; do :; done

mkdir -p $DIR
mkdir -p $DIR.real

## Ensure sudo works first
#( sudo true ) || exit 1

## Do a priming run on whatever the native /tmp file system is..
#mkdir -p $DIR
#$CMD $DIR
#rm -rf $DIR
#mkdir -p $DIR

## fscq
dd if=/dev/zero of=$DEV bs=4096 count=$FSCQBLOCKS
./fs/$MKFS $DEV
./fs/$FS $DEV -s -f -o nonempty $DIR &
while ! [[ $(findmnt $DIR) ]]; do :; done
#sudo blktrace -d $DEV -o - > $TRACE &
#TRACEPID=$!
#sleep 1

for i in $(seq 1 $I);
do
    rm -rf $DIR/*;
    $CMD $DIR
done

fusermount -u $DIR
#sudo killall blktrace
#sleep 1
#wait $TRACEPID
#mv $TRACE $TEST-fscq.blktrace
#./blkstats.sh $TEST-fscq.blktrace >> $TEST-fscq.out
