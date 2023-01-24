#cd ../src/Extraction/
#./compile.sh
#cd ../../bench
#mv ../src/Extraction/extracted/ConFs ./fs/ConFs
#mv ../src/Extraction/extracted/mkfs ./fs/ConMkfs

#cd ../../fscq/fscq15/src/
#make
#cd ../../../ConFrm/bench
#mv ../../fscq/fscq15/src/fuse ./fs/CfscqFs
#mv ../../fscq/fscq15/src/mkfs ./fs/CfscqMkfs

if [ $# -ne 2 ]; then
  echo "$0 dev num-of-times"
  exit 1
fi

./compile-sources.sh
sudo rm -rf results
#sudo ./run-confs.sh $2 $1
#sleep 1m
#sudo ./run-confssync.sh $2 $1
#sleep 1m
#sudo ./run-cfscq.sh $2 $1
#sleep 1m
sudo ./run-sfscq.sh $2 $1
sleep 1m
sudo ./run-dfscq.sh $2 $1
sleep 1m
sudo ./run-ext4.sh $2 $1
sleep 1m
sudo ./run-ext4journal.sh $2 $1
sleep 1m

./get-stats.sh
