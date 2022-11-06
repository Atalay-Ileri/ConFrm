cd ../src/Extraction/
./compile.sh
cd ../../bench
mv ../src/Extraction/extracted/ConFs ./fs/ConFs
mv ../src/Extraction/extracted/mkfs ./fs/ConMkfs

cd ../../fscq/fscq15/src/
#make
cd ../../../ConFrm/bench
mv ../../fscq/fscq15/src/fuse ./fs/CfscqFs
mv ../../fscq/fscq15/src/mkfs ./fs/CfscqMkfs

./compile-sources.sh
sudo rm -rf results
sudo ./run-confs.sh $2 $1
sudo ./run-cfscq.sh $2 $1
sudo ./run-sfscq.sh $2 $1

./get-stats.sh
