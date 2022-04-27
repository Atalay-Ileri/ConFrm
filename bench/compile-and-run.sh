cd ../src/Extraction/
./compile.sh
cd ../../bench
mv ../src/Extraction/extracted/ConFs ./fs/ConFs
mv ../src/Extraction/extracted/mkfs ./fs/ConMkfs

cd ../../fscq/fscq15/src/
make
cd ../../../ConFrm/bench
mv ../../fscq/fscq15/src/fuse ./fs/CfscqFs
mv ../../fscq/fscq15/src/mkfs ./fs/CfscqMkfs

./compile-sources.sh
./run-confs.sh 10 $1
#./run-sfscq.sh 10 $1
#./run-cfscq.sh 10 $1

./get-stats.sh
