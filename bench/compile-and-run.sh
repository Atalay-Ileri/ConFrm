cd ../src/Extraction/
./compile.sh
cd ../../bench
mv ../src/Extraction/extracted/ConFs ./fs/ConFs
mv ../src/Extraction/extracted/mkfs ./fs/ConMkfs
./compile-sources.sh
./run-confs.sh 10
#./run-sfscq.sh 10
./run-cfscq.sh 10
