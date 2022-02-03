cd ../src/Extraction/
./compile.sh
cd ../../bench
mv ../src/Extraction/extracted/ConFs ./fs/ConFs
mv ../src/Extraction/extracted/mkfs ./fs/mkfs
./compile-sources.sh
./run-all.sh 3
#sudo ./test.sh ConFs smallfile /dev/sda6 1
