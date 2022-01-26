ITER=$1

if [ $# -ne 1 ]; then
  echo "$0 iteration-num"
  exit 1
fi

rm -rf results
mkdir results
mkdir results/confs

echo "=== Running ConFs Tests ==="

echo "== smallfile =="
./run_script.sh disk_img smallfile /dev/sda1 $ITER > results/confs/smallfile
echo "== largefile =="
./run_script.sh disk_img largefile /dev/sda1 $ITER > results/confs/largefile
echo "== createdelete =="
./run_script.sh disk_img createdelete /dev/sda1 $ITER > results/confs/createdelete

python process-results.py > results.txt
python process-results-largefile.py >> results.txt
