ITER=$1

if [ $# -ne 1 ]; then
  echo "$0 iteration-num"
  exit 1
fi

rm -rf results/Sfscq
mkdir results
mkdir results/Sfscq

echo "=== Running Sfscq Tests ==="

echo "== smallfile =="
./run_script.sh Sfscq smallfile /dev/sdb3 $ITER > results/Sfscq/smallfile
echo "== largefile =="
./run_script.sh Sfscq largefile /dev/sdb3 $ITER > results/Sfscq/largefile
echo "== createdelete =="
./run_script.sh Sfscq createdelete /dev/sdb3 $ITER > results/Sfscq/createdelete
echo "== rename =="
./run_script.sh Sfscq rename /dev/sdb3 $ITER > results/Sfscq/rename
