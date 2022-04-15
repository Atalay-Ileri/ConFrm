ITER=$1

if [ $# -ne 1 ]; then
  echo "$0 iteration-num"
  exit 1
fi

rm -rf results/NB
mkdir results
mkdir results/NB

echo "=== Running Sfscq Tests ==="

echo "== smallfile =="
./run_script.sh NB smallfile /dev/sdb3 $ITER > results/NB/smallfile
echo "== largefile =="
./run_script.sh NB largefile /dev/sdb3 $ITER > results/NB/largefile
echo "== createdelete =="
./run_script.sh NB createdelete /dev/sdb3 $ITER > results/NB/createdelete
echo "== rename =="
./run_script.sh NB rename /dev/sdb3 $ITER > results/NB/rename
