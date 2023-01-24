ITER=$1
DEV=$2

if [ $# -ne 2 ]; then
  echo "$0 iteration-num dev-path"
  exit 1
fi

rm -rf results/Sfscq
mkdir results
mkdir results/Sfscq

echo "=== Running Sfscq Tests ==="

#echo "== smallfile =="
#./run_script.sh Sfscq smallfile $DEV $ITER > results/Sfscq/smallfile
echo "== largefile =="
./run_script.sh Sfscq largefile $DEV $ITER > results/Sfscq/largefile
#echo "== createdelete =="
#./run_script.sh Sfscq createdelete $DEV $ITER > results/Sfscq/createdelete
#echo "== rename =="
#./run_script.sh Sfscq rename $DEV $ITER > results/Sfscq/rename
