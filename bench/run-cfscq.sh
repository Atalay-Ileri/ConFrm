ITER=$1
DEV=$2

if [ $# -ne 2 ]; then
  echo "$0 iteration-num dev-path"
  exit 1
fi

rm -rf results/Cfscq
mkdir results
mkdir results/Cfscq

echo "=== Running Cfscq Tests ==="

echo "== smallfile =="
./run-cfscq-bench.sh Cfscq smallfile $DEV $ITER > results/Cfscq/smallfile
echo "== largefile =="
./run-cfscq-bench.sh Cfscq largefile $DEV $ITER > results/Cfscq/largefile
echo "== createdelete =="
./run-cfscq-bench.sh Cfscq createdelete $DEV $ITER > results/Cfscq/createdelete
echo "== rename =="
./run-cfscq-bench.sh Cfscq rename $DEV $ITER > results/Cfscq/rename
