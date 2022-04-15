ITER=$1

if [ $# -ne 1 ]; then
  echo "$0 iteration-num"
  exit 1
fi

rm -rf results/Cfscq
mkdir results
mkdir results/Cfscq

echo "=== Running Cfscq Tests ==="

echo "== smallfile =="
./run-cfscq-bench.sh Cfscq smallfile /dev/sdb3 $ITER > results/Cfscq/smallfile
echo "== largefile =="
./run-cfscq-bench.sh Cfscq largefile /dev/sdb3 $ITER > results/Cfscq/largefile
echo "== createdelete =="
./run-cfscq-bench.sh Cfscq createdelete /dev/sdb3 $ITER > results/Cfscq/createdelete
echo "== rename =="
./run-cfscq-bench.sh Cfscq rename /dev/sdb3 $ITER > results/Cfscq/rename
