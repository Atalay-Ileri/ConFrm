ITER=$1
DEV=$2

if [ $# -ne 2 ]; then
  echo "$0 iteration-num dev-path"
  exit 1
fi

rm -rf results/ConFs
mkdir results
mkdir results/ConFs

echo "=== Running ConFs Tests ==="

echo "== smallfile =="
./run_script.sh Con smallfile $DEV $ITER > results/ConFs/smallfile
echo "== largefile =="
./run_script.sh Con largefile $DEV $ITER > results/ConFs/largefile
echo "== createdelete =="
./run_script.sh Con createdelete $DEV $ITER > results/ConFs/createdelete
echo "== rename =="
./run_script.sh Con rename $DEV $ITER > results/ConFs/rename

#python process-results.py > results.txt
#python process-results-largefile.py >> results.txt

# echo "=== ConFs Stats ===" > stat-results.txt
# cat results/ConFs/fsstats >> stat-results.txt
# echo "" >> stat-results.txt
