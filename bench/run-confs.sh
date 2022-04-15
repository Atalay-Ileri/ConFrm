ITER=$1

if [ $# -ne 1 ]; then
  echo "$0 iteration-num"
  exit 1
fi

rm -rf results/ConFs
mkdir results
mkdir results/ConFs

echo "=== Running ConFs Tests ==="

echo "== smallfile =="
./run_script.sh Con smallfile /dev/sdb3 $ITER > results/ConFs/smallfile
echo "== largefile =="
./run_script.sh Con largefile /dev/sdb3 $ITER > results/ConFs/largefile
echo "== createdelete =="
./run_script.sh Con createdelete /dev/sdb3 $ITER > results/ConFs/createdelete
echo "== rename =="
./run_script.sh Con rename /dev/sdb3 $ITER > results/ConFs/rename

#python process-results.py > results.txt
#python process-results-largefile.py >> results.txt

# echo "=== ConFs Stats ===" > stat-results.txt
# cat results/ConFs/fsstats >> stat-results.txt
# echo "" >> stat-results.txt
