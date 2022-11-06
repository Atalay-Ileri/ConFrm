rm -rf stats
mkdir stats
#python3 process-op-times.py > stats/op-times.txt
#python3 process-fs-times.py > stats/fs-times.txt
#python3 process-syscall-times.py > stats/syscall-times.txt
#python3 process-internal-times.py > stats/internal-times.txt
python3 process-results.py > stats/results.txt
python3 process-results-largefile.py > stats/results-largefile.txt
