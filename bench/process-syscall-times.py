from unicodedata import decimal
import numpy as np


def parse_file(filepath):
    operations = ["Syscall Read", "Syscall Write", "Syscall Delete",
        "Syscall Rename", "Syscall Create"]
    arrays = {}
    for label in operations:
        arrays[label] = []

    # open the file and read through it line by line
    with open(filepath, 'r') as f:
        for line in f:
            contents = line.split(': ')
            if (contents[0] in operations):
                try:
                    num = float(contents[1])
                    if (num >= 0):
                        arrays[contents[0]].append(num)
                except:
                    continue

    np_means = {}
    np_medians = {}
    np_std_devs = {}
    np_total_time = {}
    
    for label in operations:
        npa = np.array(arrays[label])
        np_means[label] = round(np.mean(npa)/1000000, 2)
        np_medians[label] = round(np.median(npa), 0)
        np_std_devs[label] = round(np.std(npa),0)
        np_total_time[label] = round(np.sum(npa) / 1000000, 2)
        print(label, "\n\tCount:", len(arrays[label]), "ops \n\tMean:", np_means[label], "ms \n\tTotal:", np_total_time[label], "ms")


    total = 0
    for label in operations:
        total += np_total_time[label]
    print("Total Time:", round(total, 2), "ms")
    print("")

if __name__ == "__main__":
    fs_names = ["ConFs", "Cfscq"]
    test_names = ["smallfile", "createdelete", "rename"]
    for test in test_names:
        for fs in fs_names:
            print("===", fs, test, "===")
            parse_file("results/"+fs+"/"+test)
