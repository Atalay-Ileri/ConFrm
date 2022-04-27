import numpy as np
import matplotlib.pyplot as plt

def reject_outliers(data, m = 15.):
    d = np.abs(data - np.median(data))
    mdev = np.median(d)
    s = d/mdev if mdev else 0.
    return data[s<m]

def parse_file(filepath, operations, without_outliers = False):
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
                    else :
                        print("Negative number")
                except:
                    continue

    np_arrays = {}
    np_means = {}
    np_medians = {}
    np_std_devs = {}
    np_total_time = {}
    for label in operations:
        npa = np.array(arrays[label])
        if without_outliers :
            npa = reject_outliers(npa)
        np_arrays[label] = npa
        np_means[label] = round(np.mean(npa), 0)
        np_medians[label] = round(np.median(npa), 0)
        np_std_devs[label] = round(np.std(npa),0)
        np_total_time[label] = round(np.sum(npa) / 1000000, 2)
        print(label, "\n\tCount:", len(arrays[label]), "ops \n\tMean:", np_means[label], "ns \n\tMedian:", np_medians[label], "ns \n\tTotal:", np_total_time[label], "ms")
        if (len(np_arrays[label]) > 0) :
            x = np.arange(0, len(np_arrays[label]))
            plt.title(filepath + ": " + label)
            plt.ylabel("ns")
            plt.plot(x, np_arrays[label], color ="red")
            plt.show()

    total = 0
    for label in operations:
        total += np_total_time[label]
    print("Total Time:", round(total, 2), "ms")
    print("")
