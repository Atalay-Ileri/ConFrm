import numpy as np

def parse_file(filepath):
    makenums = []
    makethr = []
    writenums = []
    writethr = []

    # open the file and read through it line by line
    with open(filepath, 'r') as f:
        for line in f:
            if (line.split(' ')[0] == "makefile") :
                num = float(line.split(' ')[3])
                sec = float(line.split(' ')[6])
                makenums.append(num)
                makethr.append(sec/1024.0)

            if (line.split(' ')[0] == "writefile") :
                num = float(line.split(' ')[3])
                sec = float(line.split(' ')[6])
                writenums.append(num)
                writethr.append(sec/1024.0)

    makenums_np = np.array(makenums)
    makethr_np = np.array(makethr)
    writenums_np = np.array(writenums)
    writethr_np = np.array(writethr)

    #print("Makefile Time:")
    #print("Mean")
    #print(np.mean(makenums_np))
    #print("Median")
    #print(np.median(makenums_np))
    #print("Std Dev")
    #print(np.std(makenums_np))
    #print("")


    print("Makefile Throughput:")
    print("Mean")
    print(np.mean(makethr_np))
    print("Median")
    print(np.median(makethr_np))
    print("Std Dev")
    print(np.std(makethr_np))
    print("")


    #print("Writefile Time:")
    #print("Mean")
    #print(np.mean(writenums_np))
    #print("Median")
    #print(np.median(writenums_np))
    #print("Std Dev")
    #print(np.std(writenums_np))
    #print("")

    print("Writefile Throughput:")
    print("Mean")
    print(np.mean(writethr_np))
    print("Median")
    print(np.median(writethr_np))
    print("Std Dev")
    print(np.std(writethr_np))
    print("")

if __name__== "__main__":
    fs_names = ["ConFs", "Cfscq", "Sfscq"]
    test_names = ["largefile"]
    for test in test_names:
        for fs in fs_names:
            print("===", fs, test, "===")
            parse_file("results/"+fs+"/"+test)
