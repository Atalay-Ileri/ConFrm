import numpy as np

def parse_file(filepath):
    reads = []
    writes = []
    syncs = []
    # open the file and read through it line by line
    with open(filepath, 'r') as f:
        for line in f:
            contents = line.split(': ')
            if (contents[0] == "Disk Read"):
                try:
                    num = float(contents[1])
                    if (num >= 0):
                    	reads.append(num)
                    else:
                    	print("Negative Num")
                except:
                    print("parse error")
            elif (contents[0] == "Disk Write"):
                try:
                    num = float(contents[1])
                    if (num >= 0):
                    	writes.append(num)
                    else:
                    	print("Negative Num")
                except:
                    print("parse error")
            elif (contents[0] == "Disk Sync"):
                try:
                    num = float(contents[1])
                    if (num >= 500):
                    	syncs.append(num)
                    #else:
                    	#print("Negative Num")
                except:
                    print("parse error")

    reads_np = np.array(reads)
    writes_np = np.array(writes)
    syncs_np = np.array(syncs)

    print("--Reads--")
    print("Median: ")
    print(np.median(reads_np))
    print("Mean: ")
    print(np.mean(reads_np))
    print("Std Dev: ")
    print(np.std(reads_np))
    print("")

    print("--Writes--")
    print("Median: ")
    print(np.median(writes_np))
    print("Mean: ")
    print(np.mean(writes_np))
    print("Std Dev: ")
    print(np.std(writes_np))
    print("")
    
    print("--Syncs--")
    print("Median: ")
    print(np.median(syncs_np))
    print("Mean: ")
    print(np.mean(syncs_np))
    print("Std Dev: ")
    print(np.std(syncs_np))
    print("")

if __name__== "__main__":

    print("=== ConFs/smallfile ===")
    parse_file("results/ConFs/smallfile")
    
    print("=== Cfscq/smallfile ===")
    parse_file("results/Cfscq/smallfile")

    print("=== ConFs/createdelete ===")
    parse_file("results/ConFs/createdelete")
    
    print("=== Cfscq/createdelete ===")
    parse_file("results/Cfscq/createdelete")

    print("=== ConFs/rename ===")
    parse_file("results/ConFs/rename")

    print("=== Cfscq/rename ===")
    parse_file("results/Cfscq/rename")

