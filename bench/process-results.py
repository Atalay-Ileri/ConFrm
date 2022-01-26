import numpy as np

def parse_file(filepath):
    nums = []
    secs = []
    ratios = []
    # open the file and read through it line by line
    with open(filepath, 'r') as f:
        for line in f:
            contents = line.split(' ')
            if (contents[0] != "DATA:"):
              continue
            
            num = float(contents[1])
            sec = float(contents[2])
            nums.append(num)
            secs.append(sec)
            ratios.append((num/sec)*1000000)

    nums_np = np.array(nums)
    secs_np = np.array(secs)
    ratios_np = np.array(ratios)

    #print("Median: ")
    #print(np.median(nums_np))
    #print("Mean: ")
    #print(np.mean(nums_np))
    #print("Std Dev: ")
    #print(np.std(nums_np))
    #print("")

    #print("Median: ")
    #print(np.median(secs_np))
    #print("Mean: ")
    #print(np.mean(secs_np))
    #print("Std Dev: ")
    #print(np.std(secs_np))
    #print("")
    
    print("Median: ")
    print(np.median(ratios_np))
    print("Mean: ")
    print(np.mean(ratios_np))
    print("Std Dev: ")
    print(np.std(ratios_np))
    print("")

if __name__== "__main__":
    print("=== dfscq/smallfile ===")
    parse_file("results/dfscq/smallfile")

    print("=== dfscq/createdelete ===")
    parse_file("results/dfscq/createdelete")

    print("=== dfscq/rename ===")
    parse_file("results/dfscq/rename")


    print("=== db_dfscq/smallfile ===")
    parse_file("results/db_dfscq/smallfile")

    print("=== db_dfscq/createdelete ===")
    parse_file("results/db_dfscq/createdelete")

    print("=== db_dfscq/rename ===")
    parse_file("results/db_dfscq/rename")


    print("=== fa_dfscq/smallfile ===")
    parse_file("results/fa_dfscq/smallfile")

    print("=== fa_dfscq/createdelete ===")
    parse_file("results/fa_dfscq/createdelete")

    print("=== fa_dfscq/rename ===")
    parse_file("results/fa_dfscq/rename")


    print("=== db_fa_dfscq/smallfile ===")
    parse_file("results/db_fa_dfscq/smallfile")

    print("=== db_fa_dfscq/createdelete ===")
    parse_file("results/db_fa_dfscq/createdelete")

    print("=== db_fa_dfscq/rename ===")
    parse_file("results/db_fa_dfscq/rename")


    print("=== sfscq/smallfile ===")
    parse_file("results/sfscq/smallfile")

    print("=== sfscq/createdelete ===")
    parse_file("results/sfscq/createdelete")

    print("=== sfscq/rename ===")
    parse_file("results/sfscq/rename")

