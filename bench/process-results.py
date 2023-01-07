import numpy as np

def parse_file(filepath):
    nums = []
    secs = []
    ratios = []
    # open the file and read through it line by line
    with open(filepath, 'r') as f:
        for line in f:
            if ("DATA:" in line):
                contents = line.split("DATA: ")
                nums = contents[1].split(" ")        
                num = float(nums[0])
                sec = float(nums[1])
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
    fs_names = ["ConFs", "Cfscq", "Sfscq", "ext4"]
    test_names = ["smallfile", "createdelete", "rename"]
    for test in test_names:
        for fs in fs_names:
            print("===", fs, test, "===")
            parse_file("results/"+fs+"/"+test)

