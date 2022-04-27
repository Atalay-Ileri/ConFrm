import process_helpers as ph

if __name__ == "__main__":
    fs_names = ["ConFs", "Cfscq"]
    test_names = ["smallfile", "largefile","createdelete", "rename"]
    operations = ["Disk Read", "Disk Write", "Disk Sync", 
        "Directory Read", "Directory Modify",
        "Cache Read", "Cache Write", "Cache Flush", 
        "List Get", "List Put", "List Delete",
        "Crypto Hash", "Crypto GetKey", "Crypto Encrypt", "Crypto Decrypt"]

    for test in test_names:
        for fs in fs_names:
            print("===", fs, test, "===")
            ph.parse_file("results/"+fs+"/"+test, operations)
