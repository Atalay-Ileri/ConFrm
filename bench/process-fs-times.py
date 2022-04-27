import process_helpers as ph


if __name__ == "__main__":
    fs_names = ["ConFs", "Cfscq"]
    test_names = ["smallfile", "largefile", "createdelete", "rename"]
    operations = ["Fs Read", "Fs Write", "Fs Extend", "Fs Delete",
        "Fs Rename", "Fs Create", "Fs Append", "Fs Lookup", "Fs Resize",
        "Fs Mkdir", "Fs Readdir" ]

    for test in test_names:
        for fs in fs_names:
            print("===", fs, test, "===")
            ph.parse_file("results/"+fs+"/"+test, operations)
