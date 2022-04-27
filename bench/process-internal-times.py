import process_helpers as ph

if __name__ == "__main__":
    fs_names = ["ConFs", "Cfscq"]
    test_names = ["smallfile", "largefile", "createdelete", "rename"]
    operations = ["Internal ReadInner", "Internal WriteInner", "Internal DeleteInner", "Internal ExtendInner" ,
        "Internal InodeGetOwner", "Internal InodeAlloc", "Internal Auth", "Internal Commit", "Internal Abort",
        "Internal LogCacheWrite", "Internal LogCommit", "Internal LogApply", "Internal WriteBatch",
        "Internal LogReadHeader", "Internal LogCommitTxn",
        "Internal EncryptAll", "Internal HashAll", "Internal WriteConsecutive",
        "Internal UpdateHeader", "Internal DiskWriteBatch", "Internal WriteHeader",
        "Internal DiskSyncCommit", "Internal DiskWriteHeader"]

    for test in test_names:
        for fs in fs_names:
            print("===", fs, test, "===")
            ph.parse_file("results/"+fs+"/"+test, operations)
