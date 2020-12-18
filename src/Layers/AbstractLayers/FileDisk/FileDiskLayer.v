Require Import Lia Framework.
Import ListNotations.
Close Scope predicate_scope.

Set Implicit Arguments.

Section FileDisk.

  Variable disk_size : nat.
  Notation "'Inum'" := addr.

  Inductive token' :=
  | CrashBefore : token'
  | CrashAfter : token'
  | CrashAfterCreate : Inum -> token'
  | NewInum : Inum -> token'
  | InodesFull : token'
  | DiskFull : token'
  | Cont : token'.

  Definition state' := (user * disk File)%type.
  
  Inductive file_disk_prog : Type -> Type :=
  | Read : Inum -> addr -> file_disk_prog (option value)
  | Write : Inum -> addr -> value -> file_disk_prog (option unit)
  | Extend : Inum -> value -> file_disk_prog (option unit)
  | SetOwner : Inum -> user -> file_disk_prog (option unit)
  | Create : user -> file_disk_prog (option addr)
  | Delete : Inum -> file_disk_prog (option unit)
  | Recover : file_disk_prog unit.
  
  Inductive exec' :
    forall T, token' ->  state' -> file_disk_prog T -> @Result state' T -> Prop :=
  | ExecReadSuccess : 
      forall s inum off file v,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        nth_error file.(blocks) off = Some v ->
        exec' Cont s (Read inum off) (Finished s (Some v))
              
  | ExecReadFail : 
      forall s inum off file,
        let u := fst s in
        let d := snd s in
        (inum >= disk_size \/
         d inum = None \/
         d inum = Some file /\
         (file.(owner) <> u \/ nth_error file.(blocks) off = None)) ->
        exec' Cont s (Read inum off) (Finished s None)
              
  | ExecWriteSuccess :
      forall s inum file off v,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        off < length (file.(blocks)) ->
        let new_file := Build_File file.(owner) (updN file.(blocks) off v) in
        exec' Cont s (Write inum off v) (Finished (u, (upd d inum new_file)) (Some tt))

  | ExecWriteFail :
      forall s inum file off v,
        let u := fst s in
        let d := snd s in
        (inum >= disk_size \/
         d inum = None \/
         d inum = Some file /\
         (file.(owner) <> u \/ off >= length (file.(blocks)))) ->
        exec' Cont s (Write inum off v) (Finished s None)

  | ExecExtendSuccess :
      forall s inum file v,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
        exec' Cont s (Extend inum v) (Finished (u, (upd d inum new_file)) (Some tt))

  | ExecExtendFail :
      forall s inum file v,
        let u := fst s in
        let d := snd s in
        (inum >= disk_size \/
         d inum = None \/
         (d inum = Some file /\ file.(owner) <> u)) ->
        exec' Cont s (Extend inum v) (Finished s None)
              
  | ExecExtendFailDiskFull :
      forall s inum file v,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        exec' DiskFull s (Extend inum v) (Finished s None)

  | ExecSetOwnerSuccess :
      forall s inum file o,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        let new_file := Build_File o file.(blocks) in
        exec' Cont s (SetOwner inum o) (Finished (u, (upd d inum new_file)) (Some tt))

  | ExecSetOwnerFail :
      forall s inum file o,
        let u := fst s in
        let d := snd s in
        (inum >= disk_size \/
         d inum = None \/
         (d inum = Some file /\ file.(owner) <> u)) ->
        exec' Cont s (SetOwner inum o) (Finished s None)

  | ExecCreateSuccess :
      forall s inum owner,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = None ->
        let new_file := Build_File owner [] in
        exec' (NewInum inum) s (Create owner) (Finished (u, (upd d inum new_file)) (Some inum))

  | ExecCreateFail :
      forall s owner,
        let u := fst s in
        let d := snd s in
        (forall inum, inum < disk_size -> d inum <> None) ->
        exec' InodesFull s (Create owner) (Finished s None)
              
  | ExecDeleteSuccess :
      forall s inum file,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        exec' Cont s (Delete inum) (Finished (u, (Mem.delete d inum)) (Some tt))

  | ExecDeleteFail :
      forall s file inum,
        let u := fst s in
        let d := snd s in
        (inum >= disk_size \/
         d inum = None \/
         (d inum = Some file /\ file.(owner) <> u)) ->
        exec' Cont s (Delete inum) (Finished s None)

  | ExecRecover : 
      forall s,
        exec' Cont s Recover (Finished s tt)

  | ExecCrashBefore :
      forall d T (p: file_disk_prog T),
        exec' CrashBefore d p (Crashed d)

  | ExecSetOwnerCrashAfter :
      forall s inum file o,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        let new_file := Build_File o file.(blocks) in
        exec' CrashAfter s (SetOwner inum o) (Crashed (u, (upd d inum new_file)))

  | ExecWriteCrashAfter :
      forall s inum file off v,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        off < length (file.(blocks)) ->
        let new_file := Build_File file.(owner) (updN file.(blocks) off v) in
        exec' CrashAfter s (Write inum off v) (Crashed (u, (upd d inum new_file)))

  | ExecExtendCrashAfter :
      forall s inum file v,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
        exec' CrashAfter s (Extend inum v) (Crashed (u, (upd d inum new_file)))

  | ExecDeleteCrashAfter :
      forall s inum file,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        exec' CrashAfter s (Delete inum) (Crashed (u, (Mem.delete d inum)))

  | ExecCreateCrashAfter :
      forall s inum owner,
        let u := fst s in
        let d := snd s in
        inum < disk_size ->
        d inum = None ->
        let new_file := Build_File owner [] in
        exec' (CrashAfterCreate inum) s (Create owner) (Crashed (u, (upd d inum new_file))).

  Hint Constructors exec' : core.

  Definition weakest_precondition' T (p: file_disk_prog T) :=
    match p in file_disk_prog T' return (T' -> state' -> Prop) -> token' -> state' -> Prop with
    | Read inum a =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = Cont /\
          inum < disk_size /\
          exists file v,
            d inum = Some file /\
            nth_error file.(blocks) a = Some v /\
            file.(owner) = u /\
            Q (Some v) s
        ) \/
        (
          o = Cont /\
          (inum >= disk_size \/
           d inum = None \/
           (exists file,
              d inum = Some file /\
              (
                file.(owner) <> u \/
                nth_error file.(blocks) a = None
              )
           )
          ) /\
          Q None s
        )
          
    | Write inum a v =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = Cont /\
          inum < disk_size /\  
          exists file,
            d inum = Some file /\
            file.(owner) = u /\
            a < length (file.(blocks)) /\
            let new_file :=
                Build_File file.(owner) (updN file.(blocks) a v) in
            Q (Some tt) (u, upd d inum new_file)
        ) \/
        (
          o = Cont /\
          (inum >= disk_size \/
           d inum = None \/
           (exists file,
              d inum = Some file /\
              (
                file.(owner) <> u \/
                a >= length (file.(blocks))
              )
           )
          ) /\
          Q None s
        )
          
    | SetOwner inum u' =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = Cont /\
          inum < disk_size /\
          exists file,
            let new_file := Build_File u' file.(blocks) in
            d inum = Some file /\
            file.(owner) = u /\
            Q (Some tt) (u, upd d inum new_file)
        ) \/
        (
          o = Cont /\
          (inum >= disk_size \/ d inum = None \/
           exists file,
             d inum = Some file /\
             file.(owner) <> u) /\
          Q None s
        )
          
    | Create u' =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = InodesFull /\
          (forall inum, inum < disk_size -> d inum <> None) /\
          Q None s
        ) \/

        (exists inum,
           o = NewInum inum /\
           inum < disk_size /\ 
           d inum = None /\
           let new_file := Build_File u' [] in
           Q (Some inum) (u, upd d inum new_file)
        )
          
    | Delete inum =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = Cont /\
          inum < disk_size /\
          (exists file,
             d inum = Some file /\ 
             file.(owner) = u) /\
          Q (Some tt) (u, Mem.delete d inum)
        ) \/
        (
          o = Cont /\
          (inum >= disk_size \/
           d inum = None \/
           exists file,
             d inum = Some file /\
             file.(owner) <> u) /\
          Q None s
        )
    | Extend inum v =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = DiskFull /\
          inum < disk_size /\
          (exists file,
             d inum = Some file /\ 
             file.(owner) = u) /\
          Q None s
        ) \/
        (
          o = Cont /\
          inum < disk_size /\
          exists file,
            d inum = Some file /\
            file.(owner) = u /\
            let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
            Q (Some tt) (u, upd d inum new_file)
        ) \/
        (
          o = Cont /\
          (inum >= disk_size \/ d inum = None \/
           exists file,
             d inum = Some file /\
             file.(owner) <> u) /\
          Q None s
        )
    | Recover =>
      fun Q o s =>
        o = Cont /\
        Q tt s
    end.

  
  Definition weakest_crash_precondition' T (p: file_disk_prog T) :=
    match p in file_disk_prog T' return (state' -> Prop) -> token' -> state' -> Prop with
    | Read inum a =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = CrashBefore /\
          Q s
        )
          
    | Write inum a v =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = CrashBefore /\
          Q s
        ) \/
        (
          o = CrashAfter /\
          inum < disk_size /\  
          exists file,
            d inum = Some file /\
            file.(owner) = u /\
            a < length (file.(blocks)) /\
            let new_file :=
                Build_File file.(owner) (updN file.(blocks) a v) in
            Q (u, upd d inum new_file)
        )
          
    | SetOwner inum u' =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = CrashBefore /\
          Q s
        ) \/
        (
          o = CrashAfter /\
          inum < disk_size /\
          exists file,
            let new_file := Build_File u' file.(blocks) in
            d inum = Some file /\
            file.(owner) = u /\
            Q (u, upd d inum new_file)
        )
          
    | Create u' =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = CrashBefore /\
          Q s
        ) \/
        (exists inum,
           o = CrashAfterCreate inum /\
           inum < disk_size /\ 
           d inum = None /\
           let new_file := Build_File u' [] in
           Q (u, upd d inum new_file)
        )
          
    | Delete inum =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = CrashBefore /\
          Q s
        ) \/
        (
          o = CrashAfter /\
          inum < disk_size /\
          (exists file,
             d inum = Some file /\
             file.(owner) = u) /\
          Q (u, Mem.delete d inum)
        )
          
    | Extend inum v =>
      fun Q o s =>
        let u := fst s in
        let d := snd s in
        (
          o = CrashBefore /\
          Q s
        ) \/
        (
          o = CrashAfter /\
          inum < disk_size /\
          exists file,
            d inum = Some file /\
            file.(owner) = u /\
            let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
            Q (u, upd d inum new_file)
        )
    | Recover =>
      fun Q o s =>
        o = CrashBefore /\
        Q s
    end.

  Definition strongest_postcondition' T (p: file_disk_prog T) :=
    match p in file_disk_prog T' return (token' -> state' -> Prop) -> T' -> state' -> Prop with
    | Read inum a =>
      fun P t s' =>
        (
          exists s,
            let u := fst s in
            let d := snd s in
            P Cont s /\
            inum < disk_size /\
            exists file v,
              d inum = Some file /\
              file.(owner) = u /\
              nth_error file.(blocks) a = Some v /\
              t = Some v /\
              s' = s
        ) \/
        (
          exists s,
            let u := fst s in
            let d := snd s in
            P Cont s /\
            (inum >= disk_size \/
             d inum = None \/
             (exists file,
                d inum = Some file /\
                (
                  file.(owner) <> u \/
                  nth_error file.(blocks) a = None
                )
             )
            ) /\
            t = None /\
            s' = s
        )
          
    | Write inum a v =>
      fun P t s' =>
        (
          exists s,
            let u := fst s in
            let d := snd s in
            P Cont s /\
            inum < disk_size /\  
            exists file,
              d inum = Some file /\
              file.(owner) = u /\
              a < length (file.(blocks)) /\
              let new_file :=
                  Build_File file.(owner) (updN file.(blocks) a v) in
              t = (Some tt) /\
              s' = (u, upd d inum new_file)
        ) \/
        (
          exists s,
            let u := fst s in
            let d := snd s in
            P Cont s /\
            (inum >= disk_size \/
             d inum = None \/
             (exists file,
                d inum = Some file /\
                (
                  file.(owner) <> u \/
                  a >= length (file.(blocks))
                )
             )
            ) /\
            t = None /\
            s' = s
        )
          
    | SetOwner inum u' =>
      fun P t s' =>
        (exists s,
           let u := fst s in
           let d := snd s in
           P Cont s /\
           inum < disk_size /\
           exists file,
             let new_file := Build_File u' file.(blocks) in
             d inum = Some file /\
             file.(owner) = u /\
             t = (Some tt) /\
             s' = (u, upd d inum new_file)
        ) \/
        (exists s,
           let u := fst s in
           let d := snd s in
           P Cont s /\
           (inum >= disk_size \/
            d inum = None \/
            exists file,
              d inum = Some file /\
              file.(owner) <> u) /\
           t = None /\
           s' = s
        )
          
    | Create u' =>
      fun P t s' =>
        (exists s,
           let u := fst s in
           let d := snd s in
           P InodesFull s /\
           (forall inum, inum < disk_size -> d inum <> None) /\
           t = None /\
           s' = s
        ) \/
        (exists s inum,
           let u := fst s in
           let d := snd s in
           P (NewInum inum) s /\
           inum < disk_size /\ 
           d inum = None /\
           let new_file := Build_File u' [] in
           t = (Some inum) /\
           s' = (u, upd d inum new_file)
        )
          
    | Delete inum =>
      fun P t s' =>
        (
          exists s,
            let u := fst s in
            let d := snd s in
            P Cont s /\
            inum < disk_size /\
            (exists file,
               d inum = Some file /\
               file.(owner) = u
            ) /\
            t = (Some tt) /\
            s' = (u, Mem.delete d inum)
        ) \/
        (exists s,
           let u := fst s in
           let d := snd s in
           P Cont s /\
           (inum >= disk_size \/
            d inum = None \/
            exists file,
              d inum = Some file /\
              file.(owner) <> u) /\
           t = None /\
           s' = s
        )
          
    | Extend inum v =>
      fun P t s' =>
        (exists s,
           let u := fst s in
           let d := snd s in
           P DiskFull s /\
           inum < disk_size /\
           (exists file,
              d inum = Some file /\
              file.(owner) = u) /\
           t = None /\
           s' = s
        ) \/
        (exists s,
           let u := fst s in
           let d := snd s in
           P Cont s /\
           inum < disk_size /\
           exists file,
             d inum = Some file /\
             file.(owner) = u /\
             let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
             t = (Some tt) /\
             s' = (u, upd d inum new_file)
        ) \/
        (exists s,
           let u := fst s in
           let d := snd s in
           P Cont s /\
           (inum >= disk_size \/
            d inum = None \/
            exists file,
              d inum = Some file /\
              file.(owner) <> u) /\
           t = None /\
           s' = s
        )
    | Recover =>
      fun P t s' =>
          exists s,
            P Cont s /\
            t = tt /\
            s' = s
    end.
  
  Definition strongest_crash_postcondition' T (p: file_disk_prog T) :=
    match p in file_disk_prog T' return (token' -> state' -> Prop) -> state' -> Prop with
    | Read inum a =>
      fun P s' =>
        (exists s,
           P CrashBefore s /\
           s' = s
        )
          
    | Write inum a v =>
      fun P s' =>
        (exists s,
           P CrashBefore s /\
           s' = s
        ) \/
        (exists s,
           let u := fst s in
           let d := snd s in
           P CrashAfter s /\
           inum < disk_size /\  
           exists file,
             d inum = Some file /\
             file.(owner) = u /\
             a < length (file.(blocks)) /\
             let new_file :=
                 Build_File file.(owner) (updN file.(blocks) a v) in
             s' = (u, upd d inum new_file)
        )
          
    | SetOwner inum u' =>
      fun P s' =>
        (exists s,
           P CrashBefore s /\
           s' = s
        ) \/
        (exists s,
           let u := fst s in
           let d := snd s in
           P CrashAfter s /\
           inum < disk_size /\
           exists file,
             let new_file := Build_File u' file.(blocks) in
             d inum = Some file /\
             file.(owner) = u /\
             s' = (u, upd d inum new_file)
        )
          
    | Create u' =>
      fun P s' =>
        (exists s,
           P CrashBefore s /\
           s' = s
        ) \/
        (exists s inum,
           let u := fst s in
           let d := snd s in
           P (CrashAfterCreate inum) s /\
           inum < disk_size /\ 
           d inum = None /\
           let new_file := Build_File u' [] in
           s' = (u, upd d inum new_file)
        )
          
    | Delete inum =>
      fun P s' =>
        (exists s,
           P CrashBefore s /\
           s' = s
        ) \/
        (exists s,
           let u := fst s in
           let d := snd s in
           P CrashAfter s /\
           inum < disk_size /\
           (exists file,
              d inum = Some file /\
             file.(owner) = u) /\
           s' = (u, Mem.delete d inum)
        )
    | Extend inum v =>
      fun P s' =>
        (exists s,
           P CrashBefore s /\
           s' = s
        ) \/
        (exists s,
           let u := fst s in
           let d := snd s in
           P CrashAfter s /\
           inum < disk_size /\
           exists file,
             d inum = Some file /\
             file.(owner) = u /\
             let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
             s' = (u, upd d inum new_file)
        )

    | Recover =>
      fun P s' =>
        exists s,
           P CrashBefore s /\
           s' = s
    end.

  Arguments skipn : simpl never.
  Theorem sp_complete':
    forall T (p: file_disk_prog T) P (Q: _ -> _ -> Prop),
      (forall t s', strongest_postcondition' p P t s' -> Q t s') <->
      (forall o s s' t, P o s -> exec' o s p (Finished s' t) -> Q t s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    repeat (split_ors; cleanup; eauto);
    eapply H; eauto;
    try match goal with
        | [H: exec' _ _ _ _ |- _] =>
          inversion H; clear H; cleanup
        end;
    try solve [left; eexists; intuition eauto;               
               repeat eexists; intuition eauto; cleanup; simpl; eauto ];
    try solve [right; repeat eexists; intuition eauto ];
    try solve [intuition eauto;
               repeat eexists; intuition eauto;
               try solve [ econstructor; eauto ];
               simpl; cleanup; eauto ];
    rewrite <- H3 at 2; eauto.
    
    Unshelve.
    all: repeat econstructor; eauto.
    all: exact user0.
  Qed.

  Theorem scp_complete':
    forall T (p: file_disk_prog T) P (Q:  _ -> Prop),
      (forall s', strongest_crash_postcondition' p P s' -> Q s') <->
      (forall o s s', P o s -> exec' o s p (Crashed s') -> Q s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    repeat (split_ors; cleanup);
    eapply H; eauto;
    repeat
      match goal with
      | [H: exec' _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end;
    try solve [left; eexists; intuition eauto;               
               repeat eexists; intuition eauto; cleanup; simpl; eauto ];
    try solve [right; repeat eexists; intuition eauto ];
    try solve [intuition eauto;
               repeat eexists; intuition eauto;
               try solve [
                     econstructor;
                     [| try solve [
                              try rewrite <- H3 at 2;
                              econstructor;  eauto
                            ]
                     ]; eauto
                   ];
               simpl; cleanup; eauto
              ].

    try rewrite <- H3 at 2;
    econstructor;  eauto.
    try rewrite <- H3 at 2;
    econstructor;  eauto.
    
    Unshelve.
    all: repeat econstructor; eauto.
    all: exact user0.
  Qed.
  
    Theorem wp_complete':
    forall T (p: file_disk_prog T) H Q,
      (forall o s, H o s -> weakest_precondition' p Q o s) <->
      (forall o s, H o s -> (exists s' v, exec' o s p (Finished s' v) /\ Q v s')).
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    try match goal with
        | [H: exec' _ _ _ _ |- _] =>
          inversion H; clear H; cleanup
        end;
    try solve [
          repeat (split_ors; cleanup; eauto);
          do 2 eexists; intuition eauto;
          try solve [ econstructor; eauto ];
          simpl; cleanup; eauto ];
    try solve [
          left; intuition eauto;
          do 2 eexists; intuition eauto;
          try solve [ econstructor; eauto ];
          simpl; cleanup; eauto ];
    try solve [
          right;intuition eauto;
          do 2 eexists; intuition eauto;
          try solve [ econstructor; eauto ];
          simpl; cleanup; eauto ].
    
    Unshelve.
    all: repeat econstructor; eauto.
    all: exact user0.
  Qed.
  
  Theorem wcp_complete':
    forall T (p: file_disk_prog T) H C,
      (forall o s, H o s -> weakest_crash_precondition' p C o s) <->
      (forall o s, H o s -> (exists s', exec' o s p (Crashed s') /\ C s')).
  Proof.
    unfold weakest_crash_precondition';
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    try repeat
        match goal with
        | [H: exec' _ _ _ _ |- _] =>
          inversion H; clear H; cleanup
        end;

    try solve [
          repeat (split_ors; cleanup; eauto);
          repeat eexists; intuition eauto;
          try solve [ repeat econstructor; eauto; congruence ];
          try congruence; simpl; cleanup; eauto ];
    try solve [
          left; intuition eauto;
          repeat eexists; intuition eauto;
          try solve [ econstructor; eauto ];
          simpl; cleanup; eauto ];
    try solve [
          right;intuition eauto;
          repeat eexists; intuition eauto;
          try solve [ econstructor; eauto ];
          simpl; cleanup; eauto ].
    
    Unshelve.
    all: repeat econstructor; eauto.
    all: exact user0.
  Qed.

  Theorem exec_deterministic_wrt_token' :
    forall o s T (p: file_disk_prog T) ret1 ret2,
      exec' o s p ret1 ->
      exec' o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ |- _] =>
        inversion H; clear H; try split_ors; cleanup
      end;
    try solve [ repeat (cleanup; intuition eauto; try congruence; try lia) ].
  Qed.
  
  Definition FileDiskOperation :=
    Build_Core
      file_disk_prog
      exec'
      (*
        weakest_precondition'
      weakest_crash_precondition'
      strongest_postcondition'
      strongest_crash_postcondition'
      wp_complete'
      wcp_complete'
      sp_complete'
      scp_complete'
       *)
      exec_deterministic_wrt_token'.

  Definition FileDiskLang := Build_Language FileDiskOperation.

End FileDisk.
