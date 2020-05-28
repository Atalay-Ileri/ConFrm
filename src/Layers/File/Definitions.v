Require Import Framework Inode File.
Import ListNotations.
Close Scope pred_scope.

Set Implicit Arguments.
  
  Inductive token' :=
  | CrashBefore : token'
  | CrashAfter : token'
  | CrashAfterCreate : Inum -> token'
  | NewInum : Inum -> token'
  | InodesFull : token'
  | DiskFull : token'
  | Cont : token'.

  Definition token_dec' : forall (t t': token'), {t=t'}+{t<>t'}.
    decide equality.
    all: apply  addr_dec.
  Defined.

  Definition oracle' := list token'.  

  Definition state' := disk File.
  
  Inductive prog' : Type -> Type :=
  | Read : Inum -> addr -> prog' (option value)
  | Write : Inum -> addr -> value -> prog' (option unit)
  | Extend : Inum -> value -> prog' (option unit) 
  | SetOwner : Inum -> user -> prog' (option unit)
  | Create : user -> prog' (option addr)
  | Delete : Inum -> prog' (option unit).
   
  Inductive exec' :
    forall T, oracle' ->  state' -> prog' T -> @Result state' T -> Prop :=
  | ExecReadSuccess : 
      forall d inum off file v,
        d inum = Some file ->
        nth_error file.(blocks) off = Some v ->
        exec' [Cont] d (Read inum off) (Finished d (Some v))
              
  | ExecReadFail : 
      forall d inum off file,
        (d inum = None \/
         d inum = Some file /\ nth_error file.(blocks) off = None) ->
        exec' [Cont] d (Read inum off) (Finished d None)
             
  | ExecWriteSuccess :
      forall d inum file off v,
        d inum = Some file ->
        off < length (file.(blocks)) ->
        let new_file := Build_File file.(owner) (firstn off file.(blocks) ++ v :: skipn (S off) file.(blocks)) in
        exec' [Cont] d (Write inum off v) (Finished (upd d inum new_file) (Some tt))

  | ExecWriteFail :
      forall d inum file off v,
        (d inum = None \/
        d inum = Some file /\ off >= length (file.(blocks))) ->
        exec' [Cont] d (Write inum off v) (Finished d None)

  | ExecExtendSuccess :
      forall d inum file v,
        d inum = Some file ->
        let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
        exec' [Cont] d (Extend inum v) (Finished (upd d inum new_file) (Some tt))

  | ExecExtendFail :
      forall d inum v,
        d inum = None ->
        exec' [Cont] d (Extend inum v) (Finished d None)
              
  | ExecExtendFailDiskFull :
      forall d inum file v,
        d inum = Some file ->
        exec' [DiskFull] d (Extend inum v) (Finished d None)

  | ExecSetOwnerSuccess :
      forall d inum file u,
        d inum = Some file ->
        let new_file := Build_File u file.(blocks) in
        exec' [Cont] d (SetOwner inum u) (Finished (upd d inum new_file) (Some tt))

  | ExecSetOwnerFail :
      forall d inum u,
        d inum = None ->
        exec' [Cont] d (SetOwner inum u) (Finished d None)

  | ExecCreateSuccess :
      forall d inum u,
        inum < Definitions.inode_count ->
        d inum = None ->
        let new_file := Build_File u [] in
        exec' [NewInum inum] d (Create u) (Finished (upd d inum new_file) (Some inum))

  | ExecCreateFail :
      forall d u,
        (forall inum, inum < Definitions.inode_count -> d inum <> None) ->
        exec' [DiskFull] d (Create u) (Finished d None)
              
  | ExecDeleteSuccess :
      forall d inum file,
        d inum = Some file ->
        exec' [Cont] d (Delete inum) (Finished (Mem.delete d inum) (Some tt))

  | ExecDeleteFail :
      forall d inum,
        d inum = None ->
        exec' [Cont] d (Delete inum) (Finished d None)

  | ExecCrashBefore :
      forall d T (p: prog' T),
        exec' [CrashBefore] d p (Crashed d)

  | ExecCrashAfter :
      forall d T (p: prog' T) d' r,
        exec' [Cont] d p (Finished d' r) ->
        exec' [CrashAfter] d p (Crashed d')

  | ExecCreateCrashAfter :
      forall d inum u,
        d inum = None ->
        let new_file := Build_File u [] in
        exec' [CrashAfterCreate inum] d (Create u) (Finished (upd d inum new_file) (Some inum)).

  Hint Constructors exec' : core.

   Definition weakest_precondition' T (p: prog' T) :=
   match p in prog' T' return (T' -> state' -> Prop) -> oracle' -> state' -> Prop with
   | Read inum a =>
     fun Q o s =>
       exists file v,
         o = [Cont] /\

         ((s inum = Some file /\
         nth_error file.(blocks) a = Some v /\
         Q (Some v) s) \/
         
         ((s inum = None \/
          (s inum = Some file /\
           nth_error file.(blocks) a = None)) /\
          Q None s))
           
   | Write inum a v =>
     fun Q o s =>
        exists file,
          o = [Cont] /\
          
          ((s inum = Some file /\
           a < length (file.(blocks)) /\
           let new_file :=
               Build_File file.(owner)
               (firstn a file.(blocks) ++ v :: skipn (S a) file.(blocks)) in
           Q (Some tt) (upd s inum new_file)) \/
          
        ((s inum = None \/
          (s inum = Some file /\
           a >= length (file.(blocks)))) /\
         Q None s))
            
   | SetOwner inum u =>
     fun Q o s =>
        exists file,
        let new_file := Build_File u file.(blocks) in
        o = [Cont] /\

        ((s inum = Some file /\
        Q (Some tt) (upd s inum new_file)) \/

        (s inum = None /\
         Q None s))
          
   | Create u =>
     fun Q o s =>
        (forall inum,
           o = [DiskFull] /\
           (inum < Definitions.inode_count -> s inum <> None) /\
           Q None s) \/

        (exists inum,
           o = [NewInum inum] /\
           inum < Definitions.inode_count /\ 
           s inum = None /\
           let new_file := Build_File u [] in
           Q (Some inum) (upd s inum new_file))
       
   | Delete inum =>
       fun Q o s =>
        exists file,
        o = [Cont] /\

        ((s inum = Some file /\
          Q (Some tt) (Mem.delete s inum)) \/

         (s inum = None /\
          Q None s))
   end.

   Definition weakest_crash_precondition' T (p: prog' T) :=
    match p in prog' T' return (state' -> Prop) -> oracle' -> state' -> Prop with
   | Read a =>
     (fun Q o s =>
         o = [CrashBefore] /\
         Q s)
   | Write la lv =>
     (fun Q o s =>
       (o = [CrashBefore] /\
        Q s) \/
       (o = [CrashAfter] /\
        Q (write_all s la lv)))
    end.

  Definition strongest_postcondition' T (p: prog' T) :=
   match p in prog' T' return (oracle' -> state' -> Prop) -> T' -> state' -> Prop with
   | Read inum a =>
     (fun Q o s =>
       exists file v,
         o = [Cont] /\
         s inum = Some file /\
         nth_error file.(blocks) a = Some v /\
         Q v s)
   | Write inum a v =>
     (fun Q o s =>
        exists file,
        o = [Cont] /\
        s inum = Some file /\
        let new_file :=
            Build_File file.(owner)
            (firstn a file.(blocks) ++ v :: skipn (S a) file.(blocks)) in
        Q tt (upd s inum new_file))
   | SetOwner inum u =>
     (fun Q o s =>
        exists file,
        o = [Cont] /\
        s inum = Some file /\
        let new_file :=
            Build_File u file.(blocks) in
        Q tt (upd s inum new_file))
       
   | Create u =>
     (fun Q o s =>
        let new_file := Build_File u [] in

        (forall inum,
           o = [DiskFull] /\
           (inum < Definitions.inode_count -> s inum <> None) /\
           Q None s) \/
        
        (exists inum,
           o = [NewInum inum] /\
           inum < Definitions.inode_count /\ 
           s inum = None /\
           Q (Some inum) (upd s inum new_file)))
     | Delete inum =>
       (fun Q o s =>
        exists file,
        o = [Cont] /\
        s inum = Some file /\
        Q tt (Mem.delete s inum))
   end.

  Definition strongest_crash_postcondition' T (p: prog' T) :=
    match p in prog' T' return (oracle' -> state' -> Prop) -> state' -> Prop with
   | Read a =>
     fun P s' =>
       P [CrashBefore] s'
   | Write la lv =>
     fun P s' =>
       (P [CrashBefore] s') \/
       (exists s,
          P [CrashAfter] s /\
          s' = write_all s la lv)
    end.
  
  Theorem sp_complete':
    forall T (p: prog' T) P (Q: _ -> _ -> Prop),
      (forall t s', strongest_postcondition' p P t s' -> Q t s') <->
      (forall o s s' t, P o s -> exec' o s p (Finished s' t) -> Q t s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    eapply H; eauto;
    do 2 eexists; eauto.    
  Qed.

  Theorem scp_complete':
    forall T (p: prog' T) P (Q:  _ -> Prop),
      (forall s', strongest_crash_postcondition' p P s' -> Q s') <->
      (forall o s s', P o s -> exec' o s p (Crashed s') -> Q s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    try split_ors; eapply H; eauto.
  Qed.

  Theorem wp_complete':
    forall T (p: prog' T) H Q,
      (forall o s, H o s -> weakest_precondition' p Q o s) <->
      (forall o s, H o s -> (exists s' v, exec' o s p (Finished s' v) /\ Q v s')).
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    inversion H0; cleanup; eauto.
  Qed.
  
  Theorem wcp_complete':
    forall T (p: prog' T) H C,
      (forall o s, H o s -> weakest_crash_precondition' p C o s) <->
      (forall o s, H o s -> (exists s', exec' o s p (Crashed s') /\ C s')).
  Proof.
    unfold weakest_crash_precondition';
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    inversion H0; cleanup; eauto.
  Qed.

  Theorem exec_deterministic_wrt_oracle' :
    forall o s T (p: prog' T) ret1 ret2,
      exec' o s p ret1 ->
      exec' o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
  Qed.
  
  Definition LoggedDiskOperation :=
    Build_Operation
      (list_eq_dec token_dec')
      prog'
      exec'
      weakest_precondition'
      weakest_crash_precondition'
      strongest_postcondition'
      strongest_crash_postcondition'
      wp_complete'
      wcp_complete'
      sp_complete'
      scp_complete'
      exec_deterministic_wrt_oracle'.

  Definition LoggedDiskLang := Build_Language LoggedDiskOperation.
  Definition LoggedDiskHL := Build_HoareLogic LoggedDiskLang.

Notation "| p |" := (Op LoggedDiskOperation p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op LoggedDiskOperation p1) (fun x => p2))(right associativity, at level 60). 
Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
