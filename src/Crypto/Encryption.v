Require Import Primitives.

Module Type EncryptionSignature.
  Parameter key: Type.
  Parameter data : Type.
  Parameter encrypted_data : Type.
  Parameter encrypt : key -> data -> encrypted_data.
  Parameter decrypt : key -> encrypted_data -> data.
  Parameter encrypted_data_dec: forall h1 h2: encrypted_data, {h1=h2}+{h1<>h2}.
  
  Parameter decrypt_encrypt: forall k ed, encrypt k (decrypt k ed) = ed.
  Parameter encrypt_decrypt: forall k d, decrypt k (encrypt k d) = d.
End EncryptionSignature.


Module Encryption (ES: EncryptionSignature).
  Import ES.
  
  Definition encryptionmap := @mem  encrypted_data encrypted_data_dec (key * data).

  Definition encryption_map_valid (em: encryptionmap) :=
    forall ed k d, em ed = Some (k, d) -> encrypt k d = ed.
  
  Definition encryption_is_safe k d (em: encryptionmap) :=
    let ed := encrypt k d in
    em ed = None \/ em ed = Some (k, d).
End Encryption.

  
  