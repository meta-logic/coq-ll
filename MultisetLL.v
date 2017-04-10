Require Export Multisets.
Require Import Eqset.
Require Export Syntax.
Export ListNotations.

Module M.
  Definition A : Set := lexp.
  Definition eqA := eqLExp.  
  Definition eqA_dec := eqLExp_dec.  
  Definition eq_dec := LExp_eq_dec.
End M.

Module MultisetLL := MultisetList M.
Export MultisetLL.



  
