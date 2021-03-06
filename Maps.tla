-------------------------------- MODULE Maps --------------------------------

(***************************************************************************)
(* Adding a key-value mapping (kv[1] is the key, kv[2] the value) to a map *)
(***************************************************************************)
f ++ kv == [x \in DOMAIN f \union {kv[1]} |-> IF x = kv[1] THEN kv[2] ELSE f[x]]

(***************************************************************************)
(* The image of a map                                                      *)
(***************************************************************************)
Image(f) == {f[x] : x \in DOMAIN f}



=============================================================================
\* Modification History
\* Last modified Mon May 02 21:02:08 EDT 2016 by nano
\* Created Mon May 02 21:01:30 EDT 2016 by nano
