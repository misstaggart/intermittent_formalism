Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From Semantics Require Export semantics lemmas_0.

(*relation determining what variables are read from when evaluating exp e
 *)
Inductive rd: exp -> warvars -> Prop :=
    RD: forall {e: exp} {N: nvmem} {V: vmem} {rs: readobs} {v: value},
      eeval N V e rs v -> rd e (readobs_wvs rs).


(*the following relations are described in more detail in the technical appendix of 'Towards a Formal Foundation'*)
Inductive WAR_ins: warvars -> warvars -> warvars -> instruction -> warvars -> warvars -> Prop :=
WAR_Skip: forall(N W R: warvars),
    WAR_ins N W R skip W R
| WAR_Vol: forall(N W R Re: warvars) (x: smallvar) (e: exp),
    (rd e Re) -> 
             isV x -> 
             (inl x) \notin W -> 
             WAR_ins N W R (asgn_sv x e) W (Re ++ R)
| WAR_NoRd: forall(N W R Re: warvars)
             (x: smallvar) (e: exp),
             isNV x -> 
             (rd e Re) -> 
             not((inl x) \in (Re ++ R)) 
             -> WAR_ins N W R (asgn_sv x e) ((inl x)::W) (Re ++ R)
| WAR_Checkpointed: forall(N W R Re: warvars)
             (x: smallvar) (e: exp),
             (rd e Re) -> 
             isNV x -> 
             (inl x) \in (Re ++ R) ->
             not((inl x) \in W) ->
             ((inl x) \in N) ->
             WAR_ins N W R (asgn_sv x e) ((inl x)::W) (Re ++ R)
| WAR_WT: forall(N W R Re: warvars)
             (x: smallvar) (e: exp),
             (rd e Re) -> 
             (inl x) \in (Re ++ R) ->
                         ((inl x) \in W) ->
             isNV x -> 
             WAR_ins N W R (asgn_sv x e) ((inl x) ::W) (Re ++ R)
| WAR_NoRd_Arr: forall(N W R Re Rindex: warvars)
                 (a: array) (e index: exp),
    (rd e Re) -> 
    (rd index Rindex) -> 
    not(intersect (generate_locs a) (Re ++ Rindex ++ R)) ->
    WAR_ins N W R (asgn_arr a index e) ((generate_locs a) ++ W) (Re ++ Rindex ++ R)
| WAR_Checkpointed_Arr: forall(N W R Re Rindex: warvars)
                 (a: array) (e index: exp),
    (rd e Re) -> 
    (rd index Rindex) -> 
    (subseq (generate_locs a) (Re ++ Rindex ++ R)) ->
    (subseq (generate_locs a)  N) ->
    WAR_ins N W R (asgn_arr a index e) ((generate_locs a) ++ W) (Re ++ Rindex ++ R)
.

Inductive WARok: warvars -> warvars -> warvars -> command -> Prop:=
  WAR_I: forall(N W R W' R': warvars) (l: instruction),
    WAR_ins N W R l W' R' -> WARok N W R l
 | WAR_CP: forall(w N W R: warvars) (c: command),
       WARok w nil nil c ->
       WARok N W R ((incheckpoint w);;c)
 | WAR_Seq: forall(N W R W' R': warvars)
             (l: instruction) (c: command),
             WAR_ins N W R l W' R' ->
             WARok N W' R' c ->
             WARok N W R (l;;c)
 | WAR_If: forall(N W R Re: warvars)
            (e: exp)
            (c1 c2: command),
     (rd e Re) -> 
     WARok N W (Re ++ R) c1 ->
     WARok N W (Re ++ R) c2 ->
     WARok N W R (TEST e THEN c1 ELSE c2)
.

(*relations modeling the DINO algorithm*)
Inductive DINO_ins: warvars -> warvars -> warvars -> instruction
                -> warvars -> warvars -> warvars -> Prop:=
  D_WAR_Skip: forall(N W R: warvars),
    DINO_ins N W R skip N W R
| D_WAR_Vol: forall(N W R Re: warvars) (x: smallvar) (e: exp),
    (rd e Re) -> 
             isV x -> 
             (inl x) \notin W ->
             DINO_ins N W R (asgn_sv x e) N W (Re ++ R)
| D_WAR_Written: forall(N W R Re: warvars)
                  (x: smallvar) (e: exp),
             (rd e Re) -> 
             isNV x -> 
             not((inl x) \in (Re ++ R))
             -> DINO_ins N W R (asgn_sv x e) N ((inl x)::W) (Re ++ R)
| D_WAR_CP_Asgn: forall(N W R Re: warvars) (x: smallvar) (e: exp),
    (rd e Re) -> 
             isNV x -> 
             (inl x) \in (Re ++ R) ->
             not((inl x) \in W) ->
             DINO_ins N W R (asgn_sv x e)
                  ((inl x)::N) ((inl x)::W) (Re ++ R)
| D_WAR_WtDom: forall(N W R Re: warvars) 
             (x: smallvar) (e: exp),
             (rd e Re) -> 
             (inl x) \in (Re ++ R) ->
                         ((inl x) \in W) ->
                         isNV x ->
             DINO_ins N W R (asgn_sv x e) N ((inl x) ::W) (Re ++ R)
| D_WAR_Wt_Arr: forall(N W R Re Rindex: warvars)
                 (a: array) (e index: exp),
    (rd e Re) -> 
    (rd index Rindex) -> 
    not(intersect (generate_locs a) (Re ++ Rindex ++ R)) ->
    DINO_ins N W R (asgn_arr a index e) N ((generate_locs a) ++ W) (Re ++ Rindex ++ R)
| D_WAR_CP_Arr: forall(N W R Re Rindex: warvars)
                 (a: array) (e index: exp), 
    (rd e Re) -> 
    (rd index Rindex) -> 
                subseq (generate_locs a) (Re ++ Rindex ++ R) ->
                 DINO_ins N W R (asgn_arr a index e)
             ((generate_locs a) ++ N) ((generate_locs a)++ W) (Re ++ Rindex ++ R)
.

Inductive DINO: warvars -> warvars -> warvars -> command
                -> command -> warvars -> Prop:=
  D_WAR_Instr: forall(N N' W R W' R': warvars) (l: instruction),
    DINO_ins N W R l N' W' R' ->
    DINO N W R l l N'
| D_WAR_Seq: forall(N N' N'' W R W' R': warvars)
              (l: instruction) (c c': command),
    DINO_ins N W R l N' W' R' ->
    DINO N' W' R' c c' N''  ->
    DINO N W R (l;;c) (l;;c') N''
| D_WAR_If: forall(N N1 N2 W R Re: warvars) (c1 c1' c2 c2': command) (e: exp),
             (rd e Re) -> 
     DINO N W (Re ++ R) c1 c1' N1 ->
     DINO N W (Re ++ R) c2 c2' N2 ->
     DINO N W R (TEST e THEN c1 ELSE c2) (TEST e THEN c1' ELSE c2') (N1 ++ N2)
| D_WAR_CP: forall(N N' W R: warvars) (c c': command),
    DINO nil nil nil c c' N' ->
    DINO N W R ((incheckpoint nil);;c) ((incheckpoint N');;c') N.

