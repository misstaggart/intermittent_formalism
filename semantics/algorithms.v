Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From Semantics Require Export semantics.
(*relation determining what variables are read from when evaluating exp e
 *)
(*N, V are irrespective as they'll
determine the values read, not the variables, just put them there for eeval to typecheck*)
Inductive rd: exp -> warvars -> Prop :=
    RD: forall {e: exp} {N: nvmem} {V: vmem} {rs: readobs} {v: value},
      eeval N V e rs v -> rd e (readobs_wvs rs).



Inductive WAR_ins: warvars -> warvars -> warvars -> instruction -> warvars -> warvars -> Prop :=
WAR_Skip: forall(N W R: warvars),
    WAR_ins N W R skip W R
| WAR_Vol: forall(N W R Re: warvars) (x: smallvar) (e: exp), (*rule for writing to volatile variables: does not change written set or check checkpoint*)
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             isV x -> (*x is volatile*)
             (inl x) \notin W -> (*ensuring parameters are well formed*)
             WAR_ins N W R (asgn_sv x e) W (R ++ Re)
| WAR_NoRd: forall(N W R Re: warvars)
             (x: smallvar) (e: exp),
             isNV x -> (*checking x is nonvolatile*)
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             not((inl x) \in (R ++ Re)) 
             -> WAR_ins N W R (asgn_sv x e) ((inl x)::W) (R ++ Re)
| WAR_Checkpointed: forall(N W R Re: warvars)
             (x: smallvar) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             isNV x -> (*checking x is nonvolatile*)
             (inl x) \in (R ++ Re) ->
             not((inl x) \in W) ->
             ((inl x) \in N) ->
             WAR_ins N W R (asgn_sv x e) ((inl x)::W) (R ++ Re)
| WAR_WT: forall(N W R Re: warvars)
             (x: smallvar) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             (inl x) \in (R ++ Re) ->
             ((inl x) \in W) ->
             WAR_ins N W R (asgn_sv x e) W (R ++ Re)
(*no restrictions on the parameter W,
 if make W really big, never enter the checkpointed case
 and check N for anything
 concern w regard to lemma 13 which allows for
 an arbitrary W to be chosen*)
| WAR_NoRd_Arr: forall(N W R Re Rindex: warvars)
                 (a: array) (e index: exp),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    not(intersect (generate_locs a) (R ++ Re ++ Rindex)) -> (*would be easier
                                                        if you had intersection here
                                                       ~subseq is weak *)
    WAR_ins N W R (asgn_arr a index e) ((generate_locs a) ++ W) (R ++ Re ++ Rindex) (*written set is modified but
                                                                        don't need to check if a is NV cuz all arrays are*)
| WAR_Checkpointed_Arr: forall(N W R Re Rindex: warvars)
                 (a: array) (e index: exp),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    (subseq (generate_locs a) (R ++ Re ++ Rindex)) ->
    (subseq (generate_locs a)  N) ->
    WAR_ins N W R (asgn_arr a index e) ((generate_locs a) ++ W) (R ++ Re ++ Rindex)
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
     (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
     WARok N W (R ++ Re) c1 ->
     WARok N W (R ++ Re) c2 ->
     WARok N W R (TEST e THEN c1 ELSE c2)
.

Inductive DINO_ins: warvars -> warvars -> warvars -> instruction
                -> warvars -> warvars -> warvars -> Prop:=
  D_WAR_Skip: forall(N W R: warvars),
    DINO_ins N W R skip N W R
| D_WAR_Vol: forall(N W R Re: warvars) (x: smallvar) (e: exp), (*rule for writing to volatile variables: does not change written set or check checkpoint*)
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             isV x -> (*x is volatile*)
             (inl x) \notin W ->
             DINO_ins N W R (asgn_sv x e) N W (R ++ Re)
| D_WAR_Written: forall(N W R Re: warvars)
                  (x: smallvar) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             isNV x -> (*checking x is nonvolatile*)
             not((inl x) \in (R ++ Re))
             -> DINO_ins N W R (asgn_sv x e) N ((inl x)::W) (R ++ Re)
| D_WAR_CP_Asgn: forall(N W R Re: warvars) (x: smallvar) (e: exp), (*Changed name to avoid duplication w D_WAR_CP below*)
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             isNV x -> (*checking x is nonvolatile*)
             (inl x) \in (R ++ Re) ->
             not((inl x) \in W) ->
             DINO_ins N W R (asgn_sv x e)
                  ((inl x)::N) ((inl x)::W) (R ++ Re)
| D_WAR_WtDom: forall(N W R Re: warvars) 
             (x: smallvar) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             (inl x) \in (R ++ Re) ->
             ((inl x) \in W) ->
             DINO_ins N W R (asgn_sv x e) N W (R ++ Re)
| D_WAR_Wt_Arr: forall(N W R Re Rindex: warvars)
                 (a: array) (e index: exp),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    not(intersect (generate_locs a) (R ++ Re ++ Rindex)) ->
    DINO_ins N W R (asgn_arr a index e) N ((generate_locs a) ++ W) (R ++ Re ++ Rindex)
| D_WAR_CP_Arr: forall(N W R Re Rindex: warvars)
                 (a: array) (e index: exp), 
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
                subseq (generate_locs a) (R ++ Re ++ Rindex) ->
                 DINO_ins N W R (asgn_arr a index e)
             ((generate_locs a) ++ N) ((generate_locs a)++ W) (R ++ Re ++ Rindex)
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
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
     DINO N W (R ++ Re) c1 c1' N1 ->
     DINO N W (R ++ Re) c2 c2' N2 ->
     DINO N W R (TEST e THEN c1 ELSE c2) (TEST e THEN c1' ELSE c2') (N1 ++ N2)
| D_WAR_CP: forall(N N' W R: warvars) (c c': command),
    DINO nil nil nil c c' N' ->
    DINO N W R ((incheckpoint nil);;c) ((incheckpoint N');;c') N.

