Inductive cceval: context -> obseq -> context -> Prop :=
  NV_Assign: forall(x: smallvar) (N: nvmem) (V: vmem) (e: exp) (r: readobs) (v: value),
    eeval N V e r v ->
    isNV(x) -> (*checks x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval (N, V, Ins (asgn_sv x e)) [Obs r]
           ((updateNV N (inl x) v), V, Ins skip)
| V_Assign: forall(x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    eeval N (Vol mapV) e r v ->
    isV(x) -> (*checks x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval (N, (Vol mapV), Ins (asgn_sv x e)) [Obs r] (N, (Vol ((inl x) |-> v ; mapV)), Ins skip)
| Assign_Arr: forall (N: nvmem) (V: vmem)
               (a: array)
               (ei: exp)
               (ri: readobs)
               (vi: value)
               (e: exp)
               (r: readobs)
               (v: value)
               (element: el),
    eeval N V ei ri vi ->
    eeval N V e r v ->
    (el_arrayind_eq element a vi) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval (N, V, Ins (asgn_arr a ei e)) [Obs (ri++r)]
           ((updateNV N (inr element) v), V, Ins skip)
    (*valuability and inboundedness of vindex are checked in sameindex*)
| CheckPoint: forall(N: nvmem)
               (V: vmem)
               (c: command)
               (w: warvars),
               cceval (N, V, ((incheckpoint w);; c)) [checkpoint]
               (N, V, c)
| Skip: forall(N: nvmem)
         (V: vmem)
         (c: command),
    cceval (N, V, (skip;;c)) [Obs NoObs] (N, V, c)
| Seq: forall (N N': nvmem)
         (V V': vmem)
         (l: instruction)
         (c: command)
         (o: obs),
    cceval (N, V, Ins l) [o] (N', V', Ins skip) ->
    cceval (N, V, (l;;c)) [o] (N', V', c)
| If_T: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r true -> 
    cceval (N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (N, V, c1)
| If_F: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r false ->
    cceval (N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (N, V, c2).

Inductive trace_c: context -> context -> (list loc) -> (list loc) -> (list loc) -> obseq -> Prop :=
 CTrace_Assign_nv: forall(x: smallvar) (N N': nvmem) (V V': vmem) (e: exp) (r: readobs),
    isNV(x) -> (*checks x is in NV memory*)
    cceval N V (asgn_sv x e) [Obs r] N' V' skip ->
    trace_c (N, V, Ins (asgn_sv x e)) (N', V', Ins skip)
            [inl x]  (readobs_loc r) [inl x] [Obs r]
| CTrace_Assign_v: forall(x: smallvar) (N N': nvmem) (V V': vmem) (e: exp) (r: readobs),
    isV(x) -> (*checks x is in volatile memory*)
    cceval N V (asgn_sv x e) [Obs r] N' V' skip ->
    trace_c (N, V, Ins (asgn_sv x e)) (N', V', Ins skip)
            nil  (readobs_loc r) nil [Obs r]
| CTrace_Assign_Arr: forall (N N': nvmem) (V V': vmem)
               (a: array)
               (ei: exp)
               (ri: readobs)
               (e: exp)
               (r: readobs)
               (element: el),
    (el_arrayexp_eq element a ei N V) -> (*extra premise to check that inr element
                                        is actually a[ei] *)
    cceval N V (asgn_arr a ei e) [Obs (ri++r)] N' V' skip ->
    trace_c (N, V, Ins (asgn_arr a ei e)) (N', V', Ins skip)
            [inr element] (readobs_loc (ri ++ r)) [inr element] [Obs (ri ++ r)]
| CTrace_CheckPoint: forall(N: nvmem)
               (V: vmem)
               (c: command)
               (w: warvars),
    trace_c (N, V, (incheckpoint w);; c) (N, V, c)
            nil nil nil [checkpoint]
| CTrace_Skip: forall(N: nvmem)
         (V: vmem)
         (c: command),
    trace_c (N, V, skip;; c) (N, V, c)
            nil nil nil [Obs NoObs]
| CTrace_Seq: forall (N N' N'': nvmem)
         (V V' V'': vmem)
         (WT1 RD1 FstWt1 WT2 RD2 FstWt2: list loc)
         (O1 O2: obseq)
         (l: instruction)
         (c: command)
         (r: readobs),
    trace_c (N, V, Ins l) (N', V', Ins skip) WT1 RD1 FstWt1 O1 ->
    trace_c (N', V', c) (N'', V'', Ins skip) WT2 RD2 FstWt2 O2->
    trace_c (N, V, l;;c) (N'', V'', Ins skip) (WT1 ++ WT2) (RD1 ++ RD2) (FstWt1 ++ (remove in_loc_b RD1 FstWt2))
            (O1 ++ O2)
| CTrace_If_T: forall(N N': nvmem)
                (V V': vmem)
                (WT RD FstWt: list loc)
                (e: exp)
                (r: readobs)
                (c1 c2: command)
                (O1: obseq)
  ,
    cceval N V (TEST e THEN c1 ELSE c2) [Obs r] N V c1 ->
    trace_c (N, V, c1) (N', V', Ins skip) WT RD FstWt O1 ->
    trace_c (N, V, TEST e THEN c1 ELSE c2) (N', V', Ins skip) WT ((readobs_loc r) ++ RD) FstWt ((Obs r)::O1)
| CTrace_If_F: forall(N N': nvmem)
                (V V': vmem)
                (WT RD FstWt: list loc)
                (e: exp)
                (r: readobs)
                (c1 c2: command)
                (O2: obseq),
    cceval N V (TEST e THEN c1 ELSE c2) [Obs r] N V c2 ->
    trace_c (N, V, c2) (N', V', Ins skip) WT RD FstWt O2->
    trace_c (N, V, TEST e THEN c1 ELSE c2) (N', V', Ins skip) WT ((readobs_loc r) ++ RD) FstWt ((Obs r)::O2).
