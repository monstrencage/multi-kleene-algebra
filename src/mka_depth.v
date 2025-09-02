Require Import prelim depth gnl gnl_decomp mka.

Section gnl_depth.
  
  Context {A O : Set} {decA: decidable_set A} {decO: decidable_set O} .

  Fixpoint gnl_depth (s : GTerm A O) : @depth O :=
    match s with
    | t_var _ => d_var
    | s -[o]- t => d_prod o (gnl_depth s) (gnl_depth t)
    end.

  Global Instance gnl_depth_proper rT :
    Proper (rT ==> eq) gnl_depth ->
    Proper (gnl_term_theo_eq rT ==> eq) gnl_depth.
  Proof.
    intros h s t pr;induction pr;simpl;auto.
    - etransitivity;eassumption.
    - rewrite IHpr1,IHpr2;reflexivity.
    - destruct (gnl_depth e) as [ | | o1],(gnl_depth f) as [ | | o2 ],(gnl_depth g) as [ | | o3];
        simpl;auto;try destruct (o1 =?= o);try destruct (o2 =?= o);try destruct (o3 =?= o);subst;
        simpl;repeat rewrite eq_dec_eq || rewrite eq_dec_neq by (intros ->;tauto);
        try reflexivity || f_equal;try lia.
      + destruct n1;lia.
      + destruct n0, n1;simpl;lia.
      + destruct n0, n1;simpl;lia.
      + destruct n1;lia.
  Qed.

  Definition decomp_depth : @gnl_decomposition A O -> @depth O :=
    fun d =>
      match d with
      | inl _ => d_var
      | inr (o,l) => fold_right (d_prod o) d_one (map gnl_depth l)
      end.

  Lemma gnl_depth_not_one t :
    depth_lt d_one (gnl_depth t).
  Proof.
    induction t;simpl;auto.
    destruct (gnl_depth t1) as [| |o1],(gnl_depth t2) as [| |o2];simpl in *;
      try destruct (o1 =?= o);try destruct (o2 =?= o);auto.
  Qed.

  Lemma gnl_valid_decomp_not_one d : gnl_valid d = true -> depth_lt d_one (decomp_depth d).
  Proof.
    destruct d as [a|(o,l)];simpl;[tauto|intro V].
    apply Bool.andb_true_iff in V as (len&_).
    destruct l as [|?];[discriminate|clear len;simpl].
    generalize (fold_right (d_prod o) d_one (map gnl_depth l));clear l;intro d.
    pose proof (gnl_depth_not_one g) as h.
    destruct (gnl_depth g) as [| |o1],d as [| |o2];simpl in *;
      try destruct (o1 =?= o);try destruct (o2 =?= o);auto.
  Qed.
  
  Lemma decomp_depth_recompose d t :
    gnl_recompose d = Some t -> gnl_depth t = decomp_depth d.
  Proof.
    destruct d as [|(o,l)];simpl.
    - intro E;inversion E;subst;reflexivity.
    - revert t;induction l as [|s l];[discriminate|].
      destruct (l =?= []);[subst;clear IHl
                          |simpl;apply (GProd_Some _ o) in n as (tl&etl);rewrite etl];
        intros t E;symmetry in E;inversion E;subst;clear E;simpl.
      + destruct (gnl_depth s);simpl;auto.
      + rewrite (IHl tl etl);reflexivity.
  Qed.
  Lemma gnl_depth_prod_comm o t t' : gnl_depth (t -[o]- t') = gnl_depth (t' -[o]- t).
  Proof. simpl;apply d_prod_comm. Qed.

  Lemma gnl_term_to_list_depth_lt o s t t' :
    In s (gnl_term_to_list o t) -> depth_lt (gnl_depth s) (gnl_depth (t -[o]- t')).
  Proof.
    revert s;induction t;simpl.
    - intros ? [<-|F];[simpl|exfalso;auto].
      pose proof (gnl_depth_not_one t') as h.
      destruct (gnl_depth t') as [| |o'];simpl in *;auto.
      destruct (o' =?= o);auto.
    - destruct (o0 =?= o);[subst|intros ? [<-|F];[|exfalso];auto].
      + intro s;rewrite in_app_iff;intros [h|h].
        * apply IHt1 in h;simpl in h.
          rewrite <- d_prod_assoc.
          rewrite (d_prod_comm _ (gnl_depth t2)).
          rewrite d_prod_assoc.
          eapply depth_trans_lt_le;[apply h|].
          apply d_prod_incr_l.
        * apply IHt2 in h;simpl in h.
          rewrite <- d_prod_assoc.
          eapply depth_trans_lt_le;[apply h|].
          apply d_prod_incr_r.
      + simpl;apply d_prod_o_d_prod_o'_lt;auto using gnl_depth_not_one.
  Qed.
  

  Definition strict_sub_term (s t : GTerm A O) :=
    match gnl_decompose t with
    | inl _ => False
    | inr (_,l) => In s l
    end.

  Lemma sub_pomset_depth_lt : Proper (strict_sub_term ==> depth_lt) gnl_depth.
  Proof.
    intros s t;unfold strict_sub_term.
    destruct t;simpl;[tauto|].
    rewrite eq_dec_eq,in_app_iff;intros [h|h].
    + apply gnl_term_to_list_depth_lt,h.
    + rewrite d_prod_comm.
      apply gnl_term_to_list_depth_lt,h.
  Qed.

  Fixpoint gnl_exp_depth (e : GExp A O) : list depth :=
    match e with
    | ø => []
    | var _ => [d_var]
    | e1 ×{o} e2 => DProd o (gnl_exp_depth e1) (gnl_exp_depth e2)
    | e1 + e2 => (gnl_exp_depth e1)++(gnl_exp_depth e2)
    | e ^{o} => DIter o (gnl_exp_depth e)
    end.

  Global Instance Empty_gnl_depth : Proper (Ø ==> eq) gnl_depth.
  Proof. intros ? ? []. Qed.
    
  Lemma gnl_exp_depth_spec (e : GExp A O) d :
    In d (gnl_exp_depth e) <-> exists s, d = gnl_depth s /\ s |=(Ø)= e.
  Proof.
    revert d;induction e;simpl.
    - firstorder.
    - split;[intros [<-|F];[eexists;split;[|reflexivity]|tauto];reflexivity
            |intros (s&->&h);left;rewrite h;reflexivity].
    - setoid_rewrite in_app_iff.
      setoid_rewrite IHe1;setoid_rewrite IHe2.
      firstorder.
    - intros d.
      rewrite DProd_spec.
      setoid_rewrite IHe1;setoid_rewrite IHe2;clear IHe1 IHe2.
      firstorder (subst;simpl).
      + eexists;split;[|eexists;eexists;repeat split;eauto;reflexivity].
        reflexivity.
      + eexists;eexists;split;[rewrite H0|split;eexists;split;eauto].
        reflexivity.
    - intros d;rewrite DIter_spec.
      split.
      + intros (L&->&h&n).
        revert h n;induction L;simpl;[tauto|intros h1 _].
        assert (In a (gnl_exp_depth e)) as h2 by (apply h1;now left).
        apply IHe in h2 as (t&->&h2).
        destruct (L =?= []);[subst;clear IHL|].
        * exists t;simpl;repeat split;auto using d_prod_e_one.
          exists t,[t];repeat split;auto with proofs.
          intros ? [<-|F];[|exfalso];auto.
        * destruct IHL as (s&Es&s'&L'&Es'&h3&h4);auto.
          -- intros ? h;apply h1;now right.
          -- exists (t-[o]-s);repeat split.
             ++ simpl;rewrite Es;reflexivity.
             ++ exists (t-[o]-s'),(t::L');repeat split;auto.
                ** simpl;rewrite Es';reflexivity.
                ** rewrite h3;reflexivity.
                ** intros ? [<-|h];[|apply h4];auto.
      + intros (s & -> & s' & L & E & h1 & h2).
        exists (map gnl_depth L);repeat split.
        * rewrite h1;clear s h1 h2 IHe e.
          revert s' E;induction L;[discriminate|].
          destruct (L =?= []);[clear IHL|apply (GProd_Some _ o) in n as (s'&E)];
            intros ? E';simpl in E';[subst|rewrite E in E'];inversion E';subst;clear E'.
          -- simpl;auto using d_prod_e_one.
          -- simpl;apply IHL in E as ->;reflexivity.
        * intros d h;apply in_map_iff in h as (t&<-&h).
          apply IHe;exists t;auto.
        * intro F;apply map_eq_nil in F as ->;discriminate.
  Qed.
                                                         

  (* Lemma d_one_SP_depth {A} (s : @SP A) : SP_eq s one <-> SP_depth s = d_one. *)
  (* Proof. *)
  (*   split;[intro E;apply SP_depth_proper in E as ->;reflexivity|]. *)
  (*   rewrite <- is_one_eq_iff. *)
  (*   induction s;simpl;try discriminate||reflexivity. *)
  (*   - rewrite Bool.andb_true_iff. *)
  (*     case_eq (SP_depth s1);simpl. *)
  (*     + intuition. *)
  (*     + destruct (SP_depth s2);discriminate. *)
  (*     + destruct (SP_depth s2);discriminate. *)
  (*     + destruct (SP_depth s2);discriminate. *)
  (*   - rewrite Bool.andb_true_iff. *)
  (*     case_eq (SP_depth s1);simpl. *)
  (*     + intuition. *)
  (*     + destruct (SP_depth s2);discriminate. *)
  (*     + destruct (SP_depth s2);discriminate. *)
  (*     + destruct (SP_depth s2);discriminate. *)
  (* Qed. *)



End gnl_depth.
