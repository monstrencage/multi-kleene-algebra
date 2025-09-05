(** * gnl_alg.gnl_recompose : recomposition of expressions and axiomatic correspondance *)
Require Import prelim.
Require Import gnl theories gnl_decomp.

Section gnl_recomp.
  Context {A : Set} {decA : decidable_set A}.
  Context {O : Set} {decO : decidable_set O}.

  (** * Definitions *)

  (** The axiomatic order on projections is defined as follows: *)

  Definition dec_inf r : relation (GExp A O) :=
    fun e f =>
      gnl_slat_proj e ≤slat gnl_slat_proj f
      /\ forall o, fKA r |- gnl_reg_proj o e ≤ gnl_reg_proj o f.

  (** The [operators] of an expressions are those [o] that feature in subexpressions *)
  (** either as [_×{o}_] or as [_^{o}]. *)

  Fixpoint operators (e : GExp A O) : list O :=
    match e with
    | ø | var _ => []
    | e + f => operators e ++ operators f
    | e ×{o} f => o::operators e ++ operators f
    | e ^{o} => o::operators e
    end.

  (** The following pair of functions allows for the projections to be converted back *)
  (** to [GExp A O]. *)
  
  Fixpoint slat_to_gnl (s : slat A) : GExp A O :=
    match s with
    | ø => ø
    | var a => var a
    | e + f => slat_to_gnl e + slat_to_gnl f
    | _ => ø
    end.
  
  Fixpoint flatten {X Op : Set} (o : Op) (e : Reg (GExp X Op)) : GExp X Op :=
    match e with
    | 1_r | ø => ø
    | var (Some e) => e
    | e @@ f =>
        (if ewp_r e then flatten o f else ø)
          + ((if ewp_r f then flatten o e else ø) + (flatten o e ×{o} flatten o f))
    | e + f => flatten o e + flatten o f
    | e^+ => iter o (flatten o e)
    end.

  (** We may thus define the recomposition function that computes a new expression from *)
  (** an expression's projections. *)
  Definition gnl_recompose e :=
    slat_to_gnl (gnl_slat_proj e) +
      fold_right sum ø (map (fun o => flatten o (gnl_reg_proj o e)) (operators e)).

  (** * First lemmas *)

  (** [gnl_reg_trad] is non-destructive, since we can get back from it an expression *)
  (** that is equivalent to the original argument. *)
  
  Lemma flatten_gnl_reg_trad {X Op : Set} {decOp : decidable_set Op} :
    forall (o : Op) (e : GExp X Op), Ø |- e == flatten o (gnl_reg_trad o e).
  Proof.
    induction e as [ | | |i|i];simpl;auto;try destruct (i =?= o);subst;simpl;
      repeat rewrite ewp_gnl_reg_trad;
      try (rewrite <-IHe1,<-IHe2)||(rewrite <-IHe);simpl;
      try (eexists;split;[reflexivity|]);try reflexivity||auto with proofs.
    - repeat rewrite gnl_theo_eq_sum_zero_e;reflexivity. 
    - split;eauto with proofs.
  Qed.
  (** Any operator not in [operators e] will have an empty projection. *)

  Lemma not_operator_zero o e :
    ~ In o (operators e) -> Ø |- gnl_reg_proj o e == ø.
  Proof.
    induction e;simpl;try (now intros;auto with proofs).
    - rewrite in_app_iff;intros h;rewrite IHe1,IHe2;try tauto||(split;auto with proofs).
    - rewrite in_app_iff;intros h.
      destruct (o0 =?= o);[tauto|split;auto with proofs].
    - destruct (o0 =?= o);[tauto|].
      intro;apply IHe;tauto.
  Qed.
  
  (** The ordering we defined on projections is sound w.r.t. the satisfaction relation *)
  (** bewteen decompostions and projected expressions. *)

  Global Instance dec_inf_sound s :
    Proper (dec_inf Ø ==> Basics.impl) (gnl_decomp_sat Ø s).
  Proof.
    intros e f hyp;unfold Basics.impl.
    destruct s as [|(o,l)];simpl;auto.
    - apply slat_exact,hyp.
    - destruct hyp as (_&hyp).
      pose proof (hyp o) as E.
      clear hyp.
      generalize dependent (gnl_reg_proj o f);
        generalize dependent (gnl_reg_proj o e);clear e f;intros e f E.
      revert l;induction E;intro l;simpl;auto;try (now firstorder).
      + destruct i;intros (m&hl&s1&s2&hm&h2&h3).
        pose proof hm as E;apply Word_to_list_eq in E;rewrite E in hl;simpl in hl.
        apply list_lift_app in hl as (l1&l2&->&hl1&hl2).
        destruct (IHE1 l1) as (m1&hm1); [now exists s1|].
        destruct (IHE2 l2) as (m2&hm2); [now exists s2|].
        exists (m1**m2);simpl;split;auto.
        * apply app_list_lift;tauto.
        * exists m1,m2;repeat split;tauto||auto with proofs.
      + destruct i;intros (m&hl&s'&L&hs'&hm&hL).
        revert l m s' hs' hl hm hL;induction L;[discriminate|].
        destruct (L =?= []);[subst;clear IHL
                            |apply (GProd_Some _ •) in n as (t&ht);simpl;rewrite ht];
          intros l m ? Eq;inversion Eq;subst;clear Eq;intros.
        * destruct (IHE l) as (m1&hm1); [exists m;split;auto;rewrite hm;apply hL;now left|].
          exists m1;split;[tauto|].
          exists m1,[m1];repeat split;auto with proofs.
          intros ? [<-|F];[|exfalso];tauto.
        * pose proof hm as Eq;apply Word_to_list_eq in Eq;rewrite Eq in hl;simpl in hl.
          apply list_lift_app in hl as (l1&l2&->&hl1&hl2).
          destruct (IHE l1) as (m1&lift1&sat1); [exists a;split;auto;rewrite hm;apply hL;now left|].
          destruct (IHL l2 t t) as (m2&lift2&sat2); auto with proofs.
          exists (m1**m2);simpl;split;auto.
          -- apply app_list_lift;tauto.
          -- destruct sat2 as (s'&L'&Es'&hm2&hL').
             exists (m1**s'),(m1::L');simpl;rewrite Es';repeat split;tauto||auto with proofs.
             intros ? [<-|h];[|apply hL'];auto.
      + destruct i;intros (m&hl&s1&s'&hm&hs1&s2&s3&hs'&hs2&hs3).
        exists m;split;auto.
        exists (s1**s2),s3;repeat split;auto.
        -- rewrite hm,hs';auto with proofs.
        -- exists s1,s2;auto with proofs.
      + destruct i;intros (m&hl&s'&s3&hm&(s1&s2&hs'&hs1&hs2)&hs3).
        exists m;split;auto.
        exists s1,(s2**s3);repeat split;auto.
        -- rewrite hm,hs';auto with proofs.
        -- exists s2,s3;auto with proofs.
      + destruct i;intros (m&hlift&[sat|sat]).
        * exists m;split;auto.
          exists m,[m];repeat split;auto with proofs.
          intros ? [<-|F];[|exfalso];auto.
        * destruct sat as (s1&s2&hm&hs1&s'&L&Es'&hs2&hL).
          exists m;split;auto.
          exists (s1**s'),(s1::L);simpl;rewrite Es',hm,hs2;repeat split;auto with proofs.
          intros ? [<-|h];[|apply hL];auto.
      + destruct i;intros (m&hlift&[sat|sat]).
        * exists m;split;auto.
          exists m,[m];repeat split;auto with proofs.
          intros ? [<-|F];[|exfalso];auto.
        * destruct sat as (s1&s2&hm&(s'&L&Es'&hs1&hL)&hs2).
          exists m;split;auto.
          assert (EE : GProd • [s2] = Some s2) by reflexivity.
          destruct (GProd_app ka • _ _ _ _ Es' EE) as (t&Et&ht).
          exists t,(L++[s2]);repeat split;auto.
          -- rewrite hm,hs1,ht;reflexivity.
          -- intros ?;rewrite in_app_iff;intros [h|[<-|F]];[apply hL| |exfalso];auto.
      + destruct i;intros (m&hl&s1&s2&hm&(s&L&Es&hs1&hL)&hs2).
        rewrite hs1 in hm;clear s1 hs1.
        revert l m s2 s Es hl hm hs2 hL;induction L;[discriminate|].
        destruct (L =?= []);[subst;clear IHL
                            |apply (GProd_Some _ •) in n as (t&ht);simpl;rewrite ht];
          intros l m s2 ? Eq;inversion Eq;subst;clear Eq;intros.
        * apply IHE;exists m;split;auto.
          exists s,s2;repeat split;eauto with proofs.
          apply hL;now left.
        * pose proof hm as E';apply Word_to_list_eq in E';rewrite E' in hl;simpl in hl.
          apply list_lift_app in hl as (l'&l3&->&hl1&hl3).
          apply list_lift_app in hl1 as (l1&l2&->&hl1&hl2).
          destruct (IHL (l2++l3) (t**s2) s2 t) as (T&lift&sat);
            try apply app_list_lift;auto with proofs.
          apply IHE;exists (a**T);repeat split;simpl;auto.
          -- rewrite <- app_assoc;apply app_list_lift;auto.
          -- exists a,T;repeat split;auto with proofs.
      + destruct i;intros (m&hl&s1&s2&hm&hs1&(s&L&Es&hs2&hL)).
        rewrite hs2 in hm;clear s2 hs2.
        revert l m s1 s Es hl hm hs1 hL;induction L;[discriminate|].
        destruct (L =?= []);[subst;clear IHL
                            |apply (GProd_Some _ •) in n as (t&ht);simpl;rewrite ht];
          intros l m s2 ? Eq;inversion Eq;subst;clear Eq;intros.
        * apply IHE;exists m;split;auto.
          exists s2,s;repeat split;eauto with proofs.
          apply hL;now left.
        * pose proof hm as E';apply Word_to_list_eq in E';rewrite E' in hl;simpl in hl.
          apply list_lift_app in hl as (l1&l'&->&hl1&hl3).
          apply list_lift_app in hl3 as (l2&l3&->&hl2&hl3).
          destruct (IHE (l1++l2)) as (m1&liftm1&satm1);
            [exists (s2**a);split;[simpl;apply app_list_lift
                                  |exists s2,a;repeat split;[| |apply hL;left]];auto with proofs|].
          destruct (IHL ((l1++l2)++l3) (m1**t) m1 t) as (T&lift&sat);
            try apply app_list_lift;auto with proofs.
          exists T;rewrite app_assoc;repeat split;auto.
      + destruct i;intros (m&hl&(s&L&Es&hs2&hL)).
        revert l m s Es hl hs2 hL;induction L;[discriminate|].
        destruct (L =?= []);[subst;clear IHL
                            |apply (GProd_Some _ •) in n as (t&ht);simpl;rewrite ht];
          intros l m ? Eq;inversion Eq;subst;clear Eq;intros.
        * apply IHE;exists m;split;auto.
          left;rewrite hs2;apply hL;now left.
        * pose proof hs2 as E';apply Word_to_list_eq in E';rewrite E' in hl;simpl in hl.
          apply list_lift_app in hl as (l1&l2&->&hl1&hl3).
          destruct (IHL l2 t t) as (T&hlift&hsat);auto with proofs.
          apply IHE;exists (a**T);repeat split.
          -- simpl;apply app_list_lift;auto.
          -- right;exists a,T;repeat split;auto with proofs.
      + destruct i;intros (m&hl&(s&L&Es&hs2&hL)).
        revert l m s Es hl hs2 hL.
        apply (rev_ind (fun L =>
                          forall (l : list (GTerm A O)) (m : Word (GExp A O))
                                 (s : GTerm (option (GExp A O)) One),
                            GProd • L = Some s ->
                            list_lift (gnl_theo_sat Ø) l (Word_to_list m) ->
                            ka |- m =T= s ->
                                  (forall s'' : GTerm (option (GExp A O)) One, In s'' L ->
                                                                               s'' |=( ka )= e) ->
                                  exists m0 : Word (GExp A O),
                                    list_lift (gnl_theo_sat Ø) l (Word_to_list m0)
                                    /\ m0 |=( ka )= f));[discriminate|clear L;intros a L IHL].
        destruct (L =?= []);[subst;clear IHL;intros l m ? Eq;inversion Eq;subst;clear Eq
                            |apply (GProd_Some _ •) in n as (t&ht);simpl;intros l m s Es];
          intros hl hs2 hL.
        * apply IHE;exists m;split;auto.
          left;rewrite hs2;apply hL;now left.
        * pose proof hs2 as E';apply Word_to_list_eq in E';rewrite E' in hl;simpl in hl.
          clear m hs2 E'.
          assert (EE : GProd • [a] = Some a) by reflexivity.
          destruct (GProd_app ka • _ _ _ _ ht EE) as (?&Et&ht').
          rewrite Et in Es;inversion Es;subst;clear Es.
          pose proof ht' as E';apply Word_to_list_eq in E';rewrite E' in hl;simpl in hl.
          apply list_lift_app in hl as (l1&l2&->&hl1&hl3).
          destruct (IHL l1 t t) as (T&hlift&hsat);auto with proofs;
            [intros;apply hL,in_app_iff;now left|].
          apply IHE;exists (T**a);repeat split.
          -- simpl;apply app_list_lift;auto.
          -- right;exists T,a;repeat split;auto with proofs.
             apply hL,in_app_iff;now right;left.
      + destruct H;simpl in *.
        * intros (m&lift&sat);exists m;split;auto.
          revert sat;eapply gnl_sat_reg_theo_proper;assumption.
        * intros (m&lift&sat).
          pose proof sat as E';apply Word_to_list_eq in E';rewrite E' in lift;simpl in lift.
          destruct l as [|? [|]];try (exfalso;apply lift);simpl in E'.
          destruct lift as (sat'&_).
          exists (t_var (Some f));repeat split;auto with proofs.
          revert sat';eapply gnl_theo_sat_proper,H;auto with proofs.
          apply Empty_sat_proper.
        * intros (m&lift&sat).
          pose proof sat as E';apply Word_to_list_eq in E';rewrite E' in lift;simpl in lift.
          destruct l as [|? [|]];try (exfalso;apply lift);simpl in E'.
        * intros (m&lift&sat).
          pose proof sat as E';apply Word_to_list_eq in E';rewrite E' in lift;simpl in lift.
          destruct l as [|? [|]];try (exfalso;apply lift);simpl in E'.
          destruct lift as ([sat'|sat']&_).
          -- exists (t_var (Some e));repeat split;auto with proofs.
          -- exists (t_var (Some f));repeat split;auto with proofs.
  Qed.          

  (** * First theorem: the recomposion of an expression is equivalent to the original *)

  (** We first prove the _easy_ direction, which hinges on the fact that each projection *)
  (** is below the orgininal expression. *)
  
  Lemma gnl_slat_proj_inf e : Ø |- slat_to_gnl (gnl_slat_proj e) ≤ e.
  Proof.
    induction e;simpl;auto with proofs.
    rewrite IHe,<- gnl_theo_inf_iter_unfold_left.
    auto with proofs.
  Qed. 

  Lemma gnl_reg_proj_inf o (e : GExp A O): Ø |- flatten o (gnl_reg_proj o e) ≤ e.
  Proof.
    induction e;simpl;auto with proofs.
    - destruct (o0 =?= o);simpl;auto with proofs.
      subst;repeat rewrite ewp_gnl_reg_trad.
      repeat rewrite <- flatten_gnl_reg_trad.
      repeat apply gnl_theo_inf_join;auto with proofs.
    - destruct (o0 =?= o);simpl;auto with proofs.
      + subst;simpl;repeat (rewrite ewp_gnl_reg_trad;simpl).
        unfold ewp_r;simpl.
        rewrite Bool.andb_true_r.
        replace (ka.r_ewp (Reg_to_reg (gnl_reg_trad o e))) with (ewp_r (gnl_reg_trad o e))
          by reflexivity.
        rewrite (ewp_gnl_reg_trad o e).
        repeat rewrite <- flatten_gnl_reg_trad.
        rewrite IHe.
        repeat apply gnl_theo_inf_join;auto with proofs.
        * rewrite <- gnl_theo_inf_iter_unfold_left;auto with proofs.
        * rewrite <- gnl_theo_inf_iter_unfold_left at 2;auto with proofs.
      + rewrite IHe;rewrite <- gnl_theo_inf_iter_unfold_left;auto with proofs.
  Qed.

  Lemma gnl_recompose_inf_aux e L : 
    Ø |- slat_to_gnl (gnl_slat_proj e) + 
         fold_right sum ø (map (fun o : O => flatten o (gnl_reg_proj o e)) L) ≤ e.
  Proof.
    apply gnl_theo_inf_join.
    - apply gnl_slat_proj_inf.
    - induction L as [|o];[auto with proofs|].
      simpl;apply gnl_theo_inf_join;auto.
      apply gnl_reg_proj_inf.
  Qed.

  Corollary gnl_recompose_inf e : Ø |- gnl_recompose e ≤ e.
  Proof. apply gnl_recompose_inf_aux. Qed.

  (** For the converse inclusion, we need to generalise the list [operators e] to any *)
  (** _larger_ list. *)

  Lemma gnl_recompose_sup_aux e L : 
    incl (operators e) L ->
    Ø |- e ≤ slat_to_gnl (gnl_slat_proj e) +
              fold_right sum ø (map (fun o : O => flatten o (gnl_reg_proj o e)) L).
  Proof.
    revert L;induction e;simpl;intros;auto with proofs.
    - rewrite (IHe1 L),(IHe2 L) at 1 by (intros ? h;apply H,in_app_iff;auto).
      clear H IHe1 IHe2.
      repeat apply gnl_theo_inf_join.
      + apply gnl_theo_inf_sum_left;auto with proofs.
      + apply gnl_theo_inf_sum_right.
        induction L;[reflexivity|];simpl.
        apply sum_mono;auto with proofs.
      + apply gnl_theo_inf_sum_left;auto with proofs.
      + apply gnl_theo_inf_sum_right.
        induction L;[reflexivity|];simpl.
        apply sum_mono;auto with proofs.
    - apply gnl_theo_inf_sum_right.
      cut (In o L);[|apply H;now left].
      clear H IHe1 IHe2.
      induction L;[simpl;tauto|].
      intros [<-|ih].
      + apply gnl_theo_inf_sum_left.
        rewrite eq_dec_eq;simpl.
        repeat rewrite ewp_gnl_reg_trad.
        repeat rewrite <- flatten_gnl_reg_trad.
        apply gnl_theo_inf_sum_right;auto with proofs.
      + rewrite IHL by assumption;simpl;auto with proofs.
    - assert (ih : incl (operators e) L) by (intros ? ?;apply H;now right).
      apply IHe in ih.
      remember (slat_to_gnl (gnl_slat_proj e) +
                  fold_right sum ø
                    (map
                        (fun o0 : O =>
                          flatten o0
                            (if o =?= o0
                              then gnl_reg_proj o0 e + gnl_reg_trad o0 e @@ (gnl_reg_trad o0 e) ^+
                              else gnl_reg_proj o0 e)) L))
                  as E.
      cut (Ø |- e ≤ E).
      + intros h.
        rewrite gnl_theo_eq_iter_unfold_left.
        apply gnl_theo_inf_join;auto.
        rewrite h at 1.
        apply gnl_theo_inf_iter_right_ind.
        rewrite h.
        rewrite HeqE at 3;apply gnl_theo_inf_sum_right.
        transitivity (flatten o (gnl_reg_proj o e + gnl_reg_trad o e @@ (gnl_reg_trad o e) ^+)).
        * simpl.
          repeat rewrite ewp_gnl_reg_trad.
          unfold ewp_r;simpl.
          rewrite Bool.andb_true_r.
          replace (ka.r_ewp (Reg_to_reg (gnl_reg_trad o e))) with (ewp_r (gnl_reg_trad o e))
            by reflexivity.
          rewrite ewp_gnl_reg_trad.
          repeat rewrite <- flatten_gnl_reg_trad.
          repeat apply gnl_theo_inf_sum_right.
          pose proof (gnl_recompose_inf_aux (e ^{o}) L) as h2;simpl in h2;rewrite <- HeqE in h2.
          rewrite h2;clear.
          rewrite gnl_theo_eq_iter_unfold_left at 1.
          rewrite gnl_theo_eq_sum_prod,<-gnl_theo_eq_prod_assoc.
          apply gnl_theo_inf_join;auto with proofs.
          apply prod_mono;auto with proofs.
          apply gnl_theo_inf_iter_left_ind.
          rewrite gnl_theo_eq_iter_unfold_left at 2;auto with proofs.
        * cut (In o L);[|apply H;now left].
          clear.
          induction L as [|o'];[simpl;tauto|].
          intros [<-|ih].
          -- apply gnl_theo_inf_sum_left.
             rewrite eq_dec_eq;simpl.
             repeat rewrite ewp_gnl_reg_trad.
             unfold ewp_r;simpl.
             rewrite Bool.andb_true_r.
             replace (ka.r_ewp (Reg_to_reg (gnl_reg_trad o' e))) with (ewp_r (gnl_reg_trad o' e))
               by reflexivity.
             rewrite ewp_gnl_reg_trad.
             reflexivity.
          -- rewrite IHL by assumption;simpl;auto with proofs.
      + rewrite ih,HeqE.
        apply sum_mono;auto with proofs.
        clear;induction L as [|o'];simpl;[|destruct (o =?= o');subst;rewrite IHL;simpl];
          auto with proofs.
  Qed.


  Corollary gnl_recompose_sup e : Ø |- e ≤ gnl_recompose e.
  Proof. apply gnl_recompose_sup_aux;intro;tauto. Qed.

  (** We now prove the full theorem. *)

  Theorem gnl_recompose_id e : Ø |- gnl_recompose e == e.
  Proof. split;[apply gnl_recompose_inf|apply gnl_recompose_sup]. Qed.

  (** * A result about the empty word property *)
  Lemma fKA_ewp_r {X Op} (r : relation (GExp X Op))  e1 e2 :
    fKA r |- e1 ≤ e2 -> implb (ewp_r e1) (ewp_r e2) = true.
  Proof.
    unfold ewp_r;rewrite Bool.implb_true_iff;intro E;induction E;try destruct i;try destruct H;
      simpl in *;
      auto with bool;
      repeat (rewrite Bool.andb_true_r in * )
      || (rewrite Bool.andb_true_iff in * )
      || (rewrite Bool.orb_true_iff in * );try tauto.
    destruct H;simpl; repeat (rewrite Bool.andb_true_r in * )
                      || (rewrite Bool.andb_true_iff in * )
                      || (rewrite Bool.orb_true_iff in * );try tauto.
  Qed.

  (** * Testing whether an expression is empty *)
  (** We can use the following boolean predicate to check whether an expression is equivalent to *)
  (** [ø], i.e. it has an empty interpretation. *)

  Fixpoint is_zero {X Op:Set} (e : GExp X Op) :=
    match e with
    | ø => true
    | var _ => false
    | e + f => (is_zero e && is_zero f)%bool
    | e ×{_} f => (is_zero e || is_zero f)%bool
    | e ^{_} => is_zero e
    end.

  (** To prove the correction of this predicate, we first observe that it send the relation  *)
  (** [Ø|- _ ≤ _] to the boolean implication. *)

  Lemma is_zero_implb {X Op:Set} (e f : GExp X Op) :
    Ø |- e ≤ f -> implb (is_zero f) (is_zero e) = true.
  Proof.
    rewrite Bool.implb_true_iff;intro E;induction E;try destruct H;
      simpl in *;
      auto with bool;
      repeat (rewrite Bool.andb_true_r in * )
      || (rewrite Bool.andb_true_iff in * )
      || (rewrite Bool.orb_true_iff in * );try tauto.
  Qed.

  (** We then prove that when the predicate holds, the argument is provably empty. *)

  Lemma is_zero_inf {X Op:Set} (e : GExp X Op) : is_zero e = true -> Ø |- e ≤ ø.
  Proof.
    induction e;simpl;
      auto with bool;
      repeat (rewrite Bool.andb_true_r in * )
      || (rewrite Bool.andb_true_iff in * )
      || (rewrite Bool.orb_true_iff in * );try discriminate||auto with proofs.
    - intros (h1&h2);rewrite IHe1,IHe2;auto with proofs.
    - intros [h|h];[rewrite IHe1|rewrite IHe2];auto with proofs.
  Qed.

  (** Putting both previous lemmas together, we get that [is_zero] does characterise provably *)
  (** empty expressions. *)

  Lemma is_zero_spec {X Op: Set} (e : GExp X Op) : is_zero e = true <-> Ø |- e ≤ ø.
  Proof.
    split;[apply is_zero_inf|].
    now intro h;apply is_zero_implb in h;simpl in h.
  Qed.

  (** Being empty implies not having the empty word property. *)

  Lemma is_zero_ewp {X: Set} (e : Reg X) : is_zero e = true -> ewp_r e = false.
  Proof.
    unfold ewp_r;induction e as [| | |[] |[]];simpl;discriminate||auto.
    - rewrite Bool.andb_true_iff.
      intros (h1&h2);rewrite IHe1,IHe2 by assumption;reflexivity.
    - rewrite Bool.orb_true_iff.
      intros [h|h];[rewrite IHe1 by assumption|rewrite IHe2 by assumption].
      + apply Bool.andb_false_l.
      + apply Bool.andb_false_r.
    - intros h;rewrite IHe;auto.
  Qed.

  (** [is_zero] also characterizes expressions whose [clean_exp] is undefined. *)

  Lemma is_zero_clean_exp_None {X Op: Set} (e : GExp X Op) : 
    is_zero e = true <-> clean_exp e = None.
  Proof.
    induction e;simpl.
    - split;reflexivity.
    - split;discriminate.
    - rewrite Bool.andb_true_iff,IHe1,IHe2.
      destruct (clean_exp e1),(clean_exp e2);
        try (repeat split;reflexivity) ||(split;intros (h1&h2)||intro h;discriminate).
    - rewrite Bool.orb_true_iff,IHe1,IHe2.
      destruct (clean_exp e1),(clean_exp e2);
        (split;[intros []|intro]);discriminate||auto.
    - rewrite IHe;destruct (clean_exp e);[split;discriminate|split;reflexivity].
  Qed.

  (** * Second theorem : [gnl_decompose] is a morphism *)
  
  (** We first show that [flatten] is a morphism. *)

  Global Instance flatten_proper o (r : relation (GExp A O)) :
    Proper (gnl_theo_inf (fKA r) ==> gnl_theo_inf r) (flatten o).
  Proof.
    intros e f hyp.
    pose proof ((gnl_theo_eq_prod_sum) r) as r1;
    pose proof ((gnl_theo_eq_sum_prod) r) as r2;
    pose proof ((gnl_theo_eq_prod_e_zero) r) as r3;
    pose proof ((gnl_theo_eq_sum_assoc) r) as r4;
    pose proof ((gnl_theo_eq_prod_assoc) r) as r5.
    induction hyp;simpl;try destruct i;auto with proofs.
    - eauto with proofs.
    - pose proof (fKA_ewp_r _ _ _ hyp1) as he.
      pose proof (fKA_ewp_r _ _ _ hyp2) as hf.
      destruct (ewp_r e1),(ewp_r e2),(ewp_r f1),(ewp_r f2);simpl in he,hf;try discriminate;
        repeat rewrite IHhyp1||rewrite IHhyp2;auto with proofs.
    - unfold ewp_r;simpl.
      generalize (flatten o g);generalize (flatten o f); generalize (flatten o e);
      intros e' f' g'.
      destruct (ka.r_ewp (Reg_to_reg e)),(ka.r_ewp (Reg_to_reg f)),(ka.r_ewp (Reg_to_reg g));simpl;
      repeat rewrite (r1 o) || rewrite (r2 o) || rewrite (r3 o) || rewrite r4 || rewrite (r5 o);
      repeat apply gnl_theo_inf_join;
      repeat apply gnl_theo_inf_join_r||apply gnl_theo_inf_sum_left;
      auto with proofs.
    - unfold ewp_r;simpl.
      generalize (flatten o g);generalize (flatten o f); generalize (flatten o e);
      intros e' f' g'.
      destruct (ka.r_ewp (Reg_to_reg e)),(ka.r_ewp (Reg_to_reg f)),(ka.r_ewp (Reg_to_reg g));simpl;
      repeat rewrite (r1 o) || rewrite (r2 o) || rewrite (r3 o) || rewrite r4 || rewrite (r5 o);
      repeat apply gnl_theo_inf_join;
      repeat apply gnl_theo_inf_join_r||apply gnl_theo_inf_sum_left;
      auto with proofs.
    - unfold ewp_r;simpl.
      generalize (flatten o g);generalize (flatten o f); generalize (flatten o e);
      intros e' f' g'.
      destruct (ka.r_ewp (Reg_to_reg e)),(ka.r_ewp (Reg_to_reg f)),(ka.r_ewp (Reg_to_reg g));simpl;
      repeat rewrite (r1 o) || rewrite (r2 o) || rewrite (r3 o) || rewrite r4 || rewrite (r5 o);
      repeat apply gnl_theo_inf_join;
      repeat apply gnl_theo_inf_join_r||apply gnl_theo_inf_sum_left;
      auto with proofs.
    - unfold ewp_r;simpl.
      generalize (flatten o g);generalize (flatten o f); generalize (flatten o e);
      intros e' f' g'.
      destruct (ka.r_ewp (Reg_to_reg e)),(ka.r_ewp (Reg_to_reg f)),(ka.r_ewp (Reg_to_reg g));simpl;
      repeat rewrite (r1 o) || rewrite (r2 o) || rewrite (r3 o) || rewrite r4 || rewrite (r5 o);
      repeat apply gnl_theo_inf_join;
      repeat apply gnl_theo_inf_join_r||apply gnl_theo_inf_sum_left;
      auto with proofs.
    - repeat apply gnl_theo_inf_join;auto with proofs.
      destruct (ewp_r e);auto with proofs.
    - repeat apply gnl_theo_inf_join;auto with proofs.
      destruct (ewp_r e);auto with proofs.
    - unfold ewp_r;simpl;rewrite Bool.andb_true_r.
      destruct (ka.r_ewp (Reg_to_reg e));simpl;repeat apply gnl_theo_inf_join;auto with proofs;
        rewrite gnl_theo_eq_iter_unfold_left at 2
        || rewrite gnl_theo_eq_iter_unfold_left;auto with proofs.
    - unfold ewp_r;simpl;rewrite Bool.andb_true_r.
      destruct (ka.r_ewp (Reg_to_reg e));simpl;repeat apply gnl_theo_inf_join;auto with proofs;
        rewrite gnl_theo_eq_iter_unfold_right at 2
        || rewrite gnl_theo_eq_iter_unfold_right;auto with proofs.
    - simpl in *.
      unfold ewp_r in *;simpl;rewrite Bool.andb_true_r.
      destruct (ka.r_ewp (Reg_to_reg e)),(ka.r_ewp (Reg_to_reg f));simpl;
        repeat apply gnl_theo_inf_join;auto with proofs;
        apply gnl_theo_inf_iter_left_ind||apply gnl_theo_inf_iter_left_ind_bis;
        rewrite <- IHhyp at 2;auto with proofs;
        apply gnl_theo_inf_sum_right;auto with proofs.
    - simpl in *.
      unfold ewp_r in *;simpl;rewrite Bool.andb_true_r.
      destruct (ka.r_ewp (Reg_to_reg e)),(ka.r_ewp (Reg_to_reg f));simpl;
        repeat apply gnl_theo_inf_join;auto with proofs;
        apply gnl_theo_inf_iter_right_ind||apply gnl_theo_inf_iter_right_ind_bis;
        rewrite <- IHhyp at 2;auto with proofs;
        apply gnl_theo_inf_sum_right;auto with proofs.
    - simpl in IHhyp.
      apply gnl_theo_inf_iter_left_ind_bis.
      rewrite <- IHhyp at 2;apply gnl_theo_inf_join;auto with proofs.
      repeat apply gnl_theo_inf_sum_right;auto with proofs.
    - simpl in IHhyp.
      apply gnl_theo_inf_iter_right_ind_bis.
      rewrite <- IHhyp at 2;apply gnl_theo_inf_join;auto with proofs.
      repeat apply gnl_theo_inf_sum_right;auto with proofs.
    - destruct H;simpl;auto with proofs.
      destruct H;simpl;auto;repeat apply gnl_theo_inf_join;try rewrite Tauto.if_same;auto with proofs.
      -- transitivity (@ø A O);auto with proofs.
      -- transitivity (@ø A O);auto with proofs.
      -- apply gnl_theo_inf_sum_right;auto with proofs.
  Qed.

  (** Then we can show that [gnl_recompose] is one as well. *)
  
  Global Instance gnl_recompose_proper r :
    Proper (dec_inf r ==> gnl_theo_inf r) gnl_recompose.
  Proof.
    intros e f (hyp_slat&hyp_reg).
    unfold gnl_recompose.
    apply sum_mono.
    - clear hyp_reg.
      generalize dependent (gnl_slat_proj f);generalize dependent (gnl_slat_proj e);
        clear e f;intros e f hyp.
      induction hyp;simpl in *;auto with proofs.
      + eauto with proofs.
      + destruct i.
      + destruct i.
      + destruct H.
    - induction (operators e);simpl;auto with proofs.
      apply gnl_theo_inf_join;auto.
      transitivity (flatten a (gnl_reg_proj a f)).
      + apply flatten_proper,hyp_reg. 
      + case_eq (inb a (operators f)).
        * rewrite <- inb_In.
          clear;induction (operators f);simpl;[tauto|].
          intros [<-|h];[|apply gnl_theo_inf_sum_right];auto with proofs.
        * rewrite<- Bool.not_true_iff_false,<- inb_In.
          intros F;transitivity (@ø A O);[|auto with proofs].
          apply not_operator_zero in F.
          destruct F as (F&_).
          apply is_zero_spec in F.
          revert F;clear hyp_slat hyp_reg e IHl;
            induction (gnl_reg_proj a f) as [|[]| | []|[]];simpl;discriminate||auto with proofs.
          -- rewrite Bool.andb_true_iff.
             intros (hyp1&hyp2).
             apply gnl_theo_inf_join;[apply IHr0_1|apply IHr0_2];auto with proofs.
          -- rewrite Bool.orb_true_iff.
             intros [hyp|hyp];rewrite (is_zero_ewp _ hyp).
             ++ destruct (ewp_r r0_2);repeat apply gnl_theo_inf_join;auto with proofs.
                ** rewrite IHr0_1;auto with proofs.
                ** rewrite IHr0_1;auto with proofs.
             ++ destruct (ewp_r r0_1);repeat apply gnl_theo_inf_join;auto with proofs.
                ** rewrite IHr0_2;auto with proofs.
                ** rewrite IHr0_2;auto with proofs.
  Qed.

  (** * Clean recomposition *)
  (** We now show that we can recompose the cleaned version of the projections in the same *)
  (** manner, yielding similar results. *)

  Definition gnl_clean_recompose e :=
    slat_to_gnl (gnl_slat_proj e) +
      fold_right sum ø (map (fun o => flatten o (Clean (gnl_reg_proj o (Clean e)))) 
                            (operators e)).


  (** Some invariance properties of [Clean]. *)
  
  Lemma is_zero_clean_exp (e : Reg (GExp A O))  : is_zero e = is_zero (Clean e).
  Proof.
    pose proof (Clean_is_eq e) as (h1&h2).
    apply is_zero_implb in h1,h2.
    destruct (is_zero (Clean e)),(is_zero e);discriminate||reflexivity.
  Qed.

  Lemma ewp_clean_exp (e : Reg (GExp A O))  : ewp_r e = ewp_r (Clean e).
  Proof.
    symmetry;apply ewp_r_eq.
    split;apply Empty_implies_any_theory,Clean_is_eq.
  Qed.
  
  Lemma flatten_Clean o (e : Reg (GExp A O)) :
    Ø |- flatten o (Clean e) == flatten o e.
  Proof.
    unfold Clean;induction e;simpl;try (now split;auto with proofs).
    - rewrite <- IHe1,<-IHe2.
      destruct (clean_exp e1),(clean_exp e2);simpl;try (now split;auto with proofs).
    - destruct o0.
      pose proof (is_zero_ewp e1) as h1'.
      pose proof (is_zero_ewp e2) as h2'.
      rewrite is_zero_clean_exp_None in h1',h2'.
      pose proof (ewp_clean_exp e1) as h1.
      pose proof (ewp_clean_exp e2) as h2.
      unfold Clean in h1,h2.
      destruct (ewp_r e1),(ewp_r e2),(clean_exp e1),(clean_exp e2);simpl;
        try rewrite <- h1;try rewrite <- h2;
        try (cut (true = false);[discriminate|(now apply h1')||(now apply h2')]);
        try rewrite <-IHe1;try rewrite <-IHe2;split;auto with proofs.
    - destruct o0.
      pose proof (is_zero_ewp e) as h1'.
      rewrite is_zero_clean_exp_None in h1'.
      pose proof (ewp_clean_exp e) as h1.
      unfold Clean in h1.
      destruct (clean_exp e);simpl;
        try rewrite <- h1;
        try (cut (true = false);[discriminate|(now apply h1')]);
        try rewrite <-IHe;split;auto with proofs.
  Qed.

  Lemma gnl_reg_trad_Clean o (e : GExp A O) :
    fKA Ø |- gnl_reg_trad o (Clean e) == gnl_reg_trad o e.
  Proof.
    unfold Clean;induction e;simpl;try (now split;auto with proofs).
    - rewrite <- IHe1,<-IHe2.
      destruct (clean_exp e1),(clean_exp e2);simpl;try (now split;auto with proofs).
    - destruct (o0 =?= o);subst;simpl.
      + rewrite <- IHe1,<- IHe2.
        destruct (clean_exp e1),(clean_exp e2);simpl;try (now split;auto with proofs).
        rewrite eq_dec_eq;reflexivity.
      + pose proof (is_zero_clean_exp_None e1) as h1'.
        pose proof (is_zero_clean_exp_None e2) as h2'.
        pose proof (Clean_is_eq e1) as h1.
        pose proof (Clean_is_eq e2) as h2.
        unfold Clean in h1,h2.
        destruct (clean_exp e1),(clean_exp e2);simpl;try (now split;auto with proofs).
        * rewrite eq_dec_neq by assumption.
          split;apply gnl_theo_axiom,fKA_r_eq;rewrite h1,h2;reflexivity.
        * split;auto with proofs.
          transitivity (@var _ One (Some (@ø A O)));auto with proofs.
          apply gnl_theo_axiom,fKA_r_eq;rewrite <- h1,<-h2;auto with proofs.
        * split;auto with proofs.
          transitivity (@var _ One (Some (@ø A O)));auto with proofs.
          apply gnl_theo_axiom,fKA_r_eq;rewrite <- h1,<-h2;auto with proofs.
        * split;auto with proofs.
          transitivity (@var _ One (Some (@ø A O)));auto with proofs.
          apply gnl_theo_axiom,fKA_r_eq;rewrite <- h1,<-h2;auto with proofs.
    - destruct (o0 =?= o);subst.
      + destruct (clean_exp e);simpl;try (now split;auto with proofs).
        * rewrite eq_dec_eq,IHe;reflexivity.
        * rewrite <- IHe;simpl.
          split;auto with proofs.
      + pose proof (is_zero_clean_exp_None e) as h1'.
        pose proof (Clean_is_eq e) as h1.
        unfold Clean in h1.
        destruct (clean_exp e);simpl;try (now split;auto with proofs).
        * rewrite eq_dec_neq by assumption.
          rewrite IHe;clear IHe h1'.
          split;(apply sum_mono;[now auto with proofs|]);
            apply gnl_theo_axiom,fKA_r_eq;rewrite h1;reflexivity.
        * rewrite <- IHe;simpl.
          split;[|apply gnl_theo_inf_join]; auto with proofs.
          transitivity (@var _ One (Some (@ø A O)));auto with proofs.
          apply gnl_theo_axiom,fKA_r_eq;rewrite <-h1;auto with proofs.
  Qed.
  
  Lemma gnl_reg_proj_Clean o (e : GExp A O) :
    fKA Ø |- gnl_reg_proj o (Clean e) == gnl_reg_proj o e.
  Proof.
    unfold Clean;induction e;simpl;try (now split;auto with proofs).
    - rewrite <- IHe1,<-IHe2.
      destruct (clean_exp e1),(clean_exp e2);simpl;try (now split;auto with proofs).
    - destruct (o0 =?= o);subst;simpl.
      + rewrite <- (gnl_reg_trad_Clean o e1),<- (gnl_reg_trad_Clean o e2).
        unfold Clean.
        destruct (clean_exp e1),(clean_exp e2);simpl;try (now split;auto with proofs).
        rewrite eq_dec_eq;reflexivity.
      + pose proof (is_zero_clean_exp_None e1) as h1'.
        pose proof (is_zero_clean_exp_None e2) as h2'.
        pose proof (Clean_is_eq e1) as h1.
        pose proof (Clean_is_eq e2) as h2.
        unfold Clean in h1,h2.
        destruct (clean_exp e1),(clean_exp e2);simpl;try (now split;auto with proofs).
        rewrite eq_dec_neq by assumption;reflexivity.
    - destruct (o0 =?= o);subst.
      + rewrite <- (gnl_reg_trad_Clean o e).
        unfold Clean.
        destruct (clean_exp e);simpl;try (now split;auto with proofs).
        * rewrite eq_dec_eq,IHe;reflexivity.
        * rewrite <- IHe;simpl.
          split;auto with proofs.
      + pose proof (is_zero_clean_exp_None e) as h1'.
        pose proof (Clean_is_eq e) as h1.
        unfold Clean in h1.
        destruct (clean_exp e);simpl;try (now split;auto with proofs).
        * rewrite eq_dec_neq by assumption;auto.
        * rewrite <- IHe;simpl;reflexivity.
  Qed.

  (** With these, we can show that the clean recomposition is equivalent to the standard one. *)

  Lemma gnl_clean_recompose_id e :
    Ø |- gnl_clean_recompose e == gnl_recompose e.
  Proof.
    unfold gnl_clean_recompose,gnl_recompose.
    cut (Ø |- fold_right sum ø (map (fun o : O => flatten o (Clean (gnl_reg_proj o (Clean e))))
                                  (operators e))
              == fold_right sum ø (map (fun o : O => flatten o (gnl_reg_proj o e)) (operators e)));
      [intros ->;reflexivity|].
    induction (operators e);[reflexivity|];simpl.
    cut (Ø |- flatten a (Clean (gnl_reg_proj a (Clean e))) == flatten a (gnl_reg_proj a e));
      [intros ->;rewrite IHl;reflexivity|clear IHl].
    rewrite flatten_Clean.
    split;apply flatten_proper;
    rewrite gnl_reg_proj_Clean;reflexivity.          
  Qed.
    
End gnl_recomp.
