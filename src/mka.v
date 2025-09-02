Require Import prelim gnl theories gnl_decomp.


Section mKAs.
  Context {A : Set}{decA:decidable_set A}.
  Context {Os : Set}{decOs:decidable_set Os}.
  Context {Op : Set}{decOp:decidable_set Op}.


  Definition mRegs := GExp A (Os+Op).
  Definition mSPs := GTerm A (Os+Op).

  Inductive mkas : relation mSPs :=
  | par_comm_msps o s t : mkas (s -[inr o]- t) (t -[inr o]- s). 

  Inductive mKAs : relation mRegs :=
  | par_comm_ms o e f : mKAs (e ×{inr o} f) (f ×{inr o} e). 

  Hint Constructors mkas mKAs : proofs.

  
  Definition mSPs_decomposition := @gnl_decomposition A (Os+Op).

  Definition mSPs_decomp_eq : relation mSPs_decomposition :=
    fun d1 d2 =>
      match d1,d2 with
      | (inl a),(inl b) => a = b
      | (inr (inl o,l)),(inr (inl o',m)) =>
          o = o' /\ list_lift (gnl_term_theo_eq mkas) l m
      | (inr (inr o,l)),(inr (inr o',m)) =>
          o = o' /\ multiset_lift (gnl_term_theo_eq mkas) l m
      | _,_ => False
      end.

  Global Instance mSPs_decomp_eq_Equiv : Equivalence mSPs_decomp_eq.
  Proof.
    split;repeat intros [|([],?)];simpl;try tauto.
    - split;reflexivity.
    - split;reflexivity.
    - intros ->;reflexivity.
    - intros (h&h');split;symmetry;assumption.
    - intros (h&h');split;symmetry;assumption.
    - intros -> ->;reflexivity.
    - intros (->&h1) (->&h2);split;auto.
      etransitivity;eassumption.
    - intros (->&h1) (->&h2);split;auto.
      etransitivity;eassumption.
  Qed.
 
  Lemma msps_decompose_proper_lifted o e1 e2:
    mkas |- e1 =T= e2 ->
    list_lift (gnl_term_theo_eq mkas) (gnl_term_to_list (inl o) e1) (gnl_term_to_list (inl o) e2).
  Proof.
    intro pr;induction pr;simpl;auto.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - destruct (o0 =?= (inl o));simpl.
      + subst;apply app_list_lift;assumption.
      + split;auto.
        rewrite pr1,pr2.
        reflexivity.
    - destruct (o0 =?= (inl o));simpl.
      + rewrite app_assoc;reflexivity.
      + split;auto with proofs.
    - destruct H;simpl;auto.
      repeat rewrite eq_dec_neq by discriminate.
      repeat split;auto with proofs.
  Qed.
  
  Lemma msps_decompose_proper_mlifted o e1 e2:
    mkas |- e1 =T= e2 ->
    multiset_lift (gnl_term_theo_eq mkas)
      (gnl_term_to_list (inr o) e1) (gnl_term_to_list (inr o) e2).
  Proof.
    intro pr;induction pr;simpl;auto.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - destruct (o0 =?= (inr o));simpl.
      + subst;apply app_multiset_lift;assumption.
      + eexists;split;[|reflexivity].
        repeat split;auto.
        rewrite pr1,pr2.
        reflexivity.
    - destruct (o0 =?= (inr o));simpl.
      + rewrite app_assoc;reflexivity.
      + eexists;split;[|reflexivity].
        repeat split;auto with proofs.
    - destruct H;simpl;auto.
      destruct (inr o0 =?= inr o);[inversion e;subst;clear e|];simpl.
      + eexists;split;[reflexivity|].
        apply eq_list_comm_app_comm.
      + eexists;split;[|reflexivity].
        repeat split;auto with proofs.
  Qed.
  
  Lemma msps_decompose_proper : Proper (gnl_term_theo_eq mkas ==> mSPs_decomp_eq) gnl_decompose.
  Proof.
    intros s t pr;induction pr;simpl;auto.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - repeat rewrite eq_dec_eq.
      destruct o;simpl;split;auto.
      + apply app_list_lift;apply msps_decompose_proper_lifted;assumption.
      + apply app_multiset_lift;apply msps_decompose_proper_mlifted;assumption.
    - destruct o;simpl;split;auto;repeat rewrite eq_dec_eq||rewrite app_assoc;reflexivity.
    - destruct H;simpl.
      split;auto.
      repeat rewrite eq_dec_eq.
      eexists;split;[reflexivity|].
      apply eq_list_comm_app_comm.
  Qed.

  Lemma msps_recompose_proper :
    Proper (mSPs_decomp_eq ==> or_none (gnl_term_theo_eq mkas)) gnl_recompose.
  Proof.
    intros [a|([o|o],l)] [b|([o'|o'],m)];simpl;try tauto.
    - intros ->;reflexivity.
    - intros (<-&h).
      rewrite h;reflexivity.
    - intros (<-&k&h'&h).
      rewrite h';clear l h'.
      revert m h;induction k;intros m h.
      + apply eq_list_comm_nil in h as ->.
        simpl;tauto.
      + apply eq_list_comm_cons in h as (m1&m2&->&h).
        transitivity (GProd (inr o) (a::m1++m2)).
        * apply IHk in h;simpl in *.
          destruct (GProd (inr o) k),(GProd (inr o) (m1++m2));simpl in *;try tauto||reflexivity.
          rewrite h;reflexivity.
        * simpl.
          destruct (m1 =?= []).
          -- subst;simpl in *.
             reflexivity.
          -- apply (GProd_Some _ (inr o)) in n as (t1&h1).
             destruct (m2 =?= []).
             ++ subst;rewrite app_nil_r in *;simpl in *.
                rewrite h1.
                assert (h2 : GProd (inr o) [a] = Some a) by reflexivity.
                destruct (GProd_app mkas _ _ _ _ _ h1 h2) as (T&h3&h4);rewrite h3.
                simpl;rewrite h4.
                auto with proofs.
             ++ apply (GProd_Some _ (inr o)) in n as (t2&h2).
                assert (h3 : GProd (inr o) (a::m2) = Some (t_prod (inr o) a t2))
                  by (simpl;rewrite h2;reflexivity).
                destruct (GProd_app mkas _ _ _ _ _ h1 h2) as (T1&hT1&ET1);rewrite hT1.
                destruct (GProd_app mkas _ _ _ _ _ h1 h3) as (T2&hT2&ET2);rewrite hT2.
                simpl.
                rewrite ET1,ET2.
                transitivity ((t1 -[inr o]- a)-[inr o]- t2);eauto with proofs.
  Qed.

  Definition mKAs_decomp_sat : mSPs_decomposition -> mRegs -> Prop :=
    fun d e =>
      match d with
      | inl a => a |=slat= (gnl_slat_proj e)
      | inr (inl o,l) => exists m, list_lift (gnl_theo_sat mkas) l (Word_to_list m)
                                   /\  m |=(ka)= gnl_reg_proj (inl o) e
      | inr (inr o,l) => exists m, multiset_lift (gnl_theo_sat mkas) l (Word_to_list m)
                                   /\ m |=(ka)= gnl_reg_proj (inr o) e
      end.
  Definition mKAs_decomp_sat_bis : mSPs_decomposition -> mRegs -> Prop :=
    fun d e =>
      match d with
      | inl a => a |=slat= gnl_slat_proj e
      | inr (inl o,l) => exists m, list_lift (gnl_theo_sat mkas) l (Word_to_list m)
                                   /\  m |=(ka)= gnl_reg_proj (inl o) e
      | inr (inr o,l) => exists m, list_lift (gnl_theo_sat mkas) l (Word_to_list m)
                                   /\  m |=(cka)= gnl_reg_proj (inr o) e
      end.
  
  Lemma mKAs_decomp_sat_iff_bis d e :
    mKAs_decomp_sat d e <-> mKAs_decomp_sat_bis d e.
  Proof.
    destruct d as [|([],l)];simpl;try tauto.
    setoid_rewrite cKA_iff_cka_KA.
    split.
    - intros (m&(k&h1&h2)&h3).
      exists (list_to_Word k).
      split;[|exists m;split;[|]];auto.
      + rewrite list_to_Word_and_back;assumption.
      + rewrite h2,Word_to_list_and_back;reflexivity.
    - intros (m&h1&m'&h2&h3).
      exists m';split;auto.
      clear h3 e.
      exists (Word_to_list m);split;auto.
      rewrite h2;reflexivity.
  Qed.

  Lemma get_var_msps_eq e f : mkas |- e =T= f -> get_var e = get_var f.
  Proof.
    intro pr;induction pr;simpl;auto.
    - etransitivity;eauto.
    - destruct H.
      simpl;reflexivity.
  Qed.

  
  Lemma get_op_msps_eq  (e f : gnl_term) : mkas |- e =T= f -> get_op e = get_op f.
  Proof.
    intro pr;induction pr;simpl;auto.
    - etransitivity;eauto.
    - destruct H.
      simpl;reflexivity.
  Qed.
  
  Lemma gnl_msps_sat_vars  (e : gnl_exp) :
    forall x, t_var x |=(mkas)= e ->  x |=slat= gnl_slat_proj e.
  Proof.
    induction e;simpl.
    - tauto.
    - intros x0 E;apply get_var_msps_eq in E;inversion E;reflexivity.
    - intuition.
    - intros x (s1&s2&E&_&_).
      apply get_var_msps_eq in E;inversion E. 
    - intros x (s'&L&hs'&E&hL).
      revert s' hs' E.
      induction L;simpl.
      + discriminate.
      + intros s' hs' E.
        destruct (GProd o L);inversion hs';subst;clear hs'.
        * apply get_var_msps_eq in E;discriminate.
        * apply IHe,hL;left.
          apply get_var_msps_eq in E.
          destruct s';inversion E.
          reflexivity.
  Qed.
  
  Lemma gnl_msps_sat_vars_iff  (e : gnl_exp) :
    forall x, t_var x |=(mkas)= e <-> x |=slat= gnl_slat_proj e.
  Proof.
    intro x;split;[apply gnl_msps_sat_vars|revert x].
    induction e;simpl.
    - tauto.
    - intros x0 E.
      apply get_var_eq in E;inversion E;subst;clear E.
      reflexivity.
    - intuition.
    - tauto. 
    - intros x ih;apply IHe in ih.
      exists (t_var x),[t_var x];repeat split;auto with proofs.
      intros ? [<-|F];[|exfalso;apply F];auto.
  Qed.

  
  Global Instance mKAs_sound s :
    Proper (mKAs ==> Basics.impl) (gnl_theo_sat mkas s).
  Proof.
    intros e f h hyp.
    destruct h;eauto with proofs.
    revert hyp;intros (s1&s2&h1&h2&h3);exists s2,s1;repeat split;eauto with proofs.
  Qed.
  
  Lemma mKAs_sat_to_gnl_sat s e :
    s |=(mkas)= e <-> exists t, mkas |- s =T= t /\ t |=(Ø)= e.
  Proof. apply gnl_theo_sat_decompose. Qed.
  
  Lemma msps_decompose_eq :
    forall s t : mSPs,
      mkas |- s =T= t ->
      (exists a, s = t_var a /\ t = t_var a)
      \/ (exists o l m, gnl_decompose s = inr (inl o,l)
                       /\ gnl_decompose t = inr (inl o,m)
                       /\ list_lift (gnl_term_theo_eq mkas) l m)
      \/ (exists o l m, gnl_decompose s = inr (inr o,l)
                       /\ gnl_decompose t = inr (inr o,m)
                       /\ multiset_lift (gnl_term_theo_eq mkas) l m).
  Proof.
    intros s t pr.
    apply msps_decompose_proper in pr.
    remember (gnl_decompose s) as S.
    remember (gnl_decompose t) as T.
    destruct S as [a|([],l)],T as [b|([],m)];simpl in *;try tauto.
    - left;subst.
      destruct s as [], t as [];simpl in HeqS,HeqT;try discriminate.
      inversion HeqS;inversion HeqT;subst;exists a0;split;auto.
    - destruct pr as (<-&h).
      right;left;exists o,l,m;auto.
    - destruct pr as (<-&h).
      right;right;exists o,l,m;auto.
  Qed.

  Theorem mKAs_semantic_decomposition d e :
    mKAs_decomp_sat d e <-> exists s, mSPs_decomp_eq d (gnl_decompose s)
                                      /\ s |=(mkas)= e.
  Proof.
    destruct d as [|([o|o],l)];simpl.
    - rewrite <- gnl_msps_sat_vars_iff;simpl.
      split.
      + intro h;exists (t_var a);split;simpl;auto.
      + intros (s&h1&h2).
        destruct s as [|[]];simpl in h1;try tauto.
        subst;assumption.
    - transitivity (exists l', list_lift (gnl_term_theo_eq mkas) l l'
                               /\ gnl_decomp_sat Ø (inr (inl o,l')) e).
      + split.
        * intros (m&h1&h2).
          apply (list_lift_composition _ (gnl_term_theo_eq mkas)(gnl_theo_sat Ø))
            in h1 as (k&h1&h3).
          -- exists k;split;auto;simpl.
             exists m;split;auto.
          -- intros;apply mKAs_sat_to_gnl_sat;assumption.
        * intros (l'&h1&m&h2&h3).
          exists m;split;auto.
          rewrite h1.
          revert h2;clear l h1 h3.
          generalize (Word_to_list m);clear m.
          induction l';simpl;auto.
          intros [];simpl;auto.
          intros (h1&h2);split;auto.
          apply mKAs_sat_to_gnl_sat;exists a;split;auto with proofs.
      + setoid_rewrite gnl_semantic_correspondance.
        split.
        * intros (l'&h1&t'&h2&h3).
          exists t';split;auto.
          -- pose proof h2 as h2';apply gnl_recompose_proper in h2;simpl in h2.
             destruct (recompose_decompose t') as (T&hT1&hT2).
             rewrite hT1 in h2;simpl in h2;auto.
             destruct (l' =?= []);
               [exfalso;subst;destruct l;[clear h1|];auto|].
             apply (GProd_Some _ (inl o)) in n as (T'&hT').
             rewrite hT' in h2;simpl in h2.
             rewrite <- h2 in hT2.
             apply gnl_decompose_eq in hT2 as [(a&->&->)|(o'&m1&m2&hm1&hm2&hT2)];simpl;auto.
             rewrite hm1 in *;simpl in *.
             destruct h2' as (<-&h2').
             split;auto.
             rewrite h1.
             clear T T' e m2 h1 h2 h3 hT1 hm2 hm1 hT2 hT'.
             revert m1 h2';induction l';intros [|s m];simpl;auto.
             intros (h1&h2);split;auto.
             replace a with (id a) by reflexivity.
             rewrite h1;unfold id;reflexivity.
          -- apply mKAs_sat_to_gnl_sat;exists t';split;auto with proofs.
        * intros (s&h1&h2).
          remember (gnl_decompose s) as d.
          destruct d as [|([],m)];try tauto.
          destruct h1 as (<-&h1).
          apply mKAs_sat_to_gnl_sat in h2 as (t&h2&h3).
          apply msps_decompose_eq in h2 as [(a&->&->)|[(o'&m1&m2&hm1&hm2&hT2)
                                                      |(o'&m1&m2&hm1&hm2&hT2)]];
            simpl;try rewrite hm1 in Heqd;try inversion Heqd;subst;clear Heqd.
          exists m2;split;auto.
          -- rewrite h1;auto.
          -- exists t;split;auto.
             rewrite hm2;split;auto;reflexivity.
   - transitivity (exists l', multiset_lift (gnl_term_theo_eq mkas) l l'
                              /\ gnl_decomp_sat Ø (inr (inr o,l')) e).
     + split.
        * intros (m&(k&h1&h1')&h2).
          apply (list_lift_composition _ (gnl_term_theo_eq mkas)(gnl_theo_sat Ø))
            in h1 as (k'&h1&h3).
          -- cut (multiset_lift (gnl_theo_sat Ø) k' (Word_to_list m)).
             ++ intros h4;apply multiset_lift_inv in h4 as (k''&h4&h5).
                exists k'';split;auto.
                ** exists k';auto.
                ** simpl.
                   exists m;split;auto.
             ++ exists k;split;auto.
          -- intros;apply mKAs_sat_to_gnl_sat;assumption.
        * intros (l'&(k&h1&h1')&m&h2&h3).
          exists m;split;auto.
          cut (multiset_lift (gnl_theo_sat Ø) k (Word_to_list m));
            [|apply multiset_lift_inv;exists l';auto].
          intros (k'&h4&h5).
          exists k'.
          split;auto.
          eapply list_lift_composition_inv;[|apply h1|apply h4].
          intros s f t H1 H2.
          apply mKAs_sat_to_gnl_sat.
          exists t;auto.
     + setoid_rewrite gnl_semantic_correspondance.
        split.
        * intros (l'&h1&t'&h2&h3).
          exists t';split;auto.
          -- pose proof h2 as h2';apply gnl_recompose_proper in h2;simpl in h2.
             destruct (recompose_decompose t') as (T&hT1&hT2).
             rewrite hT1 in h2;simpl in h2;auto.
             destruct (l' =?= []);
               [exfalso;subst;destruct l;[clear h1|];auto|].
             apply (GProd_Some _ (inr o)) in n as (T'&hT').
             rewrite hT' in h2;simpl in h2.
             rewrite <- h2 in hT2.
             apply gnl_decompose_eq in hT2 as [(a&->&->)|(o'&m1&m2&hm1&hm2&hT2)];simpl;auto.
             rewrite hm1 in *;simpl in *.
             destruct h2' as (<-&h2').
             split;auto.
             rewrite h1.
             clear T T' e m2 h1 h2 h3 hT1 hm2 hm1 hT2 hT'.
             revert m1 h2';induction l';intros [|s m];simpl;try tauto||reflexivity.
             intros (h1&h2).
             apply IHl' in h2 as (k&h2&h3).
             exists (s::k).
             split;auto;[|rewrite h3;reflexivity].
             split;auto.
             replace a with (id a) by reflexivity.
             rewrite h1;unfold id;reflexivity.
          -- apply mKAs_sat_to_gnl_sat;exists t';split;auto with proofs.
        * intros (s&h1&h2).
          remember (gnl_decompose s) as d.
          destruct d as [|([],m)];try tauto.
          destruct h1 as (<-&h1).
          apply mKAs_sat_to_gnl_sat in h2 as (t&h2&h3).
          apply msps_decompose_eq in h2 as [(a&->&->)|[(o'&m1&m2&hm1&hm2&hT2)
                                                      |(o'&m1&m2&hm1&hm2&hT2)]];
            simpl;try rewrite hm1 in Heqd;try inversion Heqd;subst;clear Heqd.
          exists m2;split;auto.
          -- rewrite h1;auto.
          -- exists t;split;auto.
             rewrite hm2;split;auto;reflexivity.
  Qed.
  
End mKAs.
  
Hint Constructors mkas mKAs : proofs.
Arguments mRegs : clear implicits.
Arguments mSPs : clear implicits.

Section mKA.
  Context {A : Set}{decA:decidable_set A}.
  Context {Os : Set}{decOs:decidable_set Os}.
  Context {Op : Set}{decOp:decidable_set Op}.


  Definition mReg := GExp (option A) (Os+Op).
  Definition mSP := GTerm (option A) (Os+Op).

  Notation "1_m" := (var None).
  Notation "1_msp" := (t_var None).
  Notation var_m := (fun a : A => var (Some a)).
  Notation var_msp := (fun a : A => t_var (Some a)).
  
  Inductive mka : relation mSP :=
  | one_left_msp o w : mka (1_msp -[o]- w) w
  | one_right_msp o w : mka (w -[o]- 1_msp) w
  | par_comm_msp o s t : mka (s -[inr o]- t) (t -[inr o]- s). 

  Inductive mKA : relation mReg :=
  | one_left_m o e : mKA (1_m ×{o} e) e
  | one_right_m o e : mKA (e ×{o} 1_m) e
  | one_left_inv_m o e : mKA e (1_m ×{o} e)
  | one_right_inv_m o e : mKA e (e ×{o} 1_m)
  | par_comm_m o e f : mKA (e ×{inr o} f) (f ×{inr o} e). 

  Hint Constructors mka mKA : proofs.
  Notation in_mlang := (gnl_theo_sat mka).
  Infix " =mKA " := (gnl_theo_eq mKA) (at level 50).
  Infix " <=mKA " := (gnl_theo_inf mKA) (at level 50).
  
  Definition prod_opt o :
    option (mSPs A Os Op) -> option (mSPs A Os Op) -> option (mSPs A Os Op) :=
  fun s t => 
  match s,t with
  | None,None => None
  | None,Some u|Some u,None => Some u
  | Some s',Some t' => Some (t_prod o s' t')
  end.
  
  Fixpoint mSP_to_mSPs_opt (s : mSP) : option (mSPs A Os Op) :=
  match s with
  | 1_msp => None
  | t_var (Some a) => Some (t_var a)
  | t_prod o u v => prod_opt o (mSP_to_mSPs_opt u) (mSP_to_mSPs_opt v)
  end.
  
  Fixpoint mSPs_to_mSP (s : mSPs A Os Op) : mSP :=
  match s with
  | t_var a => t_var (Some a)
  | t_prod o u v => mSPs_to_mSP u -[o]- mSPs_to_mSP v
  end.
  
  Definition mSPs_opt_to_mSP : option (mSPs A Os Op) -> mSP :=
  fun s =>
  match s with
  | None => 1_msp
  | Some s => mSPs_to_mSP s
  end.
  
  Lemma mSPs_opt_to_mSP_and_back s :
    mSP_to_mSPs_opt (mSPs_opt_to_mSP s) = s.
  Proof.
    destruct s;simpl;auto.
    induction m;simpl;auto.
    rewrite IHm1,IHm2.
    reflexivity.
  Qed.
  
  Lemma mSP_to_mSPs_and_back s :
    mka |- mSPs_opt_to_mSP (mSP_to_mSPs_opt s) =T= s.
  Proof.
    induction s as [[|]|];simpl;auto with proofs.
     rewrite <- IHs1,<- IHs2 at 2.
    destruct (mSP_to_mSPs_opt s1), (mSP_to_mSPs_opt s2);simpl;auto with proofs.
  Qed.
  
  Lemma mSP_to_mSPs_opt_proper :
    Proper (gnl_term_theo_eq mka ==> or_none (gnl_term_theo_eq mkas)) mSP_to_mSPs_opt.
  Proof.
    intros s t pr;induction pr;simpl.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - destruct (mSP_to_mSPs_opt e1), (mSP_to_mSPs_opt f1),
        (mSP_to_mSPs_opt e2), (mSP_to_mSPs_opt f2);simpl in *;try tauto.
      rewrite IHpr1,IHpr2;reflexivity.
    - destruct (mSP_to_mSPs_opt e), (mSP_to_mSPs_opt f), (mSP_to_mSPs_opt g);simpl;auto with proofs.
    - destruct H;simpl;auto.
      + destruct (mSP_to_mSPs_opt w);reflexivity.
      + destruct (mSP_to_mSPs_opt w);reflexivity.
      + destruct (mSP_to_mSPs_opt s),(mSP_to_mSPs_opt t);simpl;auto with proofs.
  Qed.
  
  Lemma mSPs_opt_to_mSP_proper :
    Proper (or_none (gnl_term_theo_eq mkas) ==> gnl_term_theo_eq mka) mSPs_opt_to_mSP.
  Proof.
    intros [s|] [t|];simpl;tauto||auto with proofs.
    intros pr;induction pr;simpl;auto with proofs.
    - rewrite IHpr1,IHpr2;auto with proofs.
    - destruct H;simpl;auto with proofs.
  Qed.
  
  Fixpoint ewp (e : mReg) : bool :=
    match e with
    | var (Some _) | zero => false
    | 1_m => true
    | prod _ e f => ewp e && ewp f
    | sum e f => ewp e || ewp f
    | iter _ e => ewp e
    end.

   Global Instance ewp_inf : Proper (gnl_theo_inf mKA ==> Bool.le) ewp.
   Proof.
    unfold Bool.le;intros e f pr;induction pr;simpl;try (rewrite IHpr1,IHpr2);auto.
    - destruct (ewp e);auto.
    - destruct (ewp e);auto.
      rewrite IHpr1 in IHpr2;auto.
    - destruct (ewp e1),(ewp e2),(ewp f1),(ewp f2);simpl in *;auto.
    - destruct (ewp e1),(ewp e2);simpl in *;auto.
    - destruct (ewp e1),(ewp e2);simpl in *;auto.
    - destruct (ewp e1),(ewp e2);simpl in *;auto.
    - destruct (ewp e),(ewp f),(ewp g);simpl in *;auto.
    - destruct (ewp e),(ewp f),(ewp g);simpl in *;auto.
    - destruct (ewp e),(ewp f),(ewp g);simpl in *;auto.
    - destruct (ewp e),(ewp f),(ewp g);simpl in *;auto.
    - destruct (ewp e);simpl in *;auto.
    - destruct (ewp e);simpl in *;auto.
    - destruct (ewp e);simpl in *;auto.
    - simpl in *;destruct (ewp e),(ewp f);simpl in *;auto.
    - simpl in *;destruct (ewp e),(ewp f);simpl in *;auto.
    - destruct H;simpl. 
      + destruct (ewp e);simpl in *;auto.
      + destruct (ewp e);simpl in *;auto.
      + destruct (ewp e);simpl in *;auto.
      + destruct (ewp e);simpl in *;auto. 
      + destruct (ewp e),(ewp f);simpl in *;auto.
   Qed.
   
   Global Instance ewp_eq : Proper (gnl_theo_eq mKA ==> eq) ewp.
   Proof.
     intros e f (h1&h2);apply ewp_inf in h1,h2;unfold Bool.le in *.
     destruct (ewp e),(ewp f);simpl in *;auto.
   Qed.
  
  Global Instance mKA_sound s :
    Proper (mKA ==> Basics.impl) (gnl_theo_sat mka s).
  Proof.
    intros e f h hyp.
    revert hyp;destruct h;simpl.
    + intros (s1&s2&h1&h2&h3).
      cut (mka |- s =T= s2).
      * intros ->;assumption.
      * rewrite h1,h2;auto with proofs.
    + intros (s1&s2&h1&h2&h3).
      cut (mka |- s =T= s1).
      * intros ->;assumption.
      * rewrite h1,h3;auto with proofs.
    + intros h;exists 1_msp,s;repeat split;auto with proofs.
    + intros h;exists s,1_msp;repeat split;auto with proofs.
    + intros (s1&s2&h1&h2&h3);exists s2,s1;repeat split;eauto with proofs.
  Qed.
  
  Definition is_one : mSP -> bool :=
  fun s => 
    match mSP_to_mSPs_opt s with
    | None => true
    | Some _ => false
    end.

  Lemma is_one_spec s : is_one s = true <-> mka |- 1_msp =T= s.
  Proof.
    unfold is_one;split.
    - induction s as [[|]|];simpl;discriminate||auto with proofs.
      destruct (mSP_to_mSPs_opt s1), (mSP_to_mSPs_opt s2);simpl in *;try discriminate.
      intros _.
      rewrite <- IHs1,<- IHs2 by reflexivity.
      auto with proofs.
    - intros h;apply mSP_to_mSPs_opt_proper in h.
      destruct (mSP_to_mSPs_opt s);auto.
  Qed.
     
  Lemma ewp_spec e : ewp e = true <-> in_mlang 1_msp e.
  Proof.
    induction e as [|[|]| | |];simpl.
    - split;[discriminate|tauto].
    - split;[discriminate|intro F].
      apply mSP_to_mSPs_opt_proper in F;simpl in F;tauto.
    - split;auto with proofs. 
    - rewrite Bool.orb_true_iff.
      tauto.
    - rewrite Bool.andb_true_iff,IHe1,IHe2;clear IHe1 IHe2.
      split.
      + intros (h1&h2);exists 1_msp,1_msp;repeat split;auto with proofs.
      + intros (s1&s2&h&h1&h2).
        cut (gnl_term_theo_eq mka 1_msp s1 /\ gnl_term_theo_eq mka 1_msp s2).
        * intros (h'1&h'2);rewrite h'1,h'2 at 1; tauto.
        * repeat rewrite <- is_one_spec in *.
          unfold is_one in *;simpl in *.
          destruct (mSP_to_mSPs_opt s1), (mSP_to_mSPs_opt s2); simpl in *;auto.
    - rewrite IHe;clear IHe;split.
      + intros h;exists 1_msp,[1_msp];repeat split;auto with proofs.
      intros ? [<-|F];[|exfalso];auto.
      + intros (s&L&h1&h2&h3).
        revert s h1 h2 h3;induction L;simpl;[discriminate|].
        destruct (L =?= []).
        * subst;clear IHL;simpl.
        intros s E;inversion E;subst;clear E.
        intros h1 h2;rewrite h1;apply h2;now left.
        * apply (GProd_Some _ o) in n as (T&hT).
        rewrite hT in *.
        intros;apply (IHL T);auto.
        inversion h1;subst;clear h1.
        repeat rewrite <- is_one_spec in *.
        unfold is_one in *;simpl in *.
        destruct (mSP_to_mSPs_opt a), (mSP_to_mSPs_opt T); simpl in *;auto.
  Qed.

  Lemma ewp_alt_spec e : ewp e = true <-> 1_m <=mKA e.
  Proof.
    split.
    - induction e as [|[|]| | |];simpl;discriminate||auto with proofs.
      + rewrite Bool.orb_true_iff;intros [h|h];[apply IHe1 in h|apply IHe2 in h];
          rewrite h;auto with proofs.
      + rewrite Bool.andb_true_iff;intros (h1&h2);apply IHe1 in h1;apply IHe2 in h2;
          rewrite <-h1,<-h2;auto with proofs.
      + intro h;rewrite (IHe h);eauto with proofs.
    - intros h;apply ewp_inf in h;unfold Bool.le in h.
      simpl in h;assumption.
  Qed.
  
  Fixpoint mReg_to_mRegs (e : mReg) : mRegs A Os Op := 
  match e with
  | ø | 1_m => ø
  | var (Some a) => var a
  | e ×{o} f =>
      ((if (ewp e) then mReg_to_mRegs f else ø)
       + (if (ewp f) then mReg_to_mRegs e else ø))
      + (mReg_to_mRegs e ×{o} mReg_to_mRegs f)
  | e + f => mReg_to_mRegs e + mReg_to_mRegs f
  | e^{o} => (mReg_to_mRegs e)^{o}
  end.
  
  Fixpoint mRegs_to_mReg (e : mRegs A Os Op) : mReg := 
  match e with
  | ø => ø
  | var a => var (Some a)
  | e ×{o} f => mRegs_to_mReg e ×{o} mRegs_to_mReg f
  | e + f => mRegs_to_mReg e + mRegs_to_mReg f
  | e^{o} => (mRegs_to_mReg e)^{o}
  end.
  
  Lemma ewp_mRegs_to_mReg e : ewp (mRegs_to_mReg e) = false.
  Proof.
    induction e;simpl;auto.
    - rewrite IHe1,IHe2;auto.
    - rewrite IHe1,IHe2;auto.
  Qed.
    
  Lemma mRegs_to_mReg_and_back e :
    mKAs |- (mReg_to_mRegs (mRegs_to_mReg e)) == e.
  Proof.
    induction e;simpl;try rewrite IHe||rewrite IHe1,IHe2;
     try (now split;auto with proofs).
    repeat rewrite ewp_mRegs_to_mReg.
    rewrite IHe1,IHe2.
    split;auto 10 with proofs.
  Qed.
  
  Global Instance mRegs_to_mReg_proper :
    Proper (gnl_theo_inf mKAs ==> gnl_theo_inf mKA) mRegs_to_mReg.
  Proof.
    intros e f pr;induction pr;simpl;auto with proofs.
    - eauto with proofs.
    - destruct H;simpl;auto with proofs.
  Qed.

  Lemma gnl_eq_sum_assoc {X O : Set} (r : relation (@gnl_exp X O)) e f g :
    gnl_theo_eq r (sum e (sum f g)) (sum (sum e f) g).
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_eq_prod_assoc {X O : Set} (r : relation (@gnl_exp X O)) o e f g :
    gnl_theo_eq r (prod o e (prod o f g)) (prod o (prod o e f) g).
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  
  Lemma gnl_eq_sum_prod {X O : Set} (r : relation (@gnl_exp X O)) o e f g :
    gnl_theo_eq r (prod o (sum f g) e) (sum (prod o f e) (prod o g e)).
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.

  Lemma gnl_eq_prod_sum {X O : Set} (r : relation (@gnl_exp X O)) o e f g :
    gnl_theo_eq r (prod o e (sum f g)) (sum (prod o e f) (prod o e g)).
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.

  Lemma gnl_theo_eq_sum_zero_e:
    forall {X O : Set} (r : relation gnl_exp) (e : @gnl_exp X O),
    gnl_theo_eq r (sum zero e) e.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.

  Lemma gnl_theo_eq_sum_e_zero:
    forall {X O : Set} (r : relation gnl_exp) (e : @gnl_exp X O),
      gnl_theo_eq r (sum e zero) e.
  Proof. split;repeat apply gnl_theo_inf_join;auto with proofs. Qed.

  Lemma gnl_theo_eq_prod_zero_e:
    forall {X O : Set} (r : relation gnl_exp) (i : O) (e : @gnl_exp X O),
    gnl_theo_eq r (prod i zero e) zero.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.

  Lemma gnl_theo_eq_prod_e_zero:
    forall {X O : Set} (r : relation gnl_exp) (i : O) (e : @gnl_exp X O),
      gnl_theo_eq r (prod i e zero) zero.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_prod_one_e i e:
    gnl_theo_eq mKA (prod i 1_m e) e.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.

  Lemma gnl_theo_eq_prod_e_one i e :
    gnl_theo_eq mKA (prod i e 1_m) e.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.

  Global Instance mReg_to_mRegs_proper :
    Proper (gnl_theo_inf mKA ==> gnl_theo_inf mKAs) mReg_to_mRegs.
  Proof.
    intros e f pr;induction pr;simpl;auto with proofs.
    - eauto with proofs.
    - pose proof pr1 as le1;apply ewp_inf in le1.
      pose proof pr2 as le2;apply ewp_inf in le2.
      unfold Bool.le in *.
      destruct (ewp e1),(ewp e2),(ewp f1),(ewp f2);simpl;try discriminate;
        repeat rewrite gnl_eq_sum_assoc;
        repeat rewrite IHpr1||rewrite IHpr2;
        repeat apply gnl_theo_inf_join;auto with proofs;
        repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l.
    - generalize (mReg_to_mRegs g);generalize (mReg_to_mRegs f);generalize (mReg_to_mRegs e);
        intros a b c.
      destruct (ewp e),(ewp f),(ewp g);simpl;
        repeat rewrite (gnl_theo_inf_prod_zero_e mKAs)
        || rewrite (gnl_theo_inf_prod_e_zero mKAs)
        || rewrite (gnl_theo_eq_sum_zero_e mKAs)
        || rewrite (gnl_theo_eq_sum_e_zero mKAs)
        || rewrite (gnl_eq_sum_prod mKAs)
        || rewrite (gnl_eq_prod_sum mKAs)
        || rewrite (gnl_eq_prod_assoc mKAs)
        || rewrite (gnl_eq_sum_assoc mKAs);
        repeat apply gnl_theo_inf_join;auto with proofs;
        try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
        try (now transitivity zero;eauto with proofs).
    - destruct (ewp e),(ewp f),(ewp g);simpl;
        repeat rewrite gnl_eq_sum_assoc
        || rewrite gnl_eq_prod_assoc
        || rewrite gnl_theo_eq_prod_zero_e
        || rewrite gnl_theo_eq_prod_e_zero
        || rewrite gnl_eq_sum_prod
        || rewrite gnl_eq_prod_sum  ;
        repeat apply gnl_theo_inf_join;auto with proofs;
        try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
        try (now transitivity zero;eauto with proofs).
    - destruct (ewp e),(ewp f),(ewp g);simpl;
        repeat rewrite gnl_eq_sum_assoc
        || rewrite gnl_eq_prod_assoc
        || rewrite gnl_theo_eq_prod_zero_e
        || rewrite gnl_theo_eq_prod_e_zero
        || rewrite gnl_eq_sum_prod
        || rewrite gnl_eq_prod_sum  ;
        repeat apply gnl_theo_inf_join;auto with proofs;
        try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
        try (now transitivity zero;eauto with proofs).
    - destruct (ewp e),(ewp f),(ewp g);simpl;
        repeat rewrite gnl_eq_sum_assoc
        || rewrite gnl_eq_prod_assoc
        || rewrite gnl_theo_eq_prod_zero_e
        || rewrite gnl_theo_eq_prod_e_zero
        || rewrite gnl_eq_sum_prod
        || rewrite gnl_eq_prod_sum  ;
        repeat apply gnl_theo_inf_join;auto with proofs;
        try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
        try (now transitivity zero;eauto with proofs).
    - destruct (ewp e);simpl;
        repeat rewrite gnl_eq_sum_assoc
        || rewrite gnl_eq_prod_assoc
        || rewrite gnl_theo_eq_prod_zero_e
        || rewrite gnl_theo_eq_prod_e_zero
        || rewrite gnl_eq_sum_prod
        || rewrite gnl_eq_prod_sum  ;
        repeat apply gnl_theo_inf_join;auto with proofs;
        try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
        try (now transitivity zero;eauto with proofs).
     - destruct (ewp e);simpl;
        repeat rewrite gnl_eq_sum_assoc
        || rewrite gnl_eq_prod_assoc
        || rewrite gnl_theo_eq_prod_zero_e
        || rewrite gnl_theo_eq_prod_e_zero
        || rewrite gnl_eq_sum_prod
        || rewrite gnl_eq_prod_sum  ;
        repeat apply gnl_theo_inf_join;auto with proofs;
        try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
         try (now transitivity zero;eauto with proofs).
     - destruct (ewp e);simpl;
        repeat rewrite gnl_eq_sum_assoc
        || rewrite gnl_eq_prod_assoc
        || rewrite gnl_theo_eq_prod_zero_e
        || rewrite gnl_theo_eq_prod_e_zero
        || rewrite gnl_eq_sum_prod
        || rewrite gnl_eq_prod_sum  ;
        repeat apply gnl_theo_inf_join;auto with proofs;
        try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
         try (now eauto with proofs).
     - destruct (ewp e);simpl;
        repeat rewrite gnl_eq_sum_assoc
        || rewrite gnl_eq_prod_assoc
        || rewrite gnl_theo_eq_prod_zero_e
        || rewrite gnl_theo_eq_prod_e_zero
        || rewrite gnl_eq_sum_prod
        || rewrite gnl_eq_prod_sum  ;
        repeat apply gnl_theo_inf_join;auto with proofs;
        try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
         try (now eauto with proofs).
     - simpl in *.
       generalize dependent (mReg_to_mRegs f);
         generalize dependent (mReg_to_mRegs e);intros r1 r2 h.
       destruct (ewp e),(ewp f);simpl;
        repeat rewrite gnl_eq_sum_assoc
        || rewrite gnl_eq_prod_assoc
        || rewrite gnl_theo_eq_prod_zero_e
        || rewrite gnl_theo_eq_prod_e_zero
        || rewrite gnl_eq_sum_prod
        || rewrite gnl_eq_prod_sum  ;
        repeat apply gnl_theo_inf_join;auto with proofs;
         try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
         try apply gnl_theo_inf_iter_left_ind || apply gnl_theo_inf_iter_left_ind_bis;
         rewrite <- h at 2; 
         repeat rewrite gnl_eq_sum_assoc
         || rewrite gnl_eq_prod_assoc
         || rewrite gnl_theo_eq_prod_zero_e
         || rewrite gnl_theo_eq_prod_e_zero
         || rewrite gnl_eq_sum_prod
         || rewrite gnl_eq_prod_sum  ;
         repeat apply gnl_theo_inf_join;auto with proofs;
         try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l).
     - simpl in *.
       generalize dependent (mReg_to_mRegs f);
         generalize dependent (mReg_to_mRegs e);intros r1 r2 h.
       destruct (ewp e),(ewp f);simpl;
        repeat rewrite gnl_eq_sum_assoc
        || rewrite gnl_eq_prod_assoc
        || rewrite gnl_theo_eq_prod_zero_e
        || rewrite gnl_theo_eq_prod_e_zero
        || rewrite gnl_eq_sum_prod
        || rewrite gnl_eq_prod_sum  ;
        repeat apply gnl_theo_inf_join;auto with proofs;
         try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l);
         try apply gnl_theo_inf_iter_right_ind || apply gnl_theo_inf_iter_right_ind_bis;
         rewrite <- h at 2; 
         repeat rewrite gnl_eq_sum_assoc
         || rewrite gnl_eq_prod_assoc
         || rewrite gnl_theo_eq_prod_zero_e
         || rewrite gnl_theo_eq_prod_e_zero
         || rewrite gnl_eq_sum_prod
         || rewrite gnl_eq_prod_sum  ;
         repeat apply gnl_theo_inf_join;auto with proofs;
         try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l).
     - simpl in *;
         generalize dependent (mReg_to_mRegs f);
         generalize dependent (mReg_to_mRegs e);intros r1 r2 h.
       apply gnl_theo_inf_iter_left_ind_bis.
       rewrite <- h at 2.
       destruct (ewp e),(ewp f);simpl;
         repeat rewrite gnl_eq_sum_assoc
         || rewrite gnl_eq_prod_assoc
         || rewrite gnl_theo_eq_prod_zero_e
         || rewrite gnl_theo_eq_prod_e_zero
         || rewrite gnl_eq_sum_prod
         || rewrite gnl_eq_prod_sum  ;
         repeat apply gnl_theo_inf_join;auto with proofs;
         try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l).
     - simpl in *;
         generalize dependent (mReg_to_mRegs f);
         generalize dependent (mReg_to_mRegs e);intros r1 r2 h.
       apply gnl_theo_inf_iter_right_ind_bis.
       rewrite <- h at 2.
       destruct (ewp e),(ewp f);simpl;
         repeat rewrite gnl_eq_sum_assoc
         || rewrite gnl_eq_prod_assoc
         || rewrite gnl_theo_eq_prod_zero_e
         || rewrite gnl_theo_eq_prod_e_zero
         || rewrite gnl_eq_sum_prod
         || rewrite gnl_eq_prod_sum  ;
         repeat apply gnl_theo_inf_join;auto with proofs;
         try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l).
     - destruct H;simpl;auto with proofs;destruct (ewp e);eauto with proofs.
     Qed.
  
  Lemma mReg_to_mRegs_and_back1 e :
    gnl_theo_inf mKA (mRegs_to_mReg (mReg_to_mRegs e)) e.
  Proof.
    induction e as [|[|] | | |];simpl;try rewrite IHe||rewrite IHe1,IHe2;
     try (now auto with proofs).
    repeat apply gnl_theo_inf_join;auto with proofs.
    - pose proof (ewp_alt_spec e1) as (he1&_).
      destruct (ewp e1);simpl;try rewrite IHe2;auto with proofs.
      rewrite <- he1 by reflexivity.
      auto with proofs.
    - pose proof (ewp_alt_spec e2) as (he2&_).
      destruct (ewp e2);simpl;try rewrite IHe1;auto with proofs.
      rewrite <- he2 by reflexivity.
      auto with proofs.
  Qed.
  
  Lemma ewp_exp_inf e :
    gnl_theo_inf mKA (if ewp e then 1_m else zero) e.
  Proof.
    pose proof (ewp_alt_spec e) as (he&_).
    destruct (ewp e);simpl;auto with proofs.
  Qed.

  Lemma mReg_to_mRegs_and_back2 e :
    gnl_theo_inf mKA e (sum (if ewp e then 1_m else zero) (mRegs_to_mReg (mReg_to_mRegs e))).
  Proof.
    induction e as [|[|] | | |];simpl;try rewrite IHe at 1||rewrite IHe1,IHe2 at 1;
     try (now auto with proofs).
    - generalize dependent (mRegs_to_mReg (mReg_to_mRegs e1));
        generalize dependent (mRegs_to_mReg (mReg_to_mRegs e2)).
      intros E2 h2 E1 h1.
      destruct (ewp e1),(ewp e2);simpl;auto with proofs.
    - destruct (ewp e1),(ewp e2);simpl;
         repeat rewrite gnl_eq_sum_assoc
         || rewrite gnl_eq_prod_assoc
         || rewrite gnl_theo_eq_prod_one_e
         || rewrite gnl_theo_eq_prod_e_one
         || rewrite gnl_theo_eq_prod_zero_e
         || rewrite gnl_theo_eq_prod_e_zero
         || rewrite gnl_eq_sum_prod
         || rewrite gnl_eq_prod_sum;
         repeat apply gnl_theo_inf_join;auto with proofs;
         try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l).
    - destruct (ewp e);simpl;
         repeat rewrite gnl_eq_sum_assoc
         || rewrite gnl_eq_prod_assoc
         || rewrite gnl_theo_eq_prod_one_e
         || rewrite gnl_theo_eq_prod_e_one
         || rewrite gnl_theo_eq_sum_zero_e
         || rewrite gnl_theo_eq_sum_e_zero
         || rewrite gnl_theo_eq_prod_zero_e
         || rewrite gnl_theo_eq_prod_e_zero
         || rewrite gnl_eq_sum_prod
         || rewrite gnl_eq_prod_sum;
         repeat apply gnl_theo_inf_join;auto with proofs;
         try (now repeat reflexivity||apply gnl_theo_inf_join_r||rewrite <- gnl_theo_inf_join_l).
      clear IHe.
      generalize dependent (mRegs_to_mReg (mReg_to_mRegs e)).
      clear e;intros e.
      apply gnl_theo_inf_iter_left_ind_bis.
      repeat rewrite gnl_eq_sum_prod
             || rewrite gnl_eq_prod_sum
             || rewrite gnl_theo_eq_prod_one_e
             || rewrite gnl_theo_eq_prod_e_one.
      repeat apply gnl_theo_inf_join;auto with proofs.
      + rewrite <- gnl_theo_inf_join_r.
        rewrite <- gnl_theo_inf_iter_unfold_left;auto with proofs.
      + rewrite <- gnl_theo_inf_join_r.
        rewrite <- gnl_theo_inf_iter_unfold_left;auto with proofs.
      + rewrite <- gnl_theo_inf_join_r.
        rewrite <- gnl_theo_inf_iter_unfold_left at 2;auto with proofs.
  Qed.

  Theorem mReg_to_mRegs_and_back e :
    gnl_theo_eq mKA e (sum (if ewp e then 1_m else zero) (mRegs_to_mReg (mReg_to_mRegs e))).
  Proof.
    split.
    - apply mReg_to_mRegs_and_back2.
    - apply gnl_theo_inf_join.
      + apply ewp_exp_inf.
      + apply mReg_to_mRegs_and_back1.
  Qed.

  Lemma mRegs_to_mReg_sem s e :
    gnl_theo_sat mkas s e <-> in_mlang (mSPs_to_mSP s) (mRegs_to_mReg e).
  Proof.
    revert s;induction e;simpl;tauto||intro s.
    - replace (mSPs_to_mSP s) with (mSPs_opt_to_mSP (Some s)) by reflexivity.
      split;intro E.
      + cut (or_none (gnl_term_theo_eq mkas) (Some s) (Some (t_var x)));[|apply E].
        intro E';apply mSPs_opt_to_mSP_proper in E';rewrite E';simpl;reflexivity.
      + apply mSP_to_mSPs_opt_proper in E.
        rewrite mSPs_opt_to_mSP_and_back in E.
        apply E.
    - rewrite IHe1,IHe2;tauto.
    - setoid_rewrite IHe1;setoid_rewrite IHe2;clear IHe1 IHe2.
      split;intros (s1&s2&h1&h2&h3).
      + exists (mSPs_to_mSP s1),(mSPs_to_mSP s2);repeat split;auto with proofs.
        replace (mSPs_to_mSP s) with (mSPs_opt_to_mSP (Some s)) by reflexivity.
        cut (or_none (gnl_term_theo_eq mkas) (Some s) (Some (t_prod o s1 s2)));[|apply h1].
        intro E';apply mSPs_opt_to_mSP_proper in E';rewrite E';simpl;reflexivity.
      + apply mSP_to_mSPs_opt_proper in h1.
        replace (mSPs_to_mSP s) with (mSPs_opt_to_mSP (Some s)) in h1 by reflexivity.
        rewrite mSPs_opt_to_mSP_and_back in h1.
        simpl in h1.
        pose proof (is_one_spec s1) as (hs1&_).
        pose proof (is_one_spec s2) as (hs2&_).
        unfold is_one in *.
        pose proof (mSP_to_mSPs_and_back s1) as es1.
        pose proof (mSP_to_mSPs_and_back s2) as es2.
        destruct (mSP_to_mSPs_opt s1),(mSP_to_mSPs_opt s2);simpl in *;try tauto.
        * exists m, m0;repeat split;auto.
          -- rewrite es1;assumption.
          -- rewrite es2;assumption.
        * exfalso.
          rewrite <- es2 in h3.
          apply ewp_spec in h3.
          rewrite ewp_mRegs_to_mReg in h3;discriminate. 
        * exfalso.
          rewrite <- es1 in h2.
          apply ewp_spec in h2.
          rewrite ewp_mRegs_to_mReg in h2;discriminate. 
    - split;intros (s'&L&h1&h2&h3);revert s s' h1 h2 h3;(induction L;[discriminate|]);simpl;
        (destruct (L =?= []);[clear IHL;subst;simpl;intros ? ? E;inversion E;subst;clear E
                                |pose proof n as hL;apply (GProd_Some _ o) in hL as (tL&etL)]);
        intros.
      + exists (mSPs_to_mSP s'),[mSPs_to_mSP s'];repeat split;auto with proofs.
        * replace (mSPs_to_mSP s) with (mSPs_opt_to_mSP (Some s)) by reflexivity. 
          replace (mSPs_to_mSP s') with (mSPs_opt_to_mSP (Some s')) by reflexivity. 
          apply mSPs_opt_to_mSP_proper,h2.
        * intros ? [<-|F];[|exfalso];auto.
          apply IHe,h3; now left.
      + rewrite etL in h1;inversion h1;subst;clear h1.
        destruct (IHL tL tL) as (t'&L'&ih1&ih2&ih3);auto with proofs.
        exists (t_prod o (mSPs_opt_to_mSP (Some a)) t'),(mSPs_to_mSP a::L').
        repeat split;auto with proofs.
        * simpl;rewrite ih1;reflexivity.
        * rewrite <- ih2.
          replace (mSPs_to_mSP s) with (mSPs_opt_to_mSP (Some s)) by reflexivity. 
          replace (t_prod o (mSPs_opt_to_mSP (Some a)) (mSPs_to_mSP tL))
            with (mSPs_opt_to_mSP (Some (t_prod o a tL))) by reflexivity. 
          apply mSPs_opt_to_mSP_proper,h2.
        * intros ? [<-|h];[apply IHe,h3;left|apply ih3];auto.
      + exists s,[s];repeat split;auto with proofs.
        intros ? [<-|F];[|exfalso;auto].
        apply IHe;rewrite h2;apply h3;tauto.
      + rewrite etL in h1;inversion h1;subst;clear h1.
        case_eq (mSP_to_mSPs_opt tL).
        * intros g hg.
          destruct (IHL g tL) as (t'&L'&ih1&ih2&ih3);auto with proofs;
            [replace (mSPs_to_mSP g) with (mSPs_opt_to_mSP (Some g)) by reflexivity;
             rewrite <- hg;apply mSP_to_mSPs_and_back|].
          case_eq (mSP_to_mSPs_opt a).
          -- intros g' hg'.
             assert (h4: gnl_term_theo_eq mka a (mSPs_to_mSP g'))
               by (rewrite <- mSP_to_mSPs_and_back;rewrite hg';simpl;reflexivity).
             exists (t_prod o g' t'),(g'::L');simpl;rewrite ih1;repeat split;auto with proofs.
             ++ cut (or_none (gnl_term_theo_eq mkas) (Some s) (Some (t_prod o g' t')));
                  [intros h;apply h|].
                rewrite <- mSPs_opt_to_mSP_and_back.
                rewrite <- mSPs_opt_to_mSP_and_back at 1.
                apply mSP_to_mSPs_opt_proper.
                simpl.
                rewrite h2;apply gnlt_prod;auto.
                rewrite <- mSP_to_mSPs_and_back.
                rewrite hg;simpl.
                replace (mSPs_to_mSP g) with (mSPs_opt_to_mSP (Some g)) by reflexivity. 
                replace (mSPs_to_mSP t') with (mSPs_opt_to_mSP (Some t')) by reflexivity. 
                apply mSPs_opt_to_mSP_proper;simpl;assumption.
             ++ intros ? [<-|h];[|apply ih3];auto.
                apply IHe;rewrite <- h4.
                apply h3;now left.
          -- intros E.
             exists t',L';repeat split;auto.
             apply mSP_to_mSPs_opt_proper in h2;simpl in h2.
             rewrite E in h2;simpl in h2.
             replace (mSPs_to_mSP s) with (mSPs_opt_to_mSP (Some s)) in h2 by reflexivity. 
             rewrite mSPs_opt_to_mSP_and_back in h2;simpl in h2.
             rewrite hg in h2.
             rewrite h2,ih2;reflexivity.
        * intros E.
          apply mSP_to_mSPs_opt_proper in h2;simpl in h2.
          rewrite E in h2;simpl in h2.
          replace (mSPs_to_mSP s) with (mSPs_opt_to_mSP (Some s)) in h2 by reflexivity. 
          rewrite mSPs_opt_to_mSP_and_back in h2;simpl in h2.
          case_eq (mSP_to_mSPs_opt a).
          -- intros g' hg'.
             rewrite hg' in h2;simpl in h2.
             exists g',[g'];repeat split;auto.
             intros ? [<-|F];[|exfalso];auto.
             apply IHe.
             replace (mSPs_to_mSP g') with (mSPs_opt_to_mSP (Some g')) by reflexivity. 
             rewrite <- hg',mSP_to_mSPs_and_back.
             apply h3;now left.
          -- intro F;exfalso.
             rewrite F in h2;tauto.
  Qed.

  Lemma mReg_to_mRegs_sem s e :
    gnl_theo_sat mka s e <->
      ((mSP_to_mSPs_opt s) = None /\ ewp e = true)
      \/ exists d, (mSP_to_mSPs_opt s) = Some d /\ gnl_theo_sat mkas d (mReg_to_mRegs e).
  Proof.
    split.
    - case_eq (mSP_to_mSPs_opt s).
      + intros s' Es' hL;right;exists s';split;auto.
        pose proof (mSP_to_mSPs_and_back s) as E.
        rewrite Es' in E;simpl in E.
        rewrite <- E in hL.
        apply mRegs_to_mReg_sem.
        rewrite mReg_to_mRegs_and_back in hL.
        destruct hL as [hL|hL].
        * exfalso;destruct (ewp e);simpl in *;[|apply hL].
          replace (mSPs_to_mSP s') with (mSPs_opt_to_mSP (Some s')) in hL by reflexivity.
          rewrite <- Es' in hL.
          rewrite mSP_to_mSPs_and_back in hL.
          symmetry in hL;apply is_one_spec in hL.
          unfold is_one in hL;rewrite Es' in hL;discriminate.
        * assumption.
      + intros h1 h2.
        left;split;auto.
        apply ewp_spec.
        pose proof (is_one_spec s) as (h3&_).
        unfold is_one in h3;rewrite h1 in h3.
        rewrite h3 by reflexivity.
        assumption.
    - intros [(E&h)|(d&E&h)].
      + pose proof (is_one_spec s) as (h3&_).
        unfold is_one in h3;rewrite E in h3.
        rewrite <- h3 by reflexivity.
        apply ewp_spec,h.
      + apply mRegs_to_mReg_sem in h.
        rewrite (mReg_to_mRegs_and_back e).
        right.
        pose proof (mSP_to_mSPs_and_back s) as E'.
        rewrite E in E';simpl in E';rewrite <- E'.
        assumption.
  Qed.

End mKA.
Arguments mReg : clear implicits.
Arguments mSP : clear implicits.
