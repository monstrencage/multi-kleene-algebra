(** * gnl_alg.gnl_decomp : decomposition of expressions *)
Require Import prelim.
Require Import gnl theories depth.

Section gnl_decomp.
  (** * Definition of the projections and decompositions *)
  
  (** We fix a decidable set of variables and a decidable set of operators. *)

  Context {A : Set} {decA : decidable_set A}.
  Context {O : Set} {decO : decidable_set O}.

  (** A decomposition of a general term is either a variable or a pair of a *)
  (** topmost operator with a list of general terms. *)
  
  Definition gnl_decomposition : Set := A + O * list (GTerm A O).

  (** We define _valid_ decompositions, which will be the ones we will be interested in. *)
  (** Variables are valid, and a pair [o,l] is valid provided that: *)
  (** - [l] contains at least two elements; and *)
  (** - no term [t] in [l] has topmost operator [o] (they are either variables or terms with a different topmost operator). *)
  
  Definition gnl_valid_elt (o : O) (t : GTerm A O) : bool :=
    match t with
    | t_var _ => true
    | t_prod o' t1 t2 => if (o =?= o') then false else true
    end.

  Definition gnl_valid (t : gnl_decomposition) : bool :=
    match t with
    | inl _ => true
    | inr (o,l) => Nat.ltb 1 (length l) && forallb (gnl_valid_elt o) l
    end.

  (** We will consider decomposition up-to the following equivalence relation, *)
  (** parametered by a term theory [r]: *)
  
  Definition gnl_decomp_eq r : relation gnl_decomposition :=
    fun d1 d2 =>
      match d1,d2 with
      | inl a,inl b => a = b
      | inr (o,l),inr (o',m) => o = o' /\ list_lift (gnl_term_theo_eq r) l m
      | _,_ => False
      end.

  (** The following pair of functions describes how general terms can be decomposed. *)
  
  Fixpoint gnl_term_to_list (o : O) (s : GTerm A O) : list (GTerm A O) :=
    match s with
    | t_var a => [t_var a]
    | s -[i]- t => if i =?= o
                   then (gnl_term_to_list o s)++(gnl_term_to_list o t)
                   else [s -[i]- t]
    end.

  Definition gnl_decompose  (t : GTerm A O) : gnl_decomposition :=
    match t with
    | t_var a => inl a
    | t_prod o t1 t2 => inr (o,gnl_term_to_list o (t_prod o t1 t2))
    end.

  (** From a decomposition, one can build back a general term (provided the *)
  (** decomposition is valid). *)
  
  Definition gnl_recompose : gnl_decomposition -> option (GTerm A O) :=
    fun s =>
      match s with
      | inl a => Some (t_var a)
      | inr (o,l) => GProd o l
      end.

  (** [gnl_slat_proj e] extracts a [slat] expression that characterises the variables satisfying *)
  (** the expression [e]. *)
    
  Fixpoint gnl_slat_proj (e : GExp A O) : slat A :=
    match e with
    | ø => ø
    | var a => var a
    | e + f => gnl_slat_proj e + gnl_slat_proj f
    | e ×{i} f => ø
    | e^{i} => gnl_slat_proj e
    end.

  (** [gnl_reg_trad o e] extracts the maximal top subexpression of [e] that only uses *)
  (** the operator [o], and puts the other subexpressions inside variables. The result *)
  (** is a regular expression over the set of variables [GExp A O]. *)
  
  Fixpoint gnl_reg_trad (o : O) (e : GExp A O) : Reg (GExp A O) :=
    match e with
    | ø => ø
    | var a => var_r (var a)
    | e + f => gnl_reg_trad o e + gnl_reg_trad o f
    | e ×{i} f =>
        if i =?= o then gnl_reg_trad o e @@ gnl_reg_trad o f else var_r (e ×{i} f)
    | e^{i} => 
        if i =?= o
        then (gnl_reg_trad o e)^+
        else gnl_reg_trad o e + var_r (e ×{i} e^{i})
    end.

  (** [gnl_reg_proj o e] is similar, except that it _kills_ (sets to [ø]) parts of the *)
  (** expression that do not have operator [o] as the topmost operator. *)

  Fixpoint gnl_reg_proj (o : O) (e : GExp A O) : Reg (GExp A O) :=
    match e with
    | ø => ø
    | var a => ø
    | e + f => gnl_reg_proj o e + gnl_reg_proj o f
    | e ×{i} f =>
        if i =?= o then gnl_reg_trad o e @@ gnl_reg_trad o f else ø
    | e^{i} => 
        if i =?= o
        then gnl_reg_proj o e + (gnl_reg_trad o e @@ (gnl_reg_trad o e)^+ )
        else (gnl_reg_proj o e)
    end.

  (** Now that we have decompositions and projections, we can define a new satisfaction relation, *)
  (** relating decompositions with the expression's projections. *)
  
  Definition gnl_decomp_sat r (s : gnl_decomposition) (e : GExp A O) :=
    match s with
    | inl a => a |=slat= gnl_slat_proj e
    | inr (o,l) => exists m, list_lift (gnl_theo_sat r) l (Word_to_list m)
                             /\ m |=(ka)= (gnl_reg_proj o e)
    end.
  
  (** * Facts about the decomposition *)

  (** ** Stability of validity *)
  Global Instance gnl_valid_elt_proper rT o :
    Proper (rT ==> eq) (gnl_valid_elt o) ->
    Proper (gnl_term_theo_eq rT ==> eq) (gnl_valid_elt o).
  Proof. intros hrT s t pr;induction pr;eauto. Qed.
  Global Instance Ø_valid_elt_proper o :
    Proper (Ø ==> eq) (gnl_valid_elt o).
  Proof. intros s t []. Qed.

  Global Instance gnl_valid_proper rT :
    (forall o, Proper (rT ==> eq) (gnl_valid_elt o)) ->
    Proper (gnl_decomp_eq rT ==> eq) gnl_valid.
  Proof.
    intros hrT [|(o&l)] [|(o'&m)] h;simpl in h;try tauto.
    destruct h as (->&h);simpl.
    apply Bool.eq_iff_eq_true.
    repeat rewrite Bool.andb_true_iff,PeanoNat.Nat.ltb_lt,forallb_forall.
    rewrite (list_lift_length _ l m h).
    cut
      ((forall x : GTerm A O, In x l -> gnl_valid_elt o' x = true) <->
         forall x : GTerm A O, In x m -> gnl_valid_elt o' x = true);
      [intros ->;reflexivity|].
    repeat rewrite <- Forall_forall.
    revert m h;induction l;intros [] h;try (exfalso;apply h).
    - simpl;tauto.
    - repeat rewrite Forall_cons_iff.
      destruct h as (h1&h2).
      rewrite h1.
      apply IHl in h2 as ->.
      reflexivity.
  Qed.

  (** ** General properties of decompostions *)
  (** As expected, our relation on decompositions is an equivalence relation. *)
  
  Global Instance gnl_decomp_eq_Equivalence r : Equivalence (gnl_decomp_eq r).
  Proof.
    split.
    - intros [|[]];simpl;repeat split;reflexivity.
    - intros [|[]] [|[]] h;try (exfalso;apply h);simpl in *;repeat destruct h as (?&h);
        repeat split;symmetry;auto.
    - intros [|[]] [|[]] [|[]] h1 h2;try (exfalso;apply h1||apply h2);simpl in *;
        repeat destruct h1 as (?&h1)||destruct h2 as (?&h2);
        repeat split;auto;etransitivity;eassumption.
  Qed.

  
  (** [gnl_term_to_list] always return a non-empty list. *)
  Lemma gnl_term_to_list_not_nil o (s : GTerm A O) :
    gnl_term_to_list o s <> [].
  Proof.
    induction s;try discriminate.
    simpl;destruct (o0 =?= o);[|discriminate].
    intro h;apply app_eq_nil in h as (h1&h2).
    tauto.
  Qed.

  (** [gnl_term_to_list o s] return a list of terms that are valid according to [gnl_valid_elt o]. *)
  
  Lemma gnl_term_to_list_valid_elt o x s :
    In x (gnl_term_to_list o s) -> gnl_valid_elt o x = true.
  Proof.
    induction s;simpl.
    - intros [<-|F];[ |tauto];reflexivity.
    -  destruct (o0 =?= o);simpl;
         try setoid_rewrite in_app_iff;intros h;repeat (destruct h as [h|h];subst);simpl;try tauto.
       rewrite eq_dec_neq by (intros ->;tauto).
       reflexivity.
  Qed.
    
  (** With the two previous lemmas, we can show that our decomposition function *)
  (** only returns valid decompositions. *)
  
  Lemma gnl_decompose_valid  (t : GTerm A O) :
    gnl_valid (gnl_decompose t) = true.
  Proof.
    destruct t as [x|o t1 t2];simpl;auto.
    rewrite eq_dec_eq.
    simpl;apply Bool.andb_true_iff.
    rewrite <- (Bool.reflect_iff _ _ (PeanoNat.Nat.ltb_spec0 _ _)).
    rewrite forallb_forall.
    split.
    - rewrite length_app.
      pose proof (gnl_term_to_list_not_nil o t1) as h1;
        pose proof (gnl_term_to_list_not_nil o t2) as h2.
      destruct (gnl_term_to_list o t1),(gnl_term_to_list o t2);try tauto.
      simpl;lia.
    - intro;rewrite in_app_iff;intros [h|h];eapply gnl_term_to_list_valid_elt,h.
  Qed.

  (** A useful observation: [gnl_decompose] and [gnl_term_to_list] enjoy the *)
  (** following correspondance: *)
  
  Lemma gnl_decompose_gnl_term_to_list (s : GTerm A O) :
    forall o l, gnl_decompose s = inr (o,l) -> gnl_term_to_list o s = l.
  Proof.
    intros o l;destruct s;simpl;try discriminate.
    rewrite eq_dec_eq.
    intro E;inversion E;subst.
    rewrite eq_dec_eq.
    reflexivity.
  Qed.

  (** The following will be useful in case analyses: if a pair of term is equivalent *)
  (** according to the empty theory, either both are the same variable, or they can be *)
  (** decomposed as pairs of a shared operator [o] and elementwise equivalent lists. *)
  
  Lemma gnl_decompose_eq :
    forall s t : GTerm A O,
      Ø |- s =T= t -> (exists a, s = t_var a /\ t = t_var a)
                         \/ exists o l m, gnl_decompose s = inr (o,l)
                                          /\ gnl_decompose t = inr (o,m)
                                          /\ list_lift (gnl_term_theo_eq Ø) l m.
  Proof.
    intros s t pr;induction pr;simpl.
    - destruct e;simpl;auto.
      + left;exists a;split;reflexivity.
      + right;rewrite eq_dec_eq.
        exists o,(gnl_term_to_list o e1 ++ gnl_term_to_list o e2),
          (gnl_term_to_list o e1 ++ gnl_term_to_list o e2).
        repeat split;reflexivity.
    - firstorder.
      right;exists x,x1,x0;repeat split;auto.
      symmetry;assumption.
    - destruct IHpr1 as [(a1&->&->)|(o1&le&lf1&he&hf1&hef)],
         IHpr2 as [(a2&E&->)|(o2&lf2&lg&hf2&hg&hfg)].
     + inversion E;subst; left;exists a2;tauto.
     + discriminate.
     + subst;discriminate.
     + rewrite hf1 in hf2;inversion hf2;subst;clear hf2.
       right;exists o2,le,lg;repeat split;auto.
       transitivity lf2;auto.
    - repeat rewrite eq_dec_eq;right.
      exists o;eexists;eexists;repeat split;try reflexivity.
      apply app_list_lift.
      + destruct IHpr1 as [(a1&->&->)|(o1&le1&le2&he1&he2&he)];simpl;auto.
        destruct (o =?= o1).
        * subst.
          rewrite (gnl_decompose_gnl_term_to_list _ _ _ he1).
          rewrite (gnl_decompose_gnl_term_to_list _ _ _ he2).
          auto.
        * destruct e1;simpl;inversion he1;subst.
          rewrite eq_dec_eq in *;rewrite eq_dec_neq by (intros ->;tauto).
          destruct e2;simpl;inversion he2;subst.
          rewrite eq_dec_eq in *;rewrite eq_dec_neq by (intros ->;tauto).
          split;auto.
      + destruct IHpr2 as [(a2&->&->)|(o2&lf1&lf2&hf1&hf2&hf)];simpl;auto.
        destruct (o =?= o2).
        * subst.
          rewrite (gnl_decompose_gnl_term_to_list _ _ _ hf1).
          rewrite (gnl_decompose_gnl_term_to_list _ _ _ hf2).
          auto.
        * destruct f1;simpl;inversion hf1;subst.
          rewrite eq_dec_eq in *;rewrite eq_dec_neq by (intros ->;tauto).
          destruct f2;simpl;inversion hf2;subst.
          rewrite eq_dec_eq in *;rewrite eq_dec_neq by (intros ->;tauto).
          split;auto.
    - repeat rewrite eq_dec_eq.
      rewrite <- app_assoc.
      right;exists o.
      eexists;eexists;repeat (split;[reflexivity|]).
      reflexivity.
    - inversion H.
  Qed.

  (** [gnl_term_to_list] is a morphism from terms up-to the empty theory to lists up-to *)
  (** elementwise equivalence. *)
  
  Global Instance gnl_term_to_list_proper (o : O) :
    Proper (gnl_term_theo_eq Ø ==> list_lift (gnl_term_theo_eq Ø)) (gnl_term_to_list o).
  Proof.
    intros e f pr;induction pr.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - simpl;destruct (o0 =?= o);[apply app_list_lift|split;[|reflexivity]];auto with proofs.
    - simpl;destruct (o0 =?= o);[rewrite <- app_assoc|rewrite gnlt_prod_assoc];reflexivity.
    - inversion H.
  Qed.

  (** For the next result, we need the following auxiliary result: if [gnl_term_to_list o t] is *)
  (** elementwise equivalent to a concatenation [l++m], then we can build terms [s1] and [s2] *)
  (** such that [t] is equivalent to the product [s1-[o]-s2] and [s1] corresponds to [l] and *)
  (** [s2] corresponds to [m]. *)

  Lemma gnl_term_eq_app (t : GTerm A O) o l m :
    l<> [] -> m <> [] ->
    list_lift (gnl_term_theo_eq Ø) (l++m) (gnl_term_to_list o t) ->
    exists s1 s2,
      list_lift (gnl_term_theo_eq Ø) (gnl_term_to_list o s1) l 
      /\ list_lift (gnl_term_theo_eq Ø) (gnl_term_to_list o s2) m
      /\ Ø |- s1 -[o]- s2 =T= t.
  Proof.
    revert l m.
    induction t;intros l m hl hm;simpl.
    - intro E;exfalso.
      case_eq (l++m);[intros h;rewrite h in E;simpl in E;tauto|].
      intros e' [|e'' k] h;[|rewrite h in E;simpl in E;tauto].
      destruct l;[tauto|].
      inversion h.
      apply app_eq_nil in H1 as (_&F);tauto.
    - destruct (o0 =?= o);subst.
      + intros E.
        apply list_lift_app in E as (m1&m2&E&hm1&hm2).
        apply Levi in E as [(m'&->&->)|(m'&->&->)].
        * case_eq m'.
          -- intros ->.
             rewrite app_nil_r in *.
             simpl in *.
             exists t1,t2.
             repeat split;symmetry;reflexivity||assumption.
          -- intros e'' m'' Em;apply IHt2 in hm2 as (s1&s2&hs1&hs2&h);
               [|subst;discriminate|assumption].
             exists (t_prod o t1 s1),s2;repeat split;auto.
             ++ simpl;rewrite eq_dec_eq.
                rewrite <- hm1,hs1,Em.
                reflexivity.
             ++ rewrite <- gnlt_prod_assoc;apply gnlt_prod;assumption||reflexivity.
        * case_eq m'.
          -- intros ->.
             rewrite app_nil_r in *.
             simpl in *.
             exists t1,t2.
             repeat split;symmetry;reflexivity||assumption.
          -- intros e'' m'' Em;apply IHt1 in hm1 as (s1&s2&hs1&hs2&h);
               [|assumption|subst;discriminate].
             exists s1,(t_prod o s2 t2);repeat split;auto.
             ++ simpl;rewrite eq_dec_eq.
                rewrite <- hm2,hs2,Em.
                reflexivity.
             ++ rewrite gnlt_prod_assoc;apply gnlt_prod;assumption||reflexivity.
      + intro f;exfalso.
         case_eq (l++m);[intros h;rewrite h in f;simpl in f;tauto|].
         intros e' [|e'' k] h;[|rewrite h in f;simpl in f;tauto].
         destruct l;[tauto|].
         inversion h.
         apply app_eq_nil in H1 as (_&F);tauto.
  Qed.

  (** With this we can show that [gnl_term_to_list] enjoys a form of injectivity: *)
  
  Lemma gnl_term_to_list_gnl_term_eq (s t : GTerm A O) o :
    list_lift (gnl_term_theo_eq Ø) (gnl_term_to_list o s) (gnl_term_to_list o t) ->
    Ø |- s =T= t.
  Proof.
    revert t;induction s;intros t;simpl.
    - destruct t;simpl;try tauto.
      destruct (o0 =?= o);try tauto.
      case_eq (gnl_term_to_list o t1 ++ gnl_term_to_list o t2);[tauto|].
      intros e' [|];try tauto.
      case_eq (gnl_term_to_list o t1);[intro F;apply gnl_term_to_list_not_nil in F;tauto|].
      intros e'' l _ F.
      inversion F;simpl in *;subst;clear F.
      apply app_eq_nil in H1 as (_&F).
      apply gnl_term_to_list_not_nil in F;tauto.
    - destruct (o0 =?= o);subst.
      + intro h.
        apply gnl_term_eq_app in h as (t1 &t2 &h1&h2&E);try apply gnl_term_to_list_not_nil.
        rewrite <- E.
        apply gnlt_prod;[apply IHs1|apply IHs2];symmetry;assumption.
      + destruct t.
        * simpl;intros (f&_);exfalso.
          apply get_var_eq in f;discriminate.
        * simpl;destruct (o1 =?= o);[|tauto].
          case_eq (gnl_term_to_list o t1 ++ gnl_term_to_list o t2);[tauto|].
          intros g [];simpl;try tauto.
          subst.
          intro f;exfalso.
          case_eq (gnl_term_to_list o t1);[apply gnl_term_to_list_not_nil|].
          intros e' l E;rewrite E in f.
          inversion f;subst;clear f.
          apply app_eq_nil in H1 as (_&f).
          eapply gnl_term_to_list_not_nil,f.
  Qed.

  (** Valid decompostion recompose to actual terms (no [None] value). *)
  
  Lemma gnl_recompose_Some d : gnl_valid d = true -> exists t, gnl_recompose d = Some t.
  Proof.
    destruct d as [a|(o,l)];simpl.
    - intros _;eexists;reflexivity.
    - intros h;apply GProd_Some.
      apply Bool.andb_true_iff in h as (h&_).
      apply PeanoNat.Nat.ltb_lt in h.
      intros ->;simpl in h;lia.
  Qed.

  (** For terms that are valid according to [gnl_valid_elt o], [gnl_term_to_list o] just returns *)
  (** the singleton list containing the term itself. *)
  Lemma gnl_valid_elt_to_list_sngl o a :
    gnl_valid_elt o a = true -> gnl_term_to_list o a = [a].
  Proof.
    destruct a as [|o'];simpl;[|destruct (o' =?= o);[subst;rewrite eq_dec_eq
                                                    |rewrite eq_dec_neq by (intros ->;tauto)]];
      discriminate||reflexivity.
  Qed.

  (** Since [gnl_term_to_list] dose not return the empty list, the [GProd] of its output is *)
  (** well defined. *)
  
  Lemma GProd_gnl_term_to_list_Some (s : GTerm A O) o :
    exists t, GProd o (gnl_term_to_list o s) = Some t.
  Proof. apply GProd_Some,gnl_term_to_list_not_nil. Qed.

  (** Furthermore, that output is equivalent to the original term. *)
  
  Lemma GProd_gnl_term_to_list_eq (s t : GTerm A O) o :
    GProd o (gnl_term_to_list o s) = Some t -> Ø |- s =T= t.
  Proof.
    revert t;induction s as [|o'];simpl;intros s E.
    - inversion E;reflexivity.
    - destruct (o' =?= o).
      + destruct (GProd_gnl_term_to_list_Some s1 o) as (s'1&Es1).
        destruct (GProd_gnl_term_to_list_Some s2 o) as (s'2&Es2).
        destruct (GProd_app Ø _ _ _ _ _ Es1 Es2) as (s'&E'&Es).
        rewrite E in E';symmetry in E';inversion E';subst;clear E'.
        rewrite Es.
        rewrite IHs1,IHs2 by eassumption.
        reflexivity.
      + inversion E;reflexivity.
  Qed.

  (** ** From terms to decompositions and back *)

  (** [gnl_recompose] is a morphism w.r.t. any theory [rT] . *)

  Global Instance gnl_recompose_proper rT :
    Proper (gnl_decomp_eq rT ==> or_none (gnl_term_theo_eq rT)) gnl_recompose.
  Proof.
    intros [a|(o,l)] [b|(o',m)];simpl;try tauto.
    - intros ->;reflexivity.
    - intros (<-&h).
      rewrite h;reflexivity.
  Qed.

  (** The same does not hold for [gnl_decompose] with arbitrary theories, but it is true *)
  (** in the case of the empty theory. *)
  
  Global Instance gnl_decompose_proper :
    Proper (gnl_term_theo_eq Ø ==> gnl_decomp_eq Ø) gnl_decompose.
  Proof.
    intros ? ? h.
    destruct (gnl_decompose_eq _ _ h) as [(a&->&->)|(o&l&m&->&->&hlm)];[reflexivity|].
    simpl;split;auto.
  Qed.

  (** We can show that valid decompositions recompose to terms that decompose back into them. *)
  
  Lemma decompose_recompose (s : gnl_decomposition) t :
    gnl_valid s = true -> gnl_recompose s = Some t -> gnl_decompose t = s.
  Proof.
    destruct s as [a|(o,l)];simpl.
    - intros _ E;inversion E;subst;clear E.
      reflexivity.
    - rewrite Bool.andb_true_iff,PeanoNat.Nat.ltb_lt,forallb_forall.
      intros (hlen&hl) E.
      revert t E;induction l;[subst;simpl in *;discriminate|intros t E].
      destruct (l =?= []);simpl in E;[subst;clear IHl;simpl in hlen;lia
                                     |apply (GProd_Some _ o) in n as (s&hs);rewrite hs in E];
        inversion E;subst;clear E.
      + clear hlen.
        assert (ha: In a (a::l)) by (now left);apply hl in ha;simpl.
        rewrite eq_dec_eq,(gnl_valid_elt_to_list_sngl _ _ ha);simpl;repeat f_equal.
        destruct (PeanoNat.Nat.lt_ge_cases 1 (length l)) as [len|len].
        * apply IHl in hs;[| |intros;apply hl;simpl];auto.
          destruct s as [|o'];inversion hs;subst;simpl;repeat rewrite eq_dec_eq in *.
          reflexivity.
        * destruct l as [|? [|]];[discriminate|inversion hs;subst;clear hs|simpl in len;lia].
          apply gnl_valid_elt_to_list_sngl,hl;now right;left.
  Qed.

  (** We also show that recomposing the decomposition of a term yields a (possibly different *)
  (** but) equivalent term. *)
  
  Lemma recompose_decompose (s : GTerm A O) :
    exists t, gnl_recompose (gnl_decompose s) = Some t /\ Ø |- s =T= t.
  Proof.
    destruct s;simpl.
    - eexists;split;reflexivity.
    - rewrite eq_dec_eq.
      revert s2;induction s1 as [|o'];intros s2.
      + simpl.
        destruct (GProd_gnl_term_to_list_Some s2 o) as (s&Es).
        rewrite Es.
        eexists;split;[reflexivity|].
        apply gnlt_prod;[reflexivity|].
        eapply GProd_gnl_term_to_list_eq;eassumption.
      + simpl;destruct (o' =?= o).
        * subst.
          rewrite <- app_assoc.
          replace (_ o s1_2 ++ _) with (gnl_term_to_list o (t_prod o s1_2 s2))
            by now (simpl;rewrite eq_dec_eq).
          setoid_rewrite <- gnlt_prod_assoc.
          apply IHs1_1.
        * simpl.
          destruct (GProd_gnl_term_to_list_Some s2 o) as (s'2&Es'2).
          rewrite Es'2.
          eexists;split;[reflexivity|].
          apply  GProd_gnl_term_to_list_eq in Es'2 as ->.
          reflexivity.
  Qed.

  (** * Facts about the projections *)

  (** Both [gnl_reg_trad] and [gnl_reg_proj] produce regular expression that do not *)
  (** enjoy the empty word property. *)
  
  Lemma ewp_gnl_reg_trad (o : O) (e : GExp A O) :
    ewp_r (gnl_reg_trad o e) = false.
  Proof.
    induction e as [| | |i|i];simpl;try destruct (i =?= o);
      unfold ewp_r in *;simpl in *;try rewrite IHe1,IHe2||rewrite IHe;auto with proofs.
  Qed.

  Lemma ewp_gnl_reg_proj (o : O) (e : GExp A O) :
    ewp_r (gnl_reg_proj o e) = false.
  Proof.
    induction e as [| | |i|i];simpl;try destruct (i =?= o);
      unfold ewp_r in *;simpl in *;try rewrite IHe1,IHe2||rewrite IHe;auto with proofs.
    - pose proof (ewp_gnl_reg_trad o e1) as E1;
        pose proof (ewp_gnl_reg_trad o e2) as E2;
        unfold ewp_r in *;rewrite E1,E2;reflexivity.
    - pose proof (ewp_gnl_reg_trad o e) as E;
        unfold ewp_r in *;rewrite E;reflexivity.
  Qed.

  (** Helper lemma to lift the invariance of [|=(ø)=] with respect equivalences on *)
  (** terms and expression to lists up-to elementwise equivalence. *)
  
  Lemma list_lift_gnl_sat_modulo_eq  :
    forall (s1 s2 : list (GTerm A O)) e1 e2,
      list_lift (gnl_term_theo_eq Ø) s1 s2 ->
      list_lift (gnl_theo_sat Ø) s1 e1 ->
      list_lift (gnl_theo_eq Ø) e1 e2 ->
      list_lift (gnl_theo_sat Ø) s2 e2.
  Proof. intros l1 l2 m1 m2 hl hsat hm;rewrite <- hl,<-hm; assumption. Qed.

  (** The interpretation of [gnl_reg_proj o e] is contained in that of [gnl_reg_trad o e]. *)

  Lemma gnl_reg_proj_reg_trad_sat  (e : gnl_exp) o m :
    m |=(ka)= gnl_reg_proj o e -> m |=(ka)= gnl_reg_trad o e.
  Proof.
    revert m;induction e;simpl;intros m hsat;try tauto||discriminate.
    - intuition.
    - destruct (o0 =?= o);simpl in *;tauto.
    - destruct (o0 =?= o).
      + destruct hsat as [hsat|hsat];auto.
        * apply IHe in hsat. 
          exists m,[m];repeat split;auto with proofs.
          intros ? [<-|h];[|exfalso];auto.
        * destruct hsat as (m1&m'&->&hm1&m2&L&E&hm2&hL).
          exists (m1 ** m2),(m1::L);simpl;rewrite E;split;auto.
          rewrite hm2;split;auto with proofs.
          intros ? [<-|h];[|apply hL];auto.
      + apply IHe in hsat.
        left;assumption.
  Qed.

  (** * Semantic correspondance *)
  (** We now proceed to show an equivalence between the terms satisfying [e] and the *)
  (** decompositions satisfying [e]'s projections. *)

  (** ** Preliminary work *)
  (** A variable satisfies [e] iff it satisfies the [slat] projection of [e]. *)
  
  Lemma gnl_sat_vars  (e : gnl_exp) :
    forall x, t_var x |=(Ø)= e <-> x |=slat= gnl_slat_proj e.
  Proof.
    intros x;split;revert x;induction e;simpl.
    - tauto.
    - intros x0 E;apply get_var_eq in E;inversion E;reflexivity.
    - intuition.
    - intros x (s1&s2&E&_&_).
      apply get_var_eq in E;inversion E. 
    - intros x (s'&L&hs'&E&hL).
      revert s' hs' E.
      induction L;simpl.
      + discriminate.
      + intros s' hs' E.
        destruct (GProd o L);inversion hs';subst;clear hs'.
        * apply get_var_eq in E;discriminate.
        * apply IHe,hL;left.
          apply get_var_eq in E.
          destruct s';inversion E.
          reflexivity.
    - tauto.
    - intros a E;apply get_var_eq in E;inversion E;reflexivity.
    - intuition.
    - tauto. 
    - intros x ih;apply IHe in ih.
      exists (t_var x),[t_var x];repeat split;auto with proofs.
      intros ? [<-|F];[|exfalso;apply F];auto.
  Qed.

  (** Every term satisfying [e] can be fashioned into a decomposition *)
  (** satisfying [gnl_reg_trad o e]. *)
  
  Lemma gnl_reg_trad_sat (e : gnl_exp) :
    forall s o, s |=(Ø)= e ->  
                exists m, list_lift (gnl_theo_sat Ø) (gnl_term_to_list o s) (Word_to_list m)
                          /\  m |=(ka)= (gnl_reg_trad o e).
  Proof.
    induction e;simpl.
    - tauto.
    - intros s o E1.
      apply get_var_eq in E1.
      destruct s;simpl in *;try discriminate.
      inversion E1;subst;clear E1.
      exists (var_w (var x));repeat split;simpl;auto with proofs.
    - intuition.
      + destruct (IHe1 s o) as (m&h1&h2);auto.
        exists m;simpl;auto.
      + destruct (IHe2 s o) as (m&h1&h2);auto.
        exists m;simpl;auto.
    - intros s o' (s1&s2&hs&hs1&hs2).
      destruct (IHe1 s1 o) as (m1&h11&h12);auto.
      destruct (IHe2 s2 o) as (m2&h21&h22);auto.
      apply gnl_decompose_eq in hs as [(a&_&F)|(o''&l'&m&hl&hm&h)];[discriminate|].
       simpl in hm;rewrite eq_dec_eq in hm;symmetry in hm;inversion hm;subst;clear hm.
       destruct (o =?= o').
      + symmetry in e;subst.
        erewrite gnl_decompose_gnl_term_to_list by eassumption.
        exists (m1 ** m2);split.
        * apply list_lift_app in h as (l1&l2&->&hl1&hl2).
          apply app_list_lift.
          -- eapply list_lift_gnl_sat_modulo_eq;[symmetry;apply hl1| | reflexivity].
             assumption.
          -- eapply list_lift_gnl_sat_modulo_eq;[symmetry;apply hl2| | reflexivity].
             assumption.
        * exists m1,m2;repeat split;auto with proofs.
      + simpl.
        exists (var_w (e1 ×{o} e2));split;auto with proofs.
        destruct s;try discriminate.
        inversion hl;subst.
        simpl.
        rewrite eq_dec_neq by assumption.
        rewrite eq_dec_eq in *.
        split;simpl;auto.
        exists s1,s2;repeat split;auto.
        revert h;clear.
        intro h.
        apply (gnl_term_to_list_gnl_term_eq _ _ o).
        simpl;repeat rewrite eq_dec_eq.
        apply h.
    - firstorder.
      destruct (o =?= o0);subst.
      + revert s x H1 H H0;induction x0;simpl;[discriminate|].
        destruct (GProd o0 x0);intros s x hL E hs;inversion E;subst;clear E;setoid_rewrite hs;simpl.
        * rewrite eq_dec_eq.
          destruct (IHx0 g g) as (m&hm&hm2);try reflexivity;[intros ? h;apply hL;now right|].
          destruct (IHe a o0) as (l&hl1&hl2);[apply hL;now left|].
          destruct hm2 as (m'&L'&E&hm1&hm2).
          exists (l ** m').
          split.
          -- simpl;apply app_list_lift;auto.
             apply Word_to_list_eq in hm1 as <-;assumption.
          -- exists (l**m'),(l::L');repeat split;simpl;auto with proofs.
             ++ rewrite E;reflexivity.
             ++ intros ? [<-|h];auto.
        * clear IHx0.
          destruct (IHe x o0) as (l&hl1&hl2);[apply hL;now left|].
          eexists;split;[eassumption|].
          exists l,[l].
          repeat split;auto with proofs.
          intros ? [<-|h];[|exfalso];auto. 
      + simpl.
        case_eq x0;[intro;subst;discriminate|].
        intros g l' ->.
        case_eq (GProd o l').
        * intros g' hg'.
          simpl in H;rewrite hg' in H;inversion H;subst;clear H.
          destruct s.
          -- apply get_var_eq in H0;discriminate.
          -- pose proof H0 as h';apply get_op_eq in h';simpl in h';inversion h';subst;clear h'.
             simpl.
             rewrite eq_dec_neq by assumption.
             exists (var_w (e ×{o} e^{o})).
             repeat split;auto.
             exists g,g';repeat split;auto with proofs.
             ++ apply H1;now left.
             ++ exists g',l';repeat split;auto with proofs.
                intros;apply H1;now right.
             ++ right;auto with proofs.
        * simpl in *;intro E;rewrite E in *.
          inversion H;subst;clear H.
          destruct l';[clear E|simpl in E;destruct (GProd o l');discriminate].
          simpl in *.
          destruct (IHe x o0) as (m&h1&h2);auto.
          exists m;split;auto.
          rewrite H0.
          assumption.
  Qed.

  (** For every term satisfying [e] whose decomposition is a pair [o,l], that pair satisfies *)
  (** [gnl_reg_proj o e]. *)
  
  Lemma gnl_reg_proj_sat (e : gnl_exp) :
    forall s o l,  s |=(Ø)= e -> gnl_decompose s = inr (o,l) -> 
                   exists m, list_lift (gnl_theo_sat Ø) l (Word_to_list m)
                             /\ m |=(ka)= gnl_reg_proj o e.
  Proof.
    induction e;simpl.
    - tauto.
    - intros s o l E1 E2.
      apply get_var_eq in E1.
      destruct s;simpl in *;try discriminate.
    - intuition.
      + destruct (IHe1 s o l H1 H0) as (m&hlm&hmr).
        exists m;eexists;repeat split;try reflexivity;
          simpl;auto.
      + destruct (IHe2 s o l H1 H0) as (m&hlm&hmr).
        exists m;eexists;repeat split;try reflexivity;
          simpl;auto.
    - firstorder.
      apply gnl_decompose_eq in H as [(?&_&F)|(o'&l'&m'&h1&h2&h3)];
        [discriminate|].
      rewrite h1 in H0;inversion H0;subst;clear H0.
      simpl in h2;rewrite eq_dec_eq in h2;inversion h2;subst;clear h2.
      rewrite eq_dec_eq.
      clear s h1.
      apply (gnl_reg_trad_sat _ _ o0) in H1 as (m1&hm1&he1);
        apply (gnl_reg_trad_sat _ _ o0) in H2 as (m2&hm2&he2).
      exists (m1**m2);split;[|exists m1,m2;repeat split;auto with proofs].
      eapply list_lift_gnl_sat_modulo_eq;[symmetry;apply h3| |reflexivity].
      apply app_list_lift;assumption.
    - intros s o' l (s'&L&eL&hs'&hL) hs.
      destruct (o =?= o').
      + symmetry in e0;subst.
        revert s l s' eL hL hs' hs.
        induction L;simpl;intros;try discriminate.
        case_eq (GProd o L);[intros g Eg;rewrite Eg in *|intro E];inversion eL;subst;clear eL.
        * assert (h : a |=(Ø)= e) by (apply hL;now left).
          apply  (gnl_reg_trad_sat _ _ o) in h as (m1&hm1&he1).
          destruct s;inversion hs;subst;clear hs.
          rewrite eq_dec_eq.
          destruct g.
          -- simpl in *.
             destruct L as [|? [|? L]];[ | |simpl in Eg;destruct (GProd o L)];
                  inversion Eg;subst;clear Eg.
             assert (h: t_var a0 |=(Ø)= e) by (apply hL;now right;left).
             apply (gnl_reg_trad_sat _ _ o) in h as (k&hk1&hk2).
             simpl in hk1.
             remember (Word_to_list k) as wk;destruct wk as [|?[]];simpl in hk1;try tauto.
             destruct hk1 as (h&_).
             exists (m1 ** k);split;
               [replace (gnl_term_to_list _ _ ++ _) with (gnl_term_to_list o (t_prod o s1 s2))
                 by (simpl;rewrite eq_dec_eq;reflexivity);
                rewrite hs';simpl;rewrite eq_dec_eq;apply app_list_lift;simpl;auto
               |].
             ++ rewrite <- Heqwk;tauto.
             ++ right;exists m1,k;repeat split;auto with proofs.
                exists k,[k];repeat split;auto with proofs.
                intros ? [<-|?];[|exfalso];auto.
          -- destruct (o =?= o0).
             ++ subst.
                destruct (IHL (t_prod o0 g1 g2) (gnl_term_to_list o0 (t_prod o0 g1 g2))
                            (t_prod o0 g1 g2)) as (M&hM&hr);reflexivity||auto.
                replace (gnl_term_to_list _ _ ++ _) with (gnl_term_to_list o0 (t_prod o0 s1 s2))
                  by (simpl;rewrite eq_dec_eq;reflexivity).
                setoid_rewrite hs'.
                simpl in *;repeat rewrite eq_dec_eq in *.
                exists (m1**M);repeat split;auto.
                ** apply app_list_lift;auto.
                ** right;destruct hr as [hr|hr];exists m1,M;repeat split;auto with proofs.
                   --- exists M,[M];repeat split;auto with proofs.
                       intros ? [<-|?];[|exfalso];auto.
                       eapply gnl_reg_proj_reg_trad_sat;eassumption.
                   --- destruct hr as (M1&M'&E1&hM1&M2&L'&E2&hM2&hL').
                       setoid_rewrite E1.
                       setoid_rewrite hM2.
                       exists (M1**M2),(M1::L');simpl;rewrite E2;repeat split;auto with proofs.
                       intros k [<-|hk];auto.
             ++  simpl in *.
                 destruct L as [|? [|? L]];[ | |simpl in *;destruct (GProd o L)];
                   inversion Eg;subst;simpl in Eg;try (subst;tauto);clear Eg.
                 assert (h: g1 -[o0]- g2 |=(Ø)= e) by (apply hL;now right;left).
                 apply (gnl_reg_trad_sat _ _ o) in h as (k&hk1&hk2).
                 remember (Word_to_list k) as wk;destruct wk as [|?[]];simpl in hk1;
                   rewrite eq_dec_neq in hk1 by (symmetry;assumption);
                   try (simpl in *;tauto).
                 destruct hk1 as (h&_).
                 exists (m1**k);split;
                   [replace (gnl_term_to_list _ _ ++ _) with (gnl_term_to_list o (t_prod o s1 s2))
                     by (simpl;rewrite eq_dec_eq;reflexivity);
                    rewrite hs';simpl;rewrite eq_dec_eq;apply app_list_lift;simpl;auto;
                    rewrite eq_dec_neq by (symmetry;assumption);rewrite <-Heqwk;simpl;auto
                   |].
                 right.
                 exists m1,k;repeat split;auto with proofs.
                 exists k,[k];split;[reflexivity|];split;auto with proofs.
                 intros ? [<-|?];[|exfalso];auto.
        * clear IHL.
          rewrite E in H0;inversion H0;subst;clear H0.
          assert (h: s' |=(Ø)= e) by (apply hL;now left).
          rewrite <- hs' in h.
          eapply IHe in h as (m&hm1&hm2);[|apply hs].
          exists m;split;[assumption|].
          left;assumption.
      +  destruct L as [|? [|? L]];[ | |simpl in *;destruct (GProd o L)];inversion eL;subst.
         * eapply IHe;[|apply hs].
           rewrite hs';apply hL;now left.
         * destruct s;simpl in hs;try rewrite eq_dec_eq in hs;inversion hs;subst;clear hs.
           apply get_op_eq in hs';simpl in hs';inversion hs';subst;tauto.
         * destruct s;simpl in hs;try rewrite eq_dec_eq in hs;inversion hs;subst;clear hs.
           apply get_op_eq in hs';simpl in hs';inversion hs';subst;tauto.
  Qed.

  (** It is now straightforward to show that for every term satisfying [e], its decomposition *)
  (** satisfies one of [e]'s projections. *)
  
  Lemma gnl_decompose_sat
    (s : GTerm A O) (e : gnl_exp) :
    s |=(Ø)= e -> gnl_decomp_sat Ø (gnl_decompose s) e.
  Proof.
    destruct s;simpl.
    - apply gnl_sat_vars.
    - intros h.
      remember (gnl_decompose (t_prod o s1 s2)) as d;simpl in Heqd.
      rewrite eq_dec_eq in *.
      destruct (gnl_reg_proj_sat _ _ o (gnl_term_to_list o s1 ++ gnl_term_to_list o s2) h)
        as (L&hL&hr);[simpl;rewrite eq_dec_eq;reflexivity|].
      exists L;repeat split;auto.
  Qed.


  (** Conversely, for every decomposition satisfying [e]'s projections, its recomposed *)
  (** term satisfies [e]. *)
  
  Lemma gnl_recompose_sat (s: gnl_decomposition) e :
    gnl_decomp_sat Ø s e -> exists t, gnl_recompose s = Some t /\ t |=(Ø)= e.
  Proof.
    destruct s as [x|(o,l)];simpl.
    - induction e ;simpl;auto;firstorder subst.
      + eexists;split;[reflexivity|].
        apply get_var_eq in H;inversion H;subst;reflexivity.
      + eexists;split;[reflexivity|].
        exists (t_var x),[t_var x];repeat split;try reflexivity.
        intros ? [<-|F];[|exfalso;apply F].
        inversion H0;subst;assumption.
    - intros (m&hlm&hmr).
      apply (gnl_reg_proj_reg_trad_sat e o) in hmr. 
      revert l m hlm hmr.
      induction e;intros;simpl in *.
      + tauto.
      + subst.
        exists (t_var x);split;[|reflexivity].
        pose proof hmr as E.
        apply Word_to_list_eq in E;rewrite E in hlm.
        destruct l as [|?[|]];simpl in hlm;try tauto.
        destruct hlm as (h&_).
        simpl;f_equal.
        apply get_var_eq in h;destruct g;inversion h;subst.
        reflexivity.
      + firstorder.
      + destruct (o0 =?= o).
        * subst.
          destruct hmr as (m1&m2&E&hm1&hm2).
          pose proof E as E'.
          apply Word_to_list_eq in E';rewrite E' in hlm;simpl in hlm.
          apply list_lift_app in hlm as (l1&l2&->&hl1&hl2).
          eapply IHe1 in hm1 as (t1&ht1&he1);[|eassumption].
          eapply IHe2 in hm2 as (t2&ht2&he2);[|eassumption].
          cut (exists t : GTerm A O,
                  GProd o (l1 ++ l2) = Some t /\ Ø |- t =T= t1 -[o]- t2).
          -- intros (t&ht&E1).
             exists t;split;auto.
             exists t1,t2;split;auto.
          -- clear IHe1 IHe2 he1 he2 m1 m2 E E' hl1 hl2 e1 e2.
             revert l2 t1 t2 ht1 ht2.
             apply GProd_app.
        * simpl in hmr;subst.
          pose proof hmr as E.
          apply Word_to_list_eq in E;rewrite E in hlm.
          destruct l as [|?[|]];simpl in hlm;try tauto.
          destruct hlm as ((s1&s2&hg&hs1&hs2)&_).
          simpl;exists g;split;auto.
          exists s1,s2;split;auto.
      +  destruct (o0 =?= o).
        * subst.
          destruct hmr as (m1&M&E1&hm1&hM).
          apply Word_to_list_eq in hm1;rewrite hm1 in hlm;clear m hm1.
          revert l m1 E1 hlm hM;induction M;[discriminate|].
          destruct (M =?= []).
          -- clear IHM;subst;intros;inversion E1;subst;clear E1.
             assert (h: m1  |=( ka )= gnl_reg_trad o e) by (apply hM;now left).
             apply (IHe l) in h as (t'&ht'&h);auto.
             exists t';split;auto.
             exists t',[t'];repeat split;auto with proofs.
             intros ? [<-|F];[|exfalso];auto.
          -- apply (GProd_Some _ •) in n as (t2&ht2).
             simpl;rewrite ht2.
             intros l ? E h1 hM.
             inversion E;subst;clear E.
             simpl in h1;apply list_lift_app in h1 as (l1&l2&->&h1&h2).
             assert (h: a  |=( ka )= gnl_reg_trad o e) by (apply hM;now left).
             apply (IHe l1) in h as (t'&ht'1&ht'2);auto.
             destruct (IHM l2 t2) as (T&hT1&s'&L'&hT2&hT3&hT4);auto.
             destruct (GProd_app Ø _ _ _ _ _ ht'1 hT1) as (T'&hT'&ET').
             exists T';split;auto.
             setoid_rewrite ET'.
             setoid_rewrite hT3.
             exists (t' -[o]- s'),(t'::L');simpl;rewrite hT2;repeat split;auto with proofs.
             intros ? [<-|h];[|apply hT4];auto.
        * destruct hmr as [hmr|hmr];[|simpl in hmr;subst].
          ++ apply (IHe l) in hmr as (t&ht&he);auto.
             exists t;split;auto.
             exists t,[t];repeat split;auto with proofs.
             intros ? [<-|F];[|simpl in F];tauto.
          ++ pose proof hmr as E;apply Word_to_list_eq in E;rewrite E in hlm;clear E.
             destruct l as [|?[|]];simpl in hlm;try tauto.
             destruct hlm as ((s1&s2&hg&hs1&s'&L&E&hs2&hL)&_).
             simpl;exists g;split;auto.
             exists (t_prod o0 s1 s'),(s1::L);simpl;rewrite E.
             split;auto.
             split;[rewrite hg;apply gnlt_prod;auto with proofs|].
             intros ? [<-|h];[|apply hL];auto.
  Qed.

  (** The interpretation of [e]'s projections only contains valid decompositions. *)
  
  Lemma gnl_decomp_sat_valid (s : gnl_decomposition) e :
    gnl_decomp_sat Ø s e -> gnl_valid s = true.
  Proof.
    destruct s as [|(o,l)];simpl;auto.
    intros (m&hlm&hmr).
    rewrite Bool.andb_true_iff,PeanoNat.Nat.ltb_lt,forallb_forall.
    split.
    - destruct l as [|?[]];[| |simpl;lia];exfalso.
      + cut (ka |- m =T= 1_w).
        * intros E;rewrite E in hmr.
          apply ewp_r_spec in hmr.
          rewrite ewp_gnl_reg_proj in hmr;discriminate.
        * rewrite <- Word_to_list_and_back.
          destruct (Word_to_list m);[reflexivity|simpl in hlm;tauto].
      + revert g m hlm hmr.
        induction e;try (now firstorder).
        * intros g m hgm.
          simpl;destruct (o0 =?= o);simpl;[subst|tauto].
          intros (s1&s2&h1&h2&h3).
          cut (ka |- s1 =T= 1_w \/ ka |- s2 =T= 1_w).
          -- intros [E|E].
             ++ rewrite E in h2.
                apply ewp_r_spec in h2.
                rewrite ewp_gnl_reg_trad in h2;discriminate.
             ++ rewrite E in h3.
                apply ewp_r_spec in h3.
                rewrite ewp_gnl_reg_trad in h3;discriminate.
          -- rewrite <- Word_to_list_and_back.
             rewrite <- (Word_to_list_and_back s2).
             apply Word_to_list_eq in h1;rewrite h1 in hgm.
             simpl in hgm.
             destruct (Word_to_list s1);[left;reflexivity|right].
             destruct hgm as (_&hgm).
             cut (l++Word_to_list s2 = []);[|destruct (l++Word_to_list s2);
                                             [reflexivity|simpl in hgm;tauto]].
             intro E;apply app_eq_nil in E as (_&->);reflexivity.
        * intros;simpl in hmr;destruct (o0 =?= o);simpl in hmr;
            [|apply (IHe g m);auto].
          destruct hmr as [hmr|hmr];[apply (IHe g m);auto|].
          destruct hmr as (s1&s2&Em&h1&s'&L&h2&h3&hL).
          apply Word_to_list_eq in Em;rewrite Em in hlm.
          cut (ka |- s1 =T= 1_w \/ ka |- s2 =T= 1_w).
          -- intros [E|E].
             ++ rewrite E in h1.
                apply ewp_r_spec in h1.
                rewrite ewp_gnl_reg_trad in h1;discriminate.
             ++ cut (1_w |=(ka)= gnl_reg_trad o (iter o e)).
                ** intros F.
                   apply ewp_r_spec in F.
                   rewrite ewp_gnl_reg_trad in F;discriminate.
                ** rewrite <- E,h3.
                   simpl;rewrite eq_dec_eq;exists s',L;repeat split;auto with proofs.
          -- rewrite <- Word_to_list_and_back.
             rewrite <- (Word_to_list_and_back s2).
             simpl in hlm.
             destruct (Word_to_list s1);[left;reflexivity|right].
             destruct hlm as (_&hgm).
             cut (l++Word_to_list s2 = []);[|destruct (l++Word_to_list s2);
                                             [reflexivity|simpl in hgm;tauto]].
             intro E;apply app_eq_nil in E as (_&->);reflexivity.
    - revert l m hlm hmr.
      cut (forall (e : gnl_exp) (l : list (GTerm A O)) m,
              list_lift (gnl_theo_sat Ø)  l (Word_to_list m) -> m |=(ka)= (gnl_reg_trad o e) ->
              forall x : GTerm A O, In x l -> gnl_valid_elt o x = true);[intros htrad|].
      + induction e;simpl;try discriminate;try (destruct (o0 =?= o);[subst|]);try discriminate;
          simpl;
          try discriminate;intros l m hml hmr;
          try destruct hmr as [hmr|hmr];
          try destruct hmr as (m1&m'&E&hm1&hmr);
          try destruct hmr as (m2&L&E2&hm2&hL);
          try (apply Word_to_list_eq in E;rewrite E in hml;simpl in hml);
          try apply list_lift_app in hml as (l1&l'&->&hl1&hml);
          try apply list_lift_app in hml as (l2&l3&->&hl2&hl3);
          repeat setoid_rewrite in_app_iff;intros ? h;repeat destruct h as [h|h];revert h;
          try (now eapply IHe1;eauto)||(now eapply IHe2;eauto)||(now eapply IHe;eauto)
          || tauto || (now eapply htrad;eauto).
        clear IHe hl1 l1 E m m1 hm1.
        apply Word_to_list_eq in hm2;rewrite hm2 in hml;clear m' hm2.
        revert l' m2 hml E2 hL;induction L;[discriminate|].
        destruct (L =?= []);[subst;clear IHL|apply (GProd_Some _ •) in n as (t&ht)];intros;
          simpl in E2;try rewrite ht in E2;inversion E2;subst;clear E2.
        * apply (htrad e l' m2);simpl;auto.
          apply hL;now left.
        * simpl in hml.
          apply list_lift_app in hml as (l1&l2&->&h1&h2).
          apply in_app_iff in h as [h|h].
          -- apply (htrad e l1 a);auto.
             apply hL;now left.
          -- destruct (IHL l2 t);auto.
             intros;apply hL;now right.
      + clear e;intros e;induction e;simpl;try (destruct (o0 =?= o));simpl;
          firstorder subst.
        * apply Word_to_list_eq in H0;rewrite H0 in H;simpl in H.
          destruct l as [|?[|]];try (exfalso;apply H).
          destruct H1 as [<-|F];[|exfalso;apply F].
          destruct H as (H&_);simpl in H.
          pose proof (get_var_eq _ _ H) as E.
          destruct g;inversion E;subst;clear E.
          reflexivity.
        * apply Word_to_list_eq in H0;rewrite H0 in H;simpl in H.
          apply list_lift_app in H as (l0&l1&->&hl0&hl1).
          rewrite in_app_iff in H1;destruct H1 as [h|h];revert h.
          -- eapply IHe1;eauto.
          -- eapply IHe2;eauto.
        * apply Word_to_list_eq in H0;rewrite H0 in H;simpl in H.
          destruct l as [|?[|]];try (exfalso;apply H).
          destruct H1 as [<-|F];[|exfalso;apply F].
          destruct H as ((s1&s2&H&h1&h2)&_);simpl in H.
          pose proof (get_op_eq _ _ H) as E.
          destruct g;inversion E;subst;clear E.
          simpl;rewrite eq_dec_neq by (intros ->;tauto).
          reflexivity.
        * apply Word_to_list_eq in H2;rewrite H2 in H;simpl in H.
          clear H2 m.
          revert l x0 H H0 H3 x H1;induction x1;[discriminate|].
          destruct (x1 =?= []);
            [subst;clear IHx1|apply (GProd_Some _ •) in n as (t&ht)];intros;
            simpl in H0;try rewrite ht in H0;inversion H0;subst;clear H0.
          -- apply (IHe l x0);repeat split;auto.
             apply H3;now left.
          -- simpl in H;apply list_lift_app in H as (l1&l2&->&h1&h2).
             rewrite in_app_iff in H1;destruct H1 as [h|h];revert h.
             ++ apply (IHe l1 a);auto.
                apply H3;now left.
             ++ apply (IHx1 l2 t);auto.
                intros;apply H3;now right.
        * apply Word_to_list_eq in H0;rewrite H0 in H;simpl in H.
          destruct l as [|?[|]];try (exfalso;apply H).
          destruct H1 as [<-|F];[|exfalso;apply F].
          destruct H as ((s1&s2&Eg&h1&s3&L&EL&Es23&hL)&_).
          destruct g as [|o'];auto.
          simpl;destruct (o =?= o');auto.
          subst.
          apply get_op_eq in Eg;simpl in Eg;inversion Eg;subst;tauto. 
  Qed.

  (** ** Main theorem: semantic correspondance *)
  
  Theorem gnl_semantic_correspondance :
    forall s (e : gnl_exp),
      gnl_decomp_sat Ø s e <-> exists t, gnl_decomp_eq Ø s (gnl_decompose t)
                                          /\ t |=(Ø)= e.
  Proof.
    intros s e.
    transitivity (gnl_valid s = true /\ exists t, gnl_recompose s = Some t /\ t |=(Ø)= e).
    - split;[intro hsat;split;[eapply gnl_decomp_sat_valid|apply gnl_recompose_sat];eauto|].
      intros (hv&(t&E&ht)).
      rewrite <- (decompose_recompose s t hv E).
      apply gnl_decompose_sat,ht.
    - split.
      + intros (V&t&E&h).
        exists t;split;auto.
        erewrite (decompose_recompose) by eassumption.
        reflexivity.
      + intros (t&E&h).
        cut (gnl_valid s = true);[|rewrite E;apply gnl_decompose_valid].
        intros V;split;auto.
        destruct (gnl_recompose_Some _ V) as (t'&h').
        pose proof (decompose_recompose _ _ V h') as <-.
        pose proof (recompose_decompose t') as (t''&h1&_).
        rewrite h1 in h';inversion h';subst;clear h'.
        exists t';split;auto.
        apply gnl_recompose_proper in E.
        pose proof (recompose_decompose t) as (t''&h2&h3).
        rewrite h1,h2 in E;simpl in E.
        rewrite E,<-h3;assumption.
  Qed.

  (** * Clean projections *)

  (** To apply the decompositions inductively, we need the projections to be built out of *)
  (** _strictly smaller_ expressions for some ordering. The ordering we shall consider *)
  (** (later on) will be based on [depth], a semantic notion. However, because of its *)
  (** annihilation powers, [ø] may _hide_ subexpressions from the semantics, like in the *)
  (** expression [ø ×{o} e], where [e] is a proper subexpression while not contributing to *)
  (** the semantics. This means the projections defined above may feature in their support *)
  (** expressions of larger depth, which is problematic. To circumvent this problem, we *)
  (** apply the function [Clean] before and after projecting, to ensure we have _productive_ *)
  (** expressions, whose every subexpression contribute to the semantics. *)

  (** Thus we define a new notion of satisfaction between decompositions and expressions, *)
  (** using _clean_ projections. Notice that we do not bother cleaning the [slat] projection, *)
  (** as it is not meant to bear an inductive principle. *)

  Definition gnl_clean_decomp_sat r s e :=
    match s with
    | inl a => a |=slat= gnl_slat_proj e
    | inr (o, l) =>
        exists m : Word (GExp A O),
          list_lift (gnl_theo_sat r) l (Word_to_list m)
          /\ m |=( ka )= Clean (gnl_reg_proj o (Clean e))
    end.

  (** ** Semantic correspondance *)
  
  (** We proceed to show that the semantic correspondance from the previous section still *)
  (** holds. We begin by showing, first for [gnl_reg_trad], then for [gnl_reg_proj] that *)
  (** cleaning does not change the semantics of the output. *)
  
  Lemma gnl_reg_trad_Clean (r : relation (GTerm A O)) o e l :
    (exists m : Word (GExp A O),
      list_lift (gnl_theo_sat r) l (Word_to_list m) /\  m |=( ka )= gnl_reg_trad o (Clean e))
    <->  (exists m : Word (GExp A O),
             list_lift (gnl_theo_sat r) l (Word_to_list m) /\ m |=( ka )= gnl_reg_trad o e).
  Proof.
    unfold Clean;revert l.
    induction e;simpl;try (now split; auto with proofs);intro l.
    - transitivity(exists m : Word (GExp A O),
                      list_lift (gnl_theo_sat r) l (Word_to_list m) /\
                        (m |=( ka )= gnl_reg_trad o (Clean e1)
                         \/ m |=( ka )= gnl_reg_trad o (Clean e2))).
      + unfold Clean;destruct (clean_exp e1),(clean_exp e2);simpl;split;intros (m&hl&hsat);
          try destruct hsat as [hsat|hsat];exists m;split;tauto||auto.
      + unfold Clean;destruct (clean_exp e1) as [g1|],(clean_exp e2) as [g2|];simpl;split;
          intros (m&hl&[hsat|hsat]);
          try ((assert (h: exists m, list_lift (gnl_theo_sat r) l (Word_to_list m) /\
                                       m |=( ka )= gnl_reg_trad o g1)
                 by ((now exists m;split;[assumption|apply hsat])
                     ||(apply IHe1||apply IHe2;exists m;split;[assumption|apply hsat])))
               ||(assert (h:exists m, list_lift (gnl_theo_sat r) l (Word_to_list m) /\
                                        m |=( ka )= gnl_reg_trad o g2)
                   by ((now exists m;split;[assumption|apply hsat])
                       ||(apply IHe1||apply IHe2;exists m;split;[assumption|apply hsat])))
               || (assert (h:exists m, list_lift (gnl_theo_sat r) l (Word_to_list m) /\
                                         m |=( ka )= ø)
                    by ((now exists m;split;[assumption|apply hsat])
                        ||(apply IHe1;exists m;split;[assumption|apply hsat])
                        ||(apply IHe2;exists m;split;[assumption|apply hsat]))));
               (destruct h as (m'&hl'&hsat');exists m';split;tauto)
               ||(apply IHe1 in h||apply IHe2 in h;destruct h as (m'&hl'&hsat');
                  exists m';split;tauto).
    - destruct (o0 =?= o).
      + subst;simpl.
        destruct (clean_exp e1),(clean_exp e2);simpl;try rewrite eq_dec_eq. 
        * split;intros (m & h1 & h2).
          -- destruct h2 as (m1&m2&h2&hm1&hm2).
             pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
             assert (ih1 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o g)
               by (exists m1;split;auto);apply IHe1 in ih1 as (m'1&lift1&sat1).
             assert (ih2 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l2 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o g0)
               by (exists m2;split;auto);apply IHe2 in ih2 as (m'2&lift2&sat2).
             exists (m'1 ** m'2);split;auto.
             ++ simpl;apply app_list_lift;auto.
             ++ exists m'1,m'2;split;auto with proofs.
          -- destruct h2 as (m1&m2&h2&hm1&hm2).
             pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
             assert (ih1 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o e1)
               by (exists m1;split;auto);apply IHe1 in ih1 as (m'1&lift1&sat1).
             assert (ih2 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l2 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o e2)
               by (exists m2;split;auto);apply IHe2 in ih2 as (m'2&lift2&sat2).
             exists (m'1 ** m'2);split;auto.
             ++ simpl;apply app_list_lift;auto.
             ++ exists m'1,m'2;split;auto with proofs.
        * split;[firstorder|].
          intros (m&h1&m1&m2&h2&hm1&hm2);exfalso.
          pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
          assert (ih2 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l2 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o e2)
               by (exists m2;split;auto);apply IHe2 in ih2 as (m'2&lift2&sat2).
          apply sat2.
        * split;[firstorder|].
          intros (m&h1&m1&m2&h2&hm1&hm2);exfalso.
          pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
          assert (ih1 : exists m : Word (GExp A O),
                     list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                     /\ m |=( ka )= gnl_reg_trad o e1)
            by (exists m1;split;auto);apply IHe1 in ih1 as (m'1&lift1&sat1).
          apply sat1.
        * split;[firstorder|].
          intros (m&h1&m1&m2&h2&hm1&hm2);exfalso.
          pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
          assert (ih1 : exists m : Word (GExp A O),
                     list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                     /\ m |=( ka )= gnl_reg_trad o e1)
            by (exists m1;split;auto);apply IHe1 in ih1 as (m'1&lift1&sat1).
          apply sat1.
      + pose proof (Clean_is_eq e1) as C1.
        pose proof (Clean_is_eq e2) as C2.
        unfold Clean in *.
        destruct (clean_exp e1),(clean_exp e2);simpl;auto;
        try (split;[now firstorder|intro h;exfalso]).
        * rewrite eq_dec_neq by assumption.
          simpl.
          split;intros (m&h1&h2).
          -- pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             simpl in h1.
             destruct l as [|?[|]];try (exfalso;apply h1).
             destruct h1 as (h1&_).
             destruct h1 as (m1&m2&E&hm1&hm2).
             exists (var_w (e1 ×{o0} e2));split;auto with proofs.
             split;[|reflexivity].
             exists m1,m2;repeat split;auto.
             ++ eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                           |reflexivity|apply C1|apply hm1].
             ++ eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                           |reflexivity|apply C2|apply hm2].
          -- pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             simpl in h1.
             destruct l as [|?[|]];try (exfalso;apply h1).
             destruct h1 as (h1&_).
             destruct h1 as (m1&m2&E&hm1&hm2).
             exists (var_w (g ×{o0} g0));split;auto with proofs.
             split;[|reflexivity].
             exists m1,m2;repeat split;auto.
             ++ eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                           |reflexivity|apply C1|apply hm1].
             ++ eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                           |reflexivity|apply C2|apply hm2].
        * destruct h as (m&h1&h2).
          pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          simpl in h1.
          destruct l as [|?[|]];try (exfalso;apply h1).
          destruct h1 as (h1&_).
          destruct h1 as (m1&m2&E&hm1&hm2).
          cut (m2 |=(r)= ø);[tauto|].
          eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                     |reflexivity|apply C2|apply hm2].
        * destruct h as (m&h1&h2).
          pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          simpl in h1.
          destruct l as [|?[|]];try (exfalso;apply h1).
          destruct h1 as (h1&_).
          destruct h1 as (m1&m2&E&hm1&hm2).
          cut (m1 |=(r)= ø);[tauto|].
          eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                     |reflexivity|apply C1|apply hm1].
        * destruct h as (m&h1&h2).
          pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          simpl in h1.
          destruct l as [|?[|]];try (exfalso;apply h1).
          destruct h1 as (h1&_).
          destruct h1 as (m1&m2&E&hm1&hm2).
          cut (m2 |=(r)= ø);[tauto|].
          eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                     |reflexivity|apply C2|apply hm2].
    - destruct (o0 =?= o);subst.
      + destruct (clean_exp e);simpl;try rewrite eq_dec_eq. 
        * simpl;split;intros (m&h1&s&L&E&h2&hL);
            revert l s m E h1 h2 hL;
            (induction L;[discriminate
                         |destruct (L =?= []);
                          [subst;clear IHL
                          |apply (GProd_Some _ •) in n as (t&ht);simpl;rewrite ht];
                          intros l ? m E;inversion E;subst;clear E;intros]).
          -- pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o g)
               by (exists s;split;[assumption|apply hL;now left]). 
             apply IHe in ih as (m'&lift&sat).
             exists m';split;auto.
             exists m',[m'];repeat split;auto with proofs.
             intros ? [<-|F];[|exfalso];auto.
          -- pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
             destruct (IHL l2 t t) as (m'2&hm'1&s'&L'&EL'&hm'2&hm'3);auto with proofs.
             assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o g)
               by (exists a;split;[assumption|apply hL;now left]). 
             apply IHe in ih as (m'1&hm'4&hm'5).
             exists (m'1**m'2);repeat split.
             ++ simpl;apply app_list_lift;auto.
             ++ exists (m'1**s'),(m'1::L');simpl;rewrite EL',hm'2;repeat split;auto with proofs.
                intros ? [<-|h];[|apply hm'3];auto.
          -- pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o e)
               by (exists s;split;[assumption|apply hL;now left]). 
             apply IHe in ih as (m'&lift&sat).
             exists m';split;auto.
             exists m',[m'];repeat split;auto with proofs.
             intros ? [<-|F];[|exfalso];auto.
          -- pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
             destruct (IHL l2 t t) as (m'2&hm'1&s'&L'&EL'&hm'2&hm'3);auto with proofs.
             assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o e)
               by (exists a;split;[assumption|apply hL;now left]). 
             apply IHe in ih as (m'1&hm'4&hm'5).
             exists (m'1**m'2);repeat split.
             ++ simpl;apply app_list_lift;auto.
             ++ exists (m'1**s'),(m'1::L');simpl;rewrite EL',hm'2;repeat split;auto with proofs.
                intros ? [<-|h];[|apply hm'3];auto.
        * split;[firstorder|].
          intros (m&h1&s&L&E&h2&hL);exfalso.
          destruct L;[discriminate|].
          simpl in E;destruct (GProd • L);inversion E;subst;clear E;
            pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          -- simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
             assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o e)
               by (exists g;split;[assumption|apply hL;now left]). 
             apply IHe in ih as (?&_&F);apply F.
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o e)
               by (exists s;split;[assumption|apply hL;now left]). 
             apply IHe in ih as (?&_&F);apply F.
      + pose proof (Clean_is_eq e) as C;unfold Clean in C.
        destruct (clean_exp e);simpl;try rewrite eq_dec_neq by assumption.
        * split;intros (m&h1&[h2|h2]).
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o g)
               by (exists m;split;assumption). 
             apply IHe in ih as (m'&lift&sat).
             exists m';auto.
          -- simpl in h2.
             pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E;simpl in h1.
             destruct l as [|?[|]];try (exfalso;apply h1).
             exists (t_var (Some (e ×{ o0} e ^{ o0})));repeat split;auto with proofs.
             destruct h1 as (h1&_).
             destruct h1 as (x1&x2&E&hx1&hx2).
             exists x1,x2;repeat split;auto.
             ++ eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                           |reflexivity|apply C|apply hx1].
             ++ destruct hx2 as (s'&L&hs'&hx2&hL).
                exists s',L;repeat split;auto.
                intros.
                eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                           |reflexivity|apply C|apply hL,H].
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o e)
               by (exists m;split;assumption). 
             apply IHe in ih as (m'&lift&sat).
             exists m';repeat split;auto.
             now left.
          -- simpl in h2.
             pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E;simpl in h1.
             destruct l as [|?[|]];try (exfalso;apply h1).
             exists (t_var (Some (g ×{ o0} g ^{ o0})));split;[|right;simpl;auto with proofs].
             destruct h1 as (h1&_).
             destruct h1 as (x1&x2&E&hx1&hx2).
             split;auto;[|simpl;tauto].
             exists x1,x2;repeat split;auto.
             ++ eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                           |reflexivity|apply C|apply hx1].
             ++ destruct hx2 as (s'&L&hs'&hx2&hL).
                exists s',L;repeat split;auto.
                intros.
                eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                           |reflexivity|apply C|apply hL,H].
        * split;[firstorder|].
          intros (m&h1&[h2|h2]);exfalso.
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o e)
               by (exists m;split;assumption). 
             apply IHe in ih as (m'1&hm'1&hm'2).
             apply hm'2.
          -- pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E;simpl in h1.
             destruct l as [|?[|]];try (exfalso;apply h1).
             destruct h1 as (h1&_).
             destruct h1 as (x1&x2&E&hx1&hx2).
             cut (x1 |=(r)= ø);[intro h;apply h|].
              eapply gnl_theo_sat_proper;[intros ? ? ? h;exfalso;apply h
                                         |reflexivity|apply C|apply hx1].
  Qed.

  
  Lemma gnl_reg_proj_Clean r o e l :
    (exists m : Word (GExp A O),
        list_lift (gnl_theo_sat r) l (Word_to_list m) /\  m |=( ka )= gnl_reg_proj o (Clean e))
    <->  (exists m : Word (GExp A O),
             list_lift (gnl_theo_sat r) l (Word_to_list m) /\ m |=( ka )= gnl_reg_proj o e).
  Proof.
    unfold Clean;revert l.
    induction e;simpl;try (now split; auto with proofs);intro l.
    - transitivity(exists m : Word (GExp A O),
                      list_lift (gnl_theo_sat r) l (Word_to_list m) /\
                        (m |=( ka )= gnl_reg_proj o (Clean e1)
                         \/ m |=( ka )= gnl_reg_proj o (Clean e2))).
      + unfold Clean;destruct (clean_exp e1),(clean_exp e2);simpl;split;intros (m&hl&hsat);
          try destruct hsat as [hsat|hsat];exists m;split;tauto||auto.
      + unfold Clean;destruct (clean_exp e1) as [g1|],(clean_exp e2) as [g2|];simpl;split;
          intros (m&hl&[hsat|hsat]);
          try ((assert (h: exists m, list_lift (gnl_theo_sat r) l (Word_to_list m) /\
                                       m |=( ka )= gnl_reg_proj o g1)
                 by ((now exists m;split;[assumption|apply hsat])
                     ||(apply IHe1||apply IHe2;exists m;split;[assumption|apply hsat])))
               ||(assert (h:exists m, list_lift (gnl_theo_sat r) l (Word_to_list m) /\
                                        m |=( ka )= gnl_reg_proj o g2)
                   by ((now exists m;split;[assumption|apply hsat])
                       ||(apply IHe1||apply IHe2;exists m;split;[assumption|apply hsat])))
               || (assert (h:exists m, list_lift (gnl_theo_sat r) l (Word_to_list m) /\
                                         m |=( ka )= ø)
                    by ((now exists m;split;[assumption|apply hsat])
                        ||(apply IHe1;exists m;split;[assumption|apply hsat])
                        ||(apply IHe2;exists m;split;[assumption|apply hsat]))));
          (destruct h as (m'&hl'&hsat');exists m';split;tauto)
          ||(apply IHe1 in h||apply IHe2 in h;destruct h as (m'&hl'&hsat');
             exists m';split;tauto).
    - destruct (o0 =?= o).
      + subst;simpl.
        pose proof (gnl_reg_trad_Clean r o e1) as he1;
          pose proof (gnl_reg_trad_Clean r o e2) as he2;unfold Clean in *.
        destruct (clean_exp e1),(clean_exp e2);simpl;try rewrite eq_dec_eq. 
        * split;intros (m & h1 & h2).
          -- destruct h2 as (m1&m2&h2&hm1&hm2).
             pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
             assert (ih1 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o g)
               by (exists m1;split;auto);apply he1 in ih1 as (m'1&lift1&sat1).
             assert (ih2 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l2 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o g0)
               by (exists m2;split;auto);apply he2 in ih2 as (m'2&lift2&sat2).
             exists (m'1 ** m'2);split;auto.
             ++ simpl;apply app_list_lift;auto.
             ++ exists m'1,m'2;split;auto with proofs.
          -- destruct h2 as (m1&m2&h2&hm1&hm2).
             pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
             simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
             assert (ih1 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o e1)
               by (exists m1;split;auto);apply he1 in ih1 as (m'1&lift1&sat1).
             assert (ih2 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l2 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o e2)
               by (exists m2;split;auto);apply he2 in ih2 as (m'2&lift2&sat2).
             exists (m'1 ** m'2);split;auto.
             ++ simpl;apply app_list_lift;auto.
             ++ exists m'1,m'2;split;auto with proofs.
        * split;[firstorder|].
          intros (m&h1&m1&m2&h2&hm1&hm2);exfalso.
          pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
          assert (ih2 : exists m : Word (GExp A O),
                               list_lift (gnl_theo_sat r) l2 (Word_to_list m)
                               /\ m |=( ka )= gnl_reg_trad o e2)
               by (exists m2;split;auto);apply he2 in ih2 as (m'2&lift2&sat2).
          apply sat2.
        * split;[firstorder|].
          intros (m&h1&m1&m2&h2&hm1&hm2);exfalso.
          pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
          assert (ih1 : exists m : Word (GExp A O),
                     list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                     /\ m |=( ka )= gnl_reg_trad o e1)
            by (exists m1;split;auto);apply he1 in ih1 as (m'1&lift1&sat1).
          apply sat1.
        * split;[firstorder|].
          intros (m&h1&m1&m2&h2&hm1&hm2);exfalso.
          pose proof h2 as E;apply Word_to_list_eq in E;rewrite E in h1;clear E.
          simpl in h1;apply list_lift_app in h1 as (l1&l2&->&hl1&hl2).
          assert (ih1 : exists m : Word (GExp A O),
                     list_lift (gnl_theo_sat r) l1 (Word_to_list m)
                     /\ m |=( ka )= gnl_reg_trad o e1)
            by (exists m1;split;auto);apply he1 in ih1 as (m'1&lift1&sat1).
          apply sat1.
      + simpl;split;[|firstorder].
        pose proof (Clean_is_eq e1) as C1.
        pose proof (Clean_is_eq e2) as C2.
        unfold Clean in *.
        destruct (clean_exp e1),(clean_exp e2);simpl;auto.
        rewrite eq_dec_neq by assumption;simpl;tauto.
    - destruct (o0 =?= o);subst.
      + pose proof (gnl_reg_trad_Clean r o (e ×{o} (e^{o}))) as he.
        unfold Clean in he;simpl in he;repeat rewrite eq_dec_eq in he.
        destruct (clean_exp e);simpl in *;repeat rewrite eq_dec_eq in *. 
        * split;intros (m&h1&[h2|h2]).
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_proj o g)
               by (exists m;split;assumption). 
             apply IHe in ih as (m'&lift&sat).
             exists m';repeat split;auto.
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o g @@ (gnl_reg_trad o g) ^+)
               by (exists m;split;assumption). 
             apply he in ih as (m'&lift&sat).
             exists m';repeat split;auto.
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_proj o e)
               by (exists m;split;assumption). 
             apply IHe in ih as (m'&lift&sat).
             exists m';repeat split;auto.
             now left.
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o e @@ (gnl_reg_trad o e) ^+)
               by (exists m;split;assumption). 
             apply he in ih as (m'&lift&sat).
             exists m';repeat split;auto;now right.
        * split;[firstorder|].
          intros (m&h1&[h2|h2]);exfalso.
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_proj o e)
               by (exists m;split;assumption). 
             apply IHe in ih as (m'&lift&sat).
             apply sat.
          -- assert (ih : exists m : Word (GExp A O),
                        list_lift (gnl_theo_sat r) l (Word_to_list m)
                        /\ m |=( ka )= gnl_reg_trad o e @@ (gnl_reg_trad o e) ^+)
               by (exists m;split;assumption). 
             apply he in ih as (m'&lift&sat).
             apply sat.
      + pose proof (Clean_is_eq e) as C;unfold Clean in C.
        destruct (clean_exp e);simpl;try rewrite eq_dec_neq by assumption.
        * apply IHe.
        * split;[firstorder|].
          intros (m&h1&h2);exfalso.
          assert (ih : exists m : Word (GExp A O),
                     list_lift (gnl_theo_sat r) l (Word_to_list m)
                     /\ m |=( ka )= gnl_reg_proj o e)
            by (exists m;split;assumption). 
          apply IHe in ih as (m'&lift&sat).
          apply sat.
  Qed.

  (** With this out of the way, we easily show that the new semantic relation bewteen *)
  (** decompositions and expressions is equivalent to the old one. *)
  
  Corollary gnl_clean_decomp_sat_id r s e :
    gnl_clean_decomp_sat r s e <-> gnl_decomp_sat r s e.
  Proof.
    destruct s as [|(o,l)];simpl;[tauto|].
    rewrite <- gnl_reg_proj_Clean.
    cut (KA |- Clean (gnl_reg_proj o (Clean e)) == gnl_reg_proj o (Clean e)).
    - intros E;setoid_rewrite E;reflexivity.
    - generalize (Clean e);intro g.
      pose proof (Clean_is_eq (gnl_reg_proj o g)) as (h1&h2).
      apply (Empty_implies_any_theory KA) in h1,h2.
      split;auto.
  Qed.

  (** We thus recover the semantic correspondance theorem. *)
  
  Theorem gnl_clean_semantic_correspondance :
    forall s (e : gnl_exp),
      gnl_clean_decomp_sat Ø s e <-> exists t, gnl_decomp_eq Ø s (gnl_decompose t)
                                          /\ t |=(Ø)= e.
  Proof. setoid_rewrite gnl_clean_decomp_sat_id;apply gnl_semantic_correspondance. Qed.

  (** ** Subexpressions and subterms *)
  
  Definition sub_expr : relation (GExp A O) :=
    fun e f => exists o, In (Some e) (gnl_support (Clean (gnl_reg_proj o (Clean f)))).

  Lemma sub_expr_implies_is_deep_clean e f : sub_expr e f -> is_deep_clean e = true.
  Proof.
    unfold sub_expr;intros (o&h).
    apply clean_incl_support in h.
    cut (forall e f, In (Some e) (gnl_support (gnl_reg_trad o (Clean f))) -> is_deep_clean e = true).
    - intros htrad;induction f;simpl in h.
      + tauto.
      + tauto.
      + clear htrad;unfold Clean in *;simpl in *.
        destruct (clean_exp f1),(clean_exp f2);simpl in *;
          try rewrite in_app_iff in *;tauto.
      + unfold Clean in *;simpl in *.
        pose proof (htrad e f1) as hf1.
        pose proof (htrad e f2) as hf2;clear htrad.
        destruct (clean_exp f1),(clean_exp f2);simpl in *;try tauto.
        destruct (o0 =?= o);simpl in *;[|tauto].
        apply in_app_iff in h as [h|h];[apply hf1|apply hf2];apply h.
      + unfold Clean in *;simpl in *.
        pose proof (htrad e f) as hf;clear htrad.
        destruct (clean_exp f);simpl in *;try tauto.
        destruct (o0 =?= o);simpl in *;[|tauto].
        repeat apply in_app_iff in h as [h|h];tauto.
    - clear h e f;intros e f;induction f;simpl.
      + tauto.
      + intros [E|F];[inversion E;subst;simpl|];tauto.
      + unfold Clean in *;simpl in *.
        destruct (clean_exp f1),(clean_exp f2);simpl in *;
          try rewrite in_app_iff in *;tauto.
      + unfold Clean;simpl.
        destruct (clean_cases f1) as [(->&h1)|(g1&->&h1&D1)],
            (clean_cases f2) as [(->&h2)|(g2&->&h2&D2)];simpl;try tauto.
        destruct (o0 =?= o);simpl in *.
        * intros h;apply in_app_iff in h as [h|h];[apply IHf1;rewrite h1|apply IHf2;rewrite h2];
            assumption.
        * intros [E|F];[inversion E;subst;simpl|tauto].
          rewrite D1,D2;reflexivity.
      + unfold Clean;simpl in *.
        destruct (clean_cases f) as [(->&h)|(g&->&h&D)];simpl;try tauto.
        destruct (o0 =?= o);simpl in *.
        * subst;auto. 
        * rewrite in_app_iff;intros [h'|[h'|h']];subst;auto.
          inversion h';subst;clear h';simpl.
          rewrite D;reflexivity.
  Qed.

  Definition sub_term (s t : GTerm A O) :=
    match gnl_decompose t with
    | inl _ => False
    | inr (_,l) => In s l
    end.

  (* Lemma sub_expr_sat e f :
    sub_expr e f -> exists s t, s |=(Ø)= e /\ sub_term s t /\ t |=(Ø)= f.
  Proof.
    intro hyp.
    pose proof hyp as V;apply sub_expr_implies_is_deep_clean in V.
    destruct (deep_clean_sat e V) as (t&ht).
    destruct hyp as (o&h).
    apply clean_support_sat_iff in h as (s&hsat&hIn);[|apply Clean_is_clean].
    rewrite Clean_is_eq in hsat.

    
    cut(exists l, list_lift (gnl_theo_sat Ø) l (Word_to_list s) /\ In t l).
    - intros (l&h1&h2).

      intro h;ax
    intros (o&h).
  Qed. *)
End gnl_decomp.

  (* Lemma KA_sat_gnl_sat_trad  (o : O) (l : list (GTerm A O)) m e : *)
  (*   m |=(ka)= gnl_reg_trad o e -> list_lift (gnl_theo_sat Ø) l (Word_to_list m) -> *)
  (*   exists s', GProd o l = Some s' /\ s' |=(Ø)= e. *)
  (* Proof. *)
  (*   revert l m;induction e;simpl;try destruct (o0 =?= o). *)
  (*   - tauto. *)
  (*   - intros l m E h. *)
  (*     apply Word_to_list_eq in E;rewrite E in h. *)
  (*     destruct l as [|?[]];(exfalso;apply h)||destruct h as (h&_). *)
  (*     exists g;simpl;auto. *)
  (*   - intros l m [h1|h1] h2; *)
  (*       (eapply IHe1 in h1;[|eassumption]) *)
  (*       ||(eapply IHe2 in h1;[|eassumption]); *)
  (*       destruct h1 as (s'&h1&h3);exists s';tauto. *)
  (*   - subst;intros l m (m1&m2&E&hm1&hm2) h2. *)
  (*     apply Word_to_list_eq in E;rewrite E in h2;simpl in h2. *)
  (*     apply list_lift_app in h2 as (l1&l2&->&hl1&hl2). *)
  (*     eapply IHe1 in hm1 as (s1&hm1&hs1);[|eassumption]. *)
  (*     eapply IHe2 in hm2 as (s2&hm2&hs2);[|eassumption]. *)
  (*     destruct (GProd_app Ø o l1 l2 s1 s2) as (s'&E1&E2);auto. *)
  (*     exists s';split;auto. *)
  (*     exists s1,s2;split;auto. *)
  (*   - intros l m E h. *)
  (*     apply Word_to_list_eq in E;rewrite E in h. *)
  (*      destruct l as [|?[]];(exfalso;apply h)||destruct h as (h&_). *)
  (*     exists g;split;auto. *)
  (*   - subst;intros l m (m1&L&h1&E&hL) h2. *)
  (*     apply Word_to_list_eq in E;rewrite E in h2;clear m E. *)
  (*     revert l m1 h1 h2 hL;induction L;[discriminate|]. *)
  (*     destruct (L =?= []);[subst;clear IHL|apply (GProd_Some _ •) in n as (t&ht)]; *)
  (*       simpl;intros;try rewrite ht in h1;inversion h1;clear h1;subst. *)
  (*     + destruct (IHe l m1) as (s'&hs'1&hs'2);auto. *)
  (*       exists s';split;auto. *)
  (*       exists s',[s'];repeat split;auto with proofs. *)
  (*       intros ? [<-|F];[|exfalso];auto. *)
  (*     + simpl in h2;apply list_lift_app in h2 as (l1&l2&->&hl1&hl2). *)
  (*       destruct (IHe l1 a) as (s1&es1&hs1);auto. *)
  (*       destruct (IHL l2 t) as (s2&es2&s'&L'&hs'&hs2&hL');auto. *)
  (*       destruct (GProd_app Ø _ _ _ _ _ es1 es2) as (T&hT1&hT2). *)
  (*       exists T;split;auto. *)
  (*       exists (s1 -[o]- s'),(s1::L');simpl;rewrite hs';repeat split;auto. *)
  (*       * rewrite hT2,hs2;reflexivity. *)
  (*       * intros ? [<-|h];[|apply hL'];auto. *)
  (*   - intros l m [hm| E] hl. *)
  (*     + eapply IHe in hm;eauto. *)
  (*       destruct hm as (s'&Es'&hs'). *)
  (*       exists s';split;auto. *)
  (*       exists s',[s'];repeat split;auto with proofs. *)
  (*       intros ? [<-|F];[apply hs'|exfalso;apply F]. *)
  (*     + apply Word_to_list_eq in E;rewrite E in hl. *)
  (*       destruct l as [|?[]];(exfalso;apply hl)||destruct hl as (h&_). *)
  (*       exists g;split;auto. *)
  (*       destruct h as (t1&t'&E1&ht1&t2&L&E2&E3&hL). *)
  (*       setoid_rewrite E1;setoid_rewrite E3. *)
  (*       exists (t_prod o0 t1 t2),(t1::L);simpl;rewrite E2;repeat split;auto with proofs. *)
  (*       intros ? [<-|F];[apply ht1|apply hL,F]. *)
  (* Qed. *)
  
  (* Lemma KA_sat_gnl_sat_proj  (o : O) (l : list (GTerm A O)) m e : *)
  (*   m |=(ka)= gnl_reg_proj o e -> list_lift (gnl_theo_sat Ø) l (Word_to_list m) -> *)
  (*   exists s', GProd o l = Some s' /\ s' |=(Ø)= e. *)
  (* Proof. *)
  (*   revert l m ;induction e;simpl;try destruct (o0 =?= o);subst;try tauto. *)
  (*   - intros l m h1 h2;try destruct h1 as [h1|h1]; *)
  (*       (eapply IHe1 in h1;[|eassumption]) *)
  (*       ||(eapply IHe2 in h1;[|eassumption]); *)
  (*       destruct h1 as (s'&h1&h3);exists s';tauto. *)
  (*   - intros l m h1 h2. *)
  (*     destruct h1 as (m1&m2&E&hm1&hm2). *)
  (*     apply Word_to_list_eq in E;rewrite E in h2;simpl in h2. *)
  (*     apply list_lift_app in h2 as (l1&l2&->&hl1&hl2). *)
  (*     destruct (KA_sat_gnl_sat_trad o l1 m1 e1) as (s1&E1&hs1);auto. *)
  (*     destruct (KA_sat_gnl_sat_trad o l2 m2 e2) as (s2&E2&hs2);auto. *)
  (*     destruct (GProd_app Ø o l1 l2 s1 s2) as (s'&E3&E4);auto. *)
  (*     exists s';split;auto. *)
  (*     subst;exists s1,s2;repeat split;auto with proofs. *)
  (*   - subst;simpl;intros l m hm hl; *)
  (*       try destruct hm as [hm|hm]; *)
  (*       try (eapply IHe in hm as (s'&hm&hs');[|reflexivity|eassumption]; *)
  (*            exists s';split;auto; *)
  (*            exists s',[s'];simpl;repeat split;auto with proofs; *)
  (*            intros ? [<-|F];[apply hs'|exfalso;apply F]); *)
  (*       try destruct hm as (m1&m'&->&hm1&m2&m3&->&hm2&L&->&hL); *)
  (*       try apply list_lift_app in hl as (l1&l'&->&hl1&hl2); *)
  (*       try apply list_lift_app in hl2 as (l2&l3&->&hl2&hl3). *)
  (*     tauto. *)
  (*   - intros l m h1 h2. *)
  (*     destruct h1 as [h1|h1]. *)
  (*     + eapply IHe in h1 as (s&h1&h3);[|eassumption]. *)
  (*       exists s;split;auto. *)
  (*       exists s,[s];repeat split;auto with proofs. *)
  (*       intros ? [<-|F];[assumption|exfalso;apply F]. *)
  (*     + cut (m |=(ka)= gnl_reg_trad o (e^{o}));[clear h1;intro h1|]. *)
  (*       * eapply KA_sat_gnl_sat_trad in h1 as (s'&h3&s''&L&h4&h5&h6);[|apply h2]. *)
  (*         exists s';split;auto. *)
  (*         exists s'',L;repeat split;auto. *)
  (*       * simpl;rewrite eq_dec_eq. *)
  (*         destruct h1 as (m1&?&E1&h1&m2&L&E2&h3&h4). *)
  (*         exists (m1**m2),(m1::L);simpl;rewrite E2;repeat split;eauto with proofs. *)
  (*         intros ? [<-|h];[|apply h4];auto. *)
  (*   - intros l m  hm hl. *)
  (*     destruct (IHe l m hm hl) as (s'&hl'&hs'). *)
  (*     exists s';split;auto. *)
  (*     exists s',[s'];repeat split;auto with proofs. *)
  (*     intros ? [<-|F];[assumption|exfalso;apply F]. *)
  (* Qed. *)
