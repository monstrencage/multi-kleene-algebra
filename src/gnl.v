(** * gnl_alg.gnl : General expressions *)
Require Import prelim.

Section gnl.
  (** * Definitions *)

  (** General expressions are parametrized by a set [X] of _variables_ *)
  (** and a set [O] of _operators_. *)

  Context {X O : Set} {decX: decidable_set X} {decO: decidable_set O} .

  (** They are built from the constant [ø] and the variables from [X] using *)
  (** the binary operators [+] and [×{o}], the second being parametrized by *)
  (** an operator [o] from [O]. They may also feature a repetition construct *)
  (** [^{o}] for every operator [o]. *)

  Inductive gnl_exp : Set :=
  | zero : gnl_exp
  | var : X -> gnl_exp
  | sum : gnl_exp -> gnl_exp -> gnl_exp
  | prod : O -> gnl_exp -> gnl_exp -> gnl_exp
  | iter : O -> gnl_exp -> gnl_exp.

  Notation ø := zero.
  Infix "+" := sum.
  Infix " ×{ i } " := (prod i) (at level 20).
  Notation " e ^{ i }" := (iter i e).

  (** Provided [X] and [O] are decidable, the set of general expressions is decidable. *)
  Global Instance dec_gnl_exp : decidable_set gnl_exp.
  Proof.
    intro e;induction e;intros [];try (right;discriminate).
    - left;reflexivity.
    - destruct (x =?= x0);[left;subst;reflexivity|right;intro E;inversion E;tauto].
    - destruct (IHe1 g).
      + destruct (IHe2 g0).
        * subst;left;reflexivity.
        * right;intro E;inversion E;tauto.
      + right;intro E;inversion E;tauto.
    - destruct (o =?= o0).
      + destruct (IHe1 g).
        * destruct (IHe2 g0).
          -- subst;left;reflexivity.
          -- right;intro E;inversion E;tauto.
        * right;intro E;inversion E;tauto.
      + right;intro E;inversion E;tauto.
    - destruct (o =?= o0).
      + destruct (IHe g).
        * subst;left;reflexivity.
        * right;intro E;inversion E;tauto.
      + right;intro E;inversion E;tauto.
  Qed.

  (** We now define a crucial element of this development : the relation [r |- e ≤ f], *)
  (** where [r] is a relation between general expressions, called a _theory_, and [e] *)
  (** and [f] are general expressions. *)

  Reserved Notation " r |- e ≤ f " (at level 60).
  
  Inductive gnl_theo_inf (r : relation gnl_exp) : relation gnl_exp :=
  (** As a preorder, this relation is always reflexive and transitive. *)
  | gnl_theo_inf_refl e :
    r |- e ≤ e
  | gnl_theo_inf_trans e f g :
    r |- e ≤ f -> r |- f ≤ g -> r |- e ≤ g
  (** Products and iterators are monotone. *)
  | gnl_theo_inf_prod i e1 e2 f1 f2 :
    r |- e1 ≤ e2 -> r |- f1 ≤ f2 -> r |- e1 ×{i} f1 ≤ e2 ×{i}f2
  | gnl_theo_inf_iter i e1 e2 :
    r |- e1 ≤ e2 -> r |- e1^{i} ≤ e2^{i}
  (** [+] is a join operator w.r.t. this preorder. *)
  | gnl_theo_inf_join_l e1 e2 :
    r |- e1 ≤ e1 + e2
  | gnl_theo_inf_join_r e1 e2 :
    r |- e2 ≤ e1 + e2
  | gnl_theo_inf_join e1 e2 e3 :
    r |- e1 ≤ e3 -> r |- e2 ≤ e3 -> r |- e1 + e2 ≤ e3
  (** [ø] is a minimum. *)
  | gnl_theo_inf_zero e :
    r |- ø ≤ e
  (** Products are associative. *)
  | gnl_theo_inf_prod_assoc1 i e f g :
    r |- e ×{i} (f ×{i} g) ≤ (e ×{i} f) ×{i} g
  | gnl_theo_inf_prod_assoc2 i e f g :
    r |- (e ×{i} f) ×{i} g ≤ e ×{i} (f ×{i} g)
  (** Products distribute over sums. *)
  | gnl_theo_inf_prod_sum i e f g:
    r |- e ×{i} (f + g) ≤ e ×{i} f + e ×{i} g
  | gnl_theo_inf_sum_prod i e f g :
    r |- (e + f) ×{i} g ≤ e ×{i} g + f ×{i} g
  (** [ø] is a zero (annihilator) w.r.t. the products. *)
  | gnl_theo_inf_prod_e_zero i e :
    r |- e ×{i} ø ≤ ø
  | gnl_theo_inf_prod_zero_e i e :
    r |- ø ×{i} e ≤ ø
  (** Iterators may be unfolded on both sides. *)
  | gnl_theo_inf_iter_unfold_left i e :
    r |- e + e ×{i} (e^{i}) ≤ e^{i}
  | gnl_theo_inf_iter_unfold_right i e :
    r |- e + e^{i} ×{i} e ≤ e^{i}
  (** This relation is stable under four induction axioms : two for each side. *)
  | gnl_theo_inf_iter_left_ind i e f :
    r |- e ×{i} f ≤ f -> r |- e^{i} ×{i} f ≤ f
  | gnl_theo_inf_iter_right_ind i e f :
    r |- f ×{i} e ≤ f -> r |- f ×{i} (e^{i}) ≤ f
  | gnl_theo_inf_iter_left_ind_bis i e f :
    r |- e + e ×{i} f ≤ f -> r |- e^{i} ≤ f
  | gnl_theo_inf_iter_right_ind_bis i e f :
    r |- e + f ×{i} e ≤ f -> r |- e^{i} ≤ f
  (** Finally, the theory [r] is included in this relation. *)
  | gnl_theo_axiom e f :
    r e f -> r |- e ≤ f
  where " r |- e ≤ f " := (gnl_theo_inf r e f).

  Hint Constructors gnl_theo_inf : proofs.

  (** We define a corresponding equivalence relation. *)
  
  Definition gnl_theo_eq r := fun e f => r |- e ≤ f /\ r |- f ≤ e.

  Notation " r |- e == f " := (gnl_theo_eq r e f) (at level 60).

  (** * First properties *)
  
  (** As promised, for every theory the relation [r |- _ ≤ _] is a preorder, and *)
  (** the relation [r |- _ == _ ] is an equivalence relation. *)
  
  Global Instance gnl_theo_inf_preorder r : PreOrder (gnl_theo_inf r).
  Proof.
    split.
    - intros e;auto with proofs.
    - intros e f g h1 h2.
      eauto with proofs.
  Qed.
  
  Global Instance gnl_theo_eq_equiv r : Equivalence (gnl_theo_eq r).
  Proof.
    split;intro;intros;split;auto with proofs.
    - destruct H;auto.
    - destruct H;auto.
    - destruct H, H0;eauto with proofs.
    - destruct H, H0;eauto with proofs.
  Qed.

  Global Instance gnl_theo_PartialOrder r :
    PartialOrder (gnl_theo_eq r) (gnl_theo_inf r).
  Proof. intros e f;unfold Basics.flip, gnl_theo_eq;split;intros (h1&h2);split;assumption. Qed.

  Lemma r_contained_in_gnl_theo_inf_r r : subrelation r (gnl_theo_inf r).
  Proof. intros ? ? ?;auto with proofs. Qed.

  Lemma gnl_theo_inf_mono r1 r2 :
    subrelation r1 (gnl_theo_inf r2) -> subrelation (gnl_theo_inf r1) (gnl_theo_inf r2).
  Proof. intros hyp ? ? pr;induction pr;eauto with proofs. Qed.
  
  (** Every product, every iterator, as well as the sum, is monotone with respect *)
  (** to the preorder associated with any theory. *)
  
  Global Instance prod_mono r (o : O) :
    Proper (gnl_theo_inf r ==> gnl_theo_inf r ==> gnl_theo_inf r) (prod o).
  Proof. intros e e' he f f' hf;auto with proofs. Qed.

  Lemma gnl_theo_inf_sum r e1 e2 f1 f2 :
    r |- e1 ≤ e2 -> r |- f1 ≤ f2 -> r |- e1 + f1 ≤ e2 + f2.
  Proof. intros h1 h2;apply gnl_theo_inf_join;etransitivity;eauto with proofs. Qed.

  Hint Resolve gnl_theo_inf_sum : proofs.

  Global Instance sum_mono r :
    Proper (gnl_theo_inf r ==> gnl_theo_inf r ==> gnl_theo_inf r) sum.
  Proof. intros e e' he f f' hf;auto with proofs. Qed.

  Global Instance iter_mono r o :
    Proper (gnl_theo_inf r ==> gnl_theo_inf r) (iter o).
  Proof. intros s s' es;auto with proofs. Qed.

  (** The following algebraic properties are easily derived, and are handy to have. *)
  Lemma gnl_theo_inf_sum_left r e f g :
    r |- e ≤ f -> r |- e ≤ f + g.
  Proof. intros ->;apply gnl_theo_inf_join_l. Qed.
  Lemma gnl_theo_inf_sum_right r e f g :
    r |- e ≤ g -> r |- e ≤ f + g.
  Proof. intros ->;apply gnl_theo_inf_join_r. Qed.
  Lemma gnl_theo_eq_prod_assoc r i e f g :
    r |- e ×{i} (f ×{i} g) == prod i (e ×{i} f) g.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_prod_sum r i e f g:
    r |- e ×{i} (f + g) == e ×{i} f + e ×{i} g.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_sum_prod r i e f g :
    r |- (e + f) ×{i} g == e ×{i} g + f ×{i} g.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_prod_e_zero r i e :
    r |- e ×{i} ø == ø.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_prod_zero_e r i e :
    r |- ø ×{i} e == ø.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_iter_unfold_left r i e :
    r |- e^{i} == e + e ×{i} (e^{i}).
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_iter_unfold_right r i e :
    r |- e^{i} == e + prod i (e^{i}) e.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_sum_assoc r e f g :
    r |- e + (f + g) == (e + f) + g.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_sum_zero_e r e :
    r |- ø + e == e.
  Proof. split;repeat apply gnl_theo_inf_join;eauto with proofs. Qed.
  Lemma gnl_theo_eq_sum_e_zero r e:
    r |- e + ø == e.
  Proof. split;repeat apply gnl_theo_inf_join;auto with proofs. Qed.

  (** * General terms *)

  (** General terms are simply built out of variables and binary products, *)
  (** parametrized by an operator. *)

  Inductive gnl_term : Set :=
  | t_var : X -> gnl_term
  | t_prod : O -> gnl_term -> gnl_term -> gnl_term.

  Infix " -[ i ]-  " := (t_prod i) (at level 20).
  
  (** This set is decidable as long as both the set of varibles and the set of *)
  (** operators are decidable. *)
    
  Global Instance gnl_terms_dec : decidable_set gnl_term.
  Proof.
    intro s;induction s;intros [];try (right;discriminate).
    - destruct (x =?= x0).
      + subst;now left.
      + right;intro E;inversion E;tauto.
    - destruct (o =?= o0);[|right;intro E;inversion E;tauto].
      destruct (IHs1 g);[|right;intro E;inversion E;tauto].
      destruct (IHs2 g0);[|right;intro E;inversion E;tauto].
      subst;now left.
  Qed.

  (** Terms are considered up-to associativity of the products, as well as a *)
  (** theory (binary relation over terms) [r]. To that end, we define the *)
  (** following relation. *)

  Reserved Notation " r |- s =T= t " (at level 60). 
  
  Inductive gnl_term_theo_eq r : relation gnl_term :=
  (** It is defined as an equivalence relation *)
  | gnlt_refl e :
    r |- e =T= e
  | gnlt_sym e f :
    r |- e =T= f -> r |- f =T= e
  | gnlt_trans e f g :
    r |- e =T= f -> r |- f =T= g -> r |- e =T= g
  (** and a structural congruence *)
  | gnlt_prod o e1 e2 f1 f2 :
    r |- e1 =T= e2 -> r |- f1 =T= f2 ->
    r |- e1 -[o]- f1 =T= e2 -[o]- f2
  (** for which the products are associative *)
  | gnlt_prod_assoc o e f g :
    r |- e -[ o ]- (f -[ o ]- g) =T= (e -[ o ]- f) -[ o ]- g
  (** and which includes the theory [r]. *)
  | gnlt_axiom e f :
    r e f -> r |- e =T= f
  where " r |- s =T= t " := (gnl_term_theo_eq r s t).
  
  Hint Constructors gnl_term_theo_eq : proofs.

  (** The following result witness some of the properties of the relation we mention above. *)

  Global Instance gnl_term_eq_equiv r : Equivalence (gnl_term_theo_eq r).
  Proof. split;intro;intros;eauto with proofs. Qed.

  Global Instance t_prod_proper r i :
    Proper (gnl_term_theo_eq r ==> gnl_term_theo_eq r ==> gnl_term_theo_eq r) (t_prod i).
  Proof. intros s s' es t t' et;apply gnlt_prod;assumption. Qed.

  Global Instance gnl_term_theo_subrelation rT :
    subrelation rT (gnl_term_theo_eq rT).
  Proof. intros e f h;auto with proofs. Qed.
  
  (** If a theory is included in another, then its corresponding equivalence is included *)
  (** in the one associated with the larger theory. *)
  
  Global Instance gnl_term_theo_impl_eq rT1 rT2 :
    subrelation rT1 (gnl_term_theo_eq rT2) ->
    subrelation (gnl_term_theo_eq rT1) (gnl_term_theo_eq rT2).
  Proof. unfold id;intros hyp s t pr;induction pr;simpl;eauto with proofs. Qed.

  (** * General products *)
  (** General products are indexed by operators. They use their operator to bind together a *)
  (** list of general terms. Unfortunately, since general terms lack a unit, the product of *)
  (** the empty list is undefined. For that reason the return type of the general product is *)
  (** an option type. *)

  Fixpoint GProd (o : O) (l : list gnl_term) : option gnl_term:=
    match l with
    | [] => None
    | s::l => match (GProd o l) with
              | None => Some s
              | Some t => Some (s -[o]- t)
              end
    end.

  (** The general product is monotone, in the following sense : *)
  
  Global Instance GProd_proper r o :
    Proper (list_lift (gnl_term_theo_eq r) ==> or_none (gnl_term_theo_eq r)) (GProd o).
  Proof.
    intros l;induction l as [|e l];intros [|f m];simpl;try tauto.
    intros (h1&h2).
    apply IHl in h2.
    destruct (GProd o l),(GProd o m);try (exfalso;apply h2);simpl in *.
    - rewrite h1,h2;reflexivity.
    - assumption.
  Qed.

  (** Because every operator is considered associative, we may compute the general *)
  (** product of a concatenation of lists by taking the product of the general products *)
  (** of the argument lists (up-to any theory [r]). *)
  
  Lemma GProd_app r :
    forall o (l1 l2 : list gnl_term) (t1 t2 : gnl_term),
      GProd o l1 = Some t1 ->
      GProd o l2 = Some t2 ->
      exists t : gnl_term, GProd o (l1 ++ l2) = Some t /\ r |- t =T= t1 -[o]- t2.
  Proof.
    induction l1;simpl;[discriminate|].
    case_eq (GProd o l1); [intros g Eg|intro Eg];rewrite Eg in *.
    - intros l2 t1 t2 ht1 ht2.
      destruct (IHl1 l2 g t2) as (t&->&h);auto.
      exists (t_prod o a t);split;auto.
      inversion ht1.
      rewrite <- gnlt_prod_assoc.
      apply gnlt_prod;auto with proofs.
    - intros l2 t1 t2 ht1 ht2;clear IHl1.
      destruct l1;[|simpl in Eg;destruct (GProd o l1);discriminate].
      simpl;inversion ht1;subst;clear ht1;rewrite ht2.
      exists (t_prod o t1 t2);split;auto with proofs.
  Qed.

  (** The empty list is the only list of terms on which the general product is undefined. *)

  Lemma GProd_None (l : list gnl_term) o :
    GProd o l = None <-> l = [].
  Proof. destruct l;[|simpl;destruct (GProd o l)];simpl;split;reflexivity||discriminate. Qed.

  (** A corollary states that the general product of any non-empty list is well defined. *)
  
  Corollary GProd_Some (l : list gnl_term) o :
    l <> [] -> exists t, GProd o l = Some t.
  Proof.
    case_eq (GProd o l);[intros g E;exists g;reflexivity|intros F hl;exfalso].
    rewrite GProd_None in F;tauto.
  Qed.

  (** * The satisfaction relation *)
 
  (** We define a satisfaction relation up-to a theory [r] on terms. *)
  
  Reserved Notation " s |=( r )= e " (at level 60).
  
  Fixpoint gnl_theo_sat (r : relation gnl_term) (s : gnl_term) (e : gnl_exp) :=
    match e with
    (** [ø] is satisfied by no-one. *)
    | ø =>
        False
    (** [var a] is satisfied by terms [r]-equivalent to [t_var a]. *)
    | var a =>
        r |- s =T= t_var a
    (** Unions are satisfied by terms satisfying one of the disjuncts. *)
    | e + f =>
        s |=(r)= e \/ s |=(r)= f
    (** Product are statisfied by terms [r]-equivalent to the product of terms satifisfying *)
    (** each factor. *)
    | e1 ×{o} e2 =>
        exists s1 s2, r |- s =T= s1 -[o]- s2
                      /\ s1 |=(r)= e1
                      /\ s2 |=(r)= e2
    (** Iterators are satisfied by products of terms satisfying the argument expression. *)
    | iter o e =>
        exists s' L, GProd o L = Some s'
                     /\ r |- s =T= s'
                     /\ forall s'', In s'' L -> s'' |=(r)= e 
    end
  where " s |=( r )= e " := (gnl_theo_sat r s e).

  (** A weaker theory gives rise to a weaker satisfaction relation (in other words the predicate *)
  (** [gnl_teho_sat] is monotone in its first argument. *)
  
  Lemma gnl_theo_sat_subrelation (r s : relation gnl_term) :
    subrelation r (gnl_term_theo_eq s) -> forall e t, t |=(r)= e -> t |=(s)=e.
  Proof.
    intros sub e;induction e;simpl;intros t h;auto.
    - rewrite h;reflexivity.
    - firstorder.
    - destruct h as (s1&s2&h1&h2&h3).
      exists s1,s2;repeat split;auto.
      rewrite h1;reflexivity.
    - destruct h as (s'&L&h1&h2&h3).
      exists s',L;repeat split;auto.
      rewrite h2;reflexivity.
  Qed.
  
  (** [r]-equivalent terms are indistinguishable by the satisfaction relation. *)
  
  Global Instance gnl_theo_sat_proper_aux (r : relation gnl_term) :
    Proper (gnl_term_theo_eq r ==> eq ==> iff) (gnl_theo_sat r).
  Proof.
    intros s t hs e ? <-.
    revert s t hs;induction e;simpl.
    + tauto.
    + intuition.
      * rewrite <- hs;assumption.
      * rewrite hs;assumption.
    + intuition.
      * rewrite IHe1 in H0 by eassumption;tauto.
      * rewrite IHe2 in H0 by eassumption;tauto.
      * rewrite IHe1 in H0 by (symmetry;eassumption);tauto.
      * rewrite IHe2 in H0 by (symmetry;eassumption);tauto.
    + intros s t hs.
      setoid_rewrite hs.
      reflexivity.
    + intros s t hs.
      setoid_rewrite hs.
      reflexivity.
  Qed.

  (** If a theory [rG] is sound with respect to a satisfaction relation [|=(rT)=], then *)
  (** the preorder [rG |- _ ≤ _] is also sound w.r.t. the same satisfaction relation. *)
  
  Global Instance gnl_theo_sat_proper rT rG :
    (forall s, Proper (rG ==> Basics.impl) (gnl_theo_sat rT s)) ->
    Proper (gnl_term_theo_eq rT ==> gnl_theo_inf rG ==> Basics.impl) (gnl_theo_sat rT).
  Proof.
    pose proof (gnl_theo_sat_proper_aux rT) as h1.
    intros h2;cut (Proper (gnl_term_theo_eq rT ==> rG ==> Basics.impl) (gnl_theo_sat rT));
      [clear h1 h2;
       unfold Basics.impl;intros h_axioms s t hs e f he;
       intros h;cut (gnl_theo_sat rT t e);
       [|eapply gnl_theo_sat_proper_aux,h;[symmetry;apply hs|reflexivity]];
       clear s hs h;
       revert t;induction he;simpl;intro t;auto;try (now intuition)||(now firstorder)|].
    - intros (s1&s2&h1&h3&s3&s4&h5&h6&h7).
      exists (t_prod i s1 s3),s4.
      rewrite h1,h5.
      repeat split;auto with proofs.
      exists s1,s3;repeat split;auto with proofs.
    - intros (s1&s2&h1&(s3&s4&h5&h6&h7)&h2).
      exists s3,(t_prod i s4 s2).
      rewrite h1,h5.
      repeat split;auto with proofs.
      exists s4,s2;repeat split;auto with proofs.
    - intros [h|(s1&s2&h1&h2&s'&L&h3&h4&h5)].
      + exists t,[t];repeat split;auto with proofs.
        intros ? [<-|F];[|exfalso];auto.
      + exists (t_prod i s1 s'),(s1::L).
        rewrite h1,h4;repeat split;auto with proofs.
        * simpl;rewrite h3;reflexivity.
        * intros ? [<-|h];[|apply h5];auto.
    - intros [h|(s1&s2&h1&(s'&L&h3&h4&h5)&h2)].
      + exists t,[t];repeat split;auto with proofs.
        intros ? [<-|F];[|exfalso];auto.
      + assert (h6: GProd i [s2] = Some s2) by reflexivity.
        destruct (GProd_app rT i _ _ _ _ h3 h6) as (T&h7&h8).
        exists T,(L++[s2]).
        repeat split;auto.
        * rewrite h1,h4,h8;reflexivity.
        * intros ?;rewrite in_app_iff;intros [h|[<-|F]];[apply h5| |exfalso];auto.
    - intros (s1&s2&h1&(s'&L&h2&h3&h4)&h5).
      revert s' t s1 s2 h1 h2 h3 h4 h5;induction L;[discriminate|].
      destruct (L =?= []).
      + subst.
        intros;inversion h2;subst;clear h2.
        rewrite h3 in h1.
        apply IHhe.
        exists s',s2;repeat split;auto.
        apply h4;now left.
      + apply (GProd_Some _ i) in n as (T&hT);intros.
        simpl in h2;rewrite hT in h2;inversion h2;subst;clear h2.
        apply IHhe.
        exists a,(T -[i]- s2).
        rewrite h1,h3;repeat split;auto with proofs.
        * apply h4;now left.
        * eapply IHL;eauto;try reflexivity.
          intros;apply h4;now right.
    - intros (s1&s2&h1&h5&(s'&L&h2&h3&h4)).
      revert s' t s1 s2 h1 h2 h3 h4 h5.
      apply (@rev_ind _ (fun L => forall s' t s1 s2 : gnl_term,
                             rT |- t =T= s1 -[i]- s2 ->
                                   GProd i L = Some s' ->
                                   rT |- s2 =T= s' ->
                                         (forall s'' : gnl_term, In s'' L -> s''|=(rT)= e) ->
                                         s1 |=(rT)= f -> t |=(rT)= f));
        [discriminate|clear L;intros a L IHL].
      destruct (L =?= []).
      + subst.
        intros s' t s1 s2 h1 h2 h3 h4 h5;inversion h2;subst;clear h2.
        rewrite h3 in h1.
        apply IHhe.
        exists s1,s';repeat split;auto.
        apply h4;now left.
      + apply (GProd_Some _ i) in n as (T&hT);intros s' t s1 s2 h1 h2 h3 h4 h5.
        assert (h6 : GProd i [a] = Some a) by reflexivity.
        destruct (GProd_app rT _ _ _ _ _ hT h6) as (t'&ht'1&ht'2).
        rewrite ht'1 in h2;inversion h2;subst;clear h2.
        rewrite h3,ht'2 in h1.
        apply IHhe.
        exists (t_prod i s1 T),a;rewrite h1;repeat split;auto with proofs.
        * eapply IHL;eauto;try reflexivity.
          intros;apply h4,in_app_iff;now left.
        * apply h4,in_app_iff;now right;left.
    - intros (s'&L&h1&h2&h3).
      revert s' t h1 h2 h3;induction L;[discriminate|].
      destruct (L =?= []).
      + subst.
        intros;inversion h1;subst;clear h1.
        apply IHhe;left.
        eapply gnl_theo_sat_proper_aux,h3;[apply h2|reflexivity|now left]. 
      + apply (GProd_Some _ i) in n as (T&hT);intros.
        simpl in h1;rewrite hT in h1;inversion h1;subst;clear h1.
        apply IHhe.
        right;exists a,T.
        rewrite h2;repeat split;auto with proofs.
        * apply h3;now left.
        * eapply IHL;eauto;try reflexivity.
          intros;apply h3;now right.
    - intros (s'&L&h1&h2&h3).
      revert s' t h1 h2 h3.
      apply (@rev_ind _ (fun L =>
                           forall s' t : gnl_term,
                             GProd i L = Some s' ->
                             rT |- t =T= s' ->
                                   (forall s'' : gnl_term, In s'' L -> s'' |=( rT )= e) ->
                                   t |=( rT )= f));
        [discriminate|clear L;intros a L IHL].
      destruct (L =?= []).
      + subst.
        intros s' t h1 h2 h3;inversion h1;subst;clear h1.
        simpl in *.
        apply IHhe;left.
        eapply gnl_theo_sat_proper_aux,h3;[apply h2|reflexivity|now left]. 
      + apply (GProd_Some _ i) in n as (T&hT);intros s' t h1 h2 h3.
        assert (h6 : GProd i [a] = Some a) by reflexivity.
        destruct (GProd_app rT _ _ _ _ _ hT h6) as (t'&ht'1&ht'2).
        rewrite ht'1 in h1;inversion h1;subst;clear h1.
        rewrite ht'2 in h2.
        apply IHhe;right.
        exists T,a;rewrite h2;repeat split;auto with proofs.
        * eapply IHL;eauto;try reflexivity.
          intros;apply h3,in_app_iff;now left.
        * apply h3,in_app_iff;now right;left.
    - apply h_axioms ;auto with proofs.
    - intros s t Es e f Ee h.
      rewrite <- Es.
      eapply h2;eauto.
  Qed.

  (** If a preorder is sound w.r.t. some satisfaction relation, so is the corresponding *)
  (** equivalence relation. *)
  
  Global Instance gnl_theo_sat_proper_eq (rT : relation gnl_term) rG :
    Proper (gnl_term_theo_eq rT ==> gnl_theo_inf rG ==> Basics.impl) (gnl_theo_sat rT) ->
    Proper (gnl_term_theo_eq rT ==> gnl_theo_eq rG ==> iff) (gnl_theo_sat rT).
  Proof. intros h s t hs e f (he&hf);split;apply h;auto;symmetry; assumption. Qed.

End gnl.

Hint Constructors gnl_theo_inf : proofs.
Hint Constructors gnl_term_theo_eq : proofs.
Hint Resolve gnl_theo_inf_sum : proofs.

Notation ø := zero.
Infix "+" := sum.
Infix " ×{ i } " := (prod i) (at level 20).
Notation " e ^{ i }" := (iter i e).
Infix " -[ i ]-  " := (t_prod i) (at level 20).
Notation " r |- e ≤ f " := (gnl_theo_inf r e f) (at level 60).
Notation " r |- e == f " := (gnl_theo_eq r e f) (at level 60).
Notation " r |- s =T= t " := (gnl_term_theo_eq r s t) (at level 60).
Notation " s |=( r )= e " := (gnl_theo_sat r s e) (at level 60).

Notation GExp := @gnl_exp.
Notation GTerm := @gnl_term.

(** * Empty theories *)

(** We define an empty theory. *)
Definition Empty {X : Set} : relation X := fun _ _ => False.

Notation Ø := Empty.

Global Instance Empty_sat_proper {X O} (s : GTerm X O) :
  Proper (Ø ==> Basics.impl) (gnl_theo_sat Ø s).
Proof. intros ? ? []. Qed.

Lemma Empty_implies_anything {X : Set} (r : relation X) :
  subrelation Ø r.
Proof. intros s t []. Qed.

Global Instance Empty_implies_any_theory {X O: Set} (r : relation (GExp X O)) :
  subrelation (gnl_theo_inf Ø) (gnl_theo_inf r).
Proof. exact (gnl_theo_inf_mono Ø r (Empty_implies_anything (gnl_theo_inf r))). Qed.

Global Instance Empty_implies_any_term_theory {X O : Set} (r : relation (GTerm X O)) :
  subrelation Ø (gnl_term_theo_eq r).
Proof. exact (Empty_implies_anything (gnl_term_theo_eq r)). Qed.

(** Every satisfaction relation can be factored into the corresponding equivalence *)
(** on terms composed with the satisfaction relation associated with the empty theory. *)

Theorem gnl_theo_sat_decompose {X O} (rT : relation (GTerm X O)) s e :
  s |=(rT)= e <-> exists t, rT |- s =T= t /\ t |=(Ø)= e.
Proof.
  split.
  - revert s;induction e;simpl;try tauto.
    + intros s E;exists (t_var x);repeat split;auto.
      reflexivity.
    + firstorder.
    + intros s (s1&s2&h1&h2&h3).
      apply IHe1 in h2 as (t1&et1&ht1).
      apply IHe2 in h3 as (t2&et2&ht2).
      exists (t1-[o]-t2);split;eauto with proofs.
    + intros s (s'&L&h1&h2&h3).
      revert s s' h1 h2 h3;induction L;[discriminate|].
      assert (L = [] \/ L <> []) as [->|n] by (destruct L;[now left|right;discriminate]).
      * intros s s' E h1 h2;inversion E;subst;clear E.
        cut (s' |=(rT)= e);[|apply h2;now left].
        intros h3;apply IHe in h3 as (t&et&ht).
        exists t;split;eauto with proofs.
        exists t,[t];repeat split;eauto with proofs.
        intros ? [<-|F];[|exfalso];auto.
      * apply (GProd_Some _ o) in n as (s'&h1).
        simpl;rewrite h1.
        intros s ? E h2 h3;inversion E;subst;clear E.
        destruct (IHL s' s') as (t2&et2&s''&L'&EL'&hs''&hL');eauto with proofs.
        cut (a |=(rT)= e);[|apply h3;now left].
        intros h4;apply IHe in h4 as (t1&et1&ht1).
        exists (t1 -[o]- t2);split;eauto with proofs.
        exists (t1 -[o]- s''),(t1::L');simpl;rewrite EL';repeat split;eauto with proofs.
        intros ? [<-|h];[|apply hL'];auto.
  - intros (t&E&h).
    rewrite E.
    revert h;apply gnl_theo_sat_subrelation.
    intros ? ? [].
Qed.

Section gnl_functor.
  (** * Functorial expressions *)

  (** Any function over variables may be extended as a function over expressions. *)

  Fixpoint gnl_map {O} {A B : Set} (f : A -> B) (e : GExp A O) : GExp B O :=
    match e with
    | ø => ø
    | var a => var (f a)
    | e1 + e2 => gnl_map f e1 + gnl_map f e2
    | e1 ×{o} e2 => gnl_map f e1 ×{o} gnl_map f e2
    | e^{o} => (gnl_map f e)^{o}
    end.

  (** Any relation over variables may be lifted as a relation over expressions. *)

  Fixpoint gnl_lift {O} {A B : Set}
    (r : A -> B -> Prop) (e: GExp A O) (f:GExp B O) : Prop :=
    match e,f with
    | ø,ø => True
    | var a,var b => r a b
    | e1 + e2,f1 + f2 => gnl_lift r e1 f1 /\ gnl_lift r e2 f2
    | e1 ×{o} e2,f1 ×{o'} f2  => o = o' /\ gnl_lift r e1 f1 /\ gnl_lift r e2 f2
    | e^{o},e'^{o'} => o = o' /\ gnl_lift r e e'
    | _,_ => False
    end.

  (** The same can be done with terms. *)
  
  Fixpoint gnl_term_map {O} {A B : Set} (f : A -> B) (e : GTerm A O) : GTerm B O :=
    match e with
    | t_var a => t_var (f a)
    | s1 -[o]- s2 => gnl_term_map f s1 -[o]- gnl_term_map f s2
    end.

  Fixpoint gnl_term_lift {O} {A B : Set}
    (r : A -> B -> Prop) (e: GTerm A O) (f:GTerm B O) : Prop :=
    match e,f with
    | t_var a,t_var b => r a b
    | e1 -[o]- e2,f1 -[o']- f2  => o = o' /\ gnl_term_lift r e1 f1 /\ gnl_term_lift r e2 f2
    | _,_ => False
    end.

  (** We fix a set of operators, two sets of variables, and a function [f] between them. *)

  Context { O A B : Set }.
  Context { f : A -> B }.

  (** We take a pair of theories, and assume [gnl_map f] sends the relation [rTA] to the *)
  (** relation [rtB |- _ =T= _]. *)

  Context { rTA : relation (GTerm A O) } { rTB : relation (GTerm B O) }.
  Hypothesis f_term_proper : Proper (rTA ==> gnl_term_theo_eq rTB) (gnl_term_map f).

  (** Then [gnl_map f] sends the whole relation [rTA |- _ =T= _] to the relation [rtB |- _ =T= _]. *)
  
  Global Instance gnl_term_map_proper :
    Proper (gnl_term_theo_eq rTA ==> gnl_term_theo_eq rTB) (gnl_term_map f).
  Proof. intros s t E;induction E;simpl;eauto with proofs. Qed.

  (** Under the same hypotheses, we can express the terms satisfying [gnl_map f e] in terms *)
  (** of those satisfying [e] and the function [gnl_term_map f]. *)
  
  Lemma gnl_map_sat_iff (e : GExp A O) s :
    s |=(rTB)= (gnl_map f e) <-> exists t, rTB |- s =T= (gnl_term_map f t) /\ t |=(rTA)= e. 
  Proof.
    split;[revert s|intros (t&->&ht);clear s;revert t ht];induction e;simpl;try tauto.
    - intros s h.
      exists (t_var x);split;auto with proofs.
    - intros s [h|h];[apply IHe1 in h|apply IHe2 in h];destruct h as (t&et&ht);
        exists t;split;auto.
    - intros s (s1&s2&es&h1&h2).
      apply IHe1 in h1 as (t1&et1&ht1).
      apply IHe2 in h2 as (t2&et2&ht2).
      exists (t1 -[o]- t2);split;auto.
      + simpl;rewrite es,et1,et2;reflexivity.
      + exists t1,t2;split;auto with proofs.
    - intros s (s'&L&es'&es&hL).
      revert s s' es' es hL;induction L;[discriminate|].
      cut (L = [] \/ L <> []);[|destruct L;[left;reflexivity|right;discriminate]].
      intros [->|n].
      + clear IHL;intros.
        destruct (IHe s) as (t&et&ht);
          [rewrite es;inversion es';subst;apply hL;now left|].
        exists t;split;auto.
        exists t,[t];repeat split;auto with proofs.
        intros ? [<-|F];[|exfalso];auto.
      + apply (GProd_Some _ o) in n as (s'&es').
        simpl;rewrite es' in *.
        intros;inversion es'0;subst;clear es'0.
        destruct (IHL s' s') as (t&et1&s''&L'&es''&et2&hL');auto with proofs.
        destruct (IHe a) as (t'&et'&ht');[apply hL;now left|].
        exists (t' -[o]- s'');split;auto.
        * simpl;rewrite es,et1,et',et2;reflexivity.
        * exists (t' -[o]- s''),(t'::L');simpl;rewrite es'';repeat split;auto with proofs.
          intros ? [<-|h];[|apply hL'];auto.
    - intros t ->;reflexivity.
    - firstorder.
    - intros t (s1&s2&E&h1&h2).
      exists (gnl_term_map f s1),(gnl_term_map f s2);repeat split;auto with proofs.
      rewrite E;reflexivity.
    - intros s (s'&L&Es'&E&h).
      revert s s' Es' E h;induction L;[discriminate|].
      cut (L = [] \/ L <> []);[|destruct L;[left;reflexivity|right;discriminate]].
      intros [->|n].
      + clear IHL;intros.
        inversion Es';subst;clear Es'.
        exists (gnl_term_map f s'),[gnl_term_map f s'];repeat split;auto.
        * rewrite E;reflexivity.
        * intros ? [<-|F];[|exfalso;apply F].
          apply IHe,h;now left.
      + apply (GProd_Some _ o) in n as (s'&es').
        simpl;rewrite es' in *.
        intros;inversion Es';subst;clear Es'.
        destruct (IHL s' s') as (s''&L'&es''&et2&hL');auto with proofs.
        exists ((gnl_term_map f a) -[o]- s''),((gnl_term_map f a)::L');
          simpl;rewrite es'';repeat split;auto.
        * rewrite E;simpl;rewrite et2;reflexivity.
        * intros ? [<-|h'];[|apply hL'];auto.
  Qed.

  (** We consider below the effect of [gnl_map f] on relation [rE |- _ ≤ _].*)
  
  Context { rEA : relation (GExp A O) } { rEB : relation (GExp B O) }.
  Hypothesis f_exp_proper : Proper (rEA ==> gnl_theo_inf rEB) (gnl_map f).

  Global Instance gnl_map_proper :
    Proper (gnl_theo_inf rEA ==> gnl_theo_inf rEB) (gnl_map f).
  Proof. intros s t E;induction E;simpl;eauto with proofs. Qed.

  Global Instance gnl_map_proper_eq :
    Proper (gnl_theo_eq rEA ==> gnl_theo_eq rEB) (gnl_map f).
  Proof. intros s t (h1&h2);split;[rewrite h1|rewrite h2];reflexivity. Qed.
  
End gnl_functor.
