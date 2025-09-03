(** * gnl_alg.ka : Classic encoding of Kleene algebra *)
Require Import prelim.
(** We provide here a standard representation of Kleene algebra, as the algebra *)
(** of regular expressions interpreted as languages, i.e. predicates over lists. *)
  
Section reg.

  (** * Syntax & axiomatisation *)

  (** We fix a decidable set [A]. *)
  
  Context {A : Set}{decA:decidable_set A}.

  (** Regular expressions are built out of variables from [A], the constants [0r] and [1r], *)
  (** as well as two binary operators [+r] and [×r] and a unary operator [^*]. *)
  
  Inductive reg :=
  | r_var : A -> reg
  | r_one : reg
  | r_zero : reg
  | r_prod : reg -> reg -> reg
  | r_sum : reg -> reg -> reg
  | r_star : reg -> reg.

  Notation "1r" := r_one.
  Notation "0r" := r_zero.
  Infix "+r" := r_sum (at level 20).
  Infix "×r" := r_prod (at level 20).
  Notation " e ^* " := (r_star e).

  (** We define the axiomatic equivalence [=KA] as follows: *)
  
  Reserved Notation " e =KA f" (at level 60).
  
  Inductive KA_eq : relation reg :=
  (** It is an equivalence relation, i.e. reflexive symmetric and transitive. *)
  | KA_eq_refl e : e =KA e
  | KA_eq_sym e f : e =KA f -> f =KA e
  | KA_eq_trans e f g : e =KA f -> f =KA g -> e =KA g
  (** It is a congruence with respect to each operator. *)
  | KA_eq_prod e1 f1 e2 f2 : e1 =KA e2 -> f1 =KA f2 -> e1 ×r f1 =KA e2 ×r f2
  | KA_eq_sum e1 f1 e2 f2 : e1 =KA e2 -> f1 =KA f2 -> e1 +r f1 =KA e2 +r f2
  | KA_eq_star e1 e2 : e1 =KA e2 -> e1^* =KA e2^*
  (** Both binary operators are associative. *)
  | KA_eq_prod_assoc e f g : e ×r (f ×r g) =KA (e ×r f) ×r g
  | KA_eq_sum_assoc e f g : e +r (f +r g) =KA (e +r f) +r g
  (** [+r] is commutative and idempotent. *)
  | KA_eq_sum_comm e f : e +r f =KA f +r e
  | KA_eq_sum_idem e : e +r e =KA e
  (** [1r] is the unit of [×r] and [0r] that of [+r]. *)
  | KA_eq_prod_one_e e : 1r ×r e =KA e
  | KA_eq_prod_e_one e : e ×r 1r =KA e
  | KA_eq_sum_zero_e e : 0r +r e =KA e
  (** [×r] distributes over [+r]. *)
  | KA_eq_prod_sum e f g : e ×r (f +r g) =KA (e ×r f) +r (e ×r g)
  | KA_eq_sum_prod e f g : (e +r f) ×r g =KA (e ×r g) +r (f ×r g)
  (** [0r] is an annihilator for [×r]. *)
  | KA_eq_prod_zero e : e ×r 0r =KA 0r
  | KA_eq_zero_prod e : 0r ×r e =KA 0r
  (** [^*] may be unfolded on both sides. *)
  | KA_eq_star_unfold_left e : e^* =KA 1r +r (e ×r (e^* ))
  | KA_eq_star_unfold_right e : e^* =KA 1r +r ((e^* ) ×r e)
  (** [^*] enjoys two _induction axioms_ :*)
  | KA_eq_star_left_ind e f : (e ×r f) +r f =KA f -> ((e^* ) ×r f) +r f =KA f
  | KA_eq_star_right_ind e f : (f ×r e) +r f =KA f -> (f ×r (e^* )) +r f =KA f
  where " e =KA f " := (KA_eq e f).
               
  Hint Constructors KA_eq : proofs.

  (** Some obvious properties of this relation. *)
  
  Global Instance KA_eq_equiv : Equivalence KA_eq.
  Proof.
    split.
    - intro;apply KA_eq_refl.
    - intros s t e;apply KA_eq_sym,e.
    - intros s t u e1 e2;eapply KA_eq_trans;eassumption.
  Qed.

  Lemma KA_eq_sum_e_zero e : e +r 0r =KA e.
  Proof. transitivity (0r +r e);auto with proofs. Qed.
  Hint Resolve KA_eq_sum_e_zero : proofs.
  
  Global Instance r_prod_proper : Proper (KA_eq ==> KA_eq ==> KA_eq) r_prod.
  Proof. intros s s' es t t' et;apply KA_eq_prod;assumption. Qed.

  Global Instance r_sum_proper : Proper (KA_eq ==> KA_eq ==> KA_eq) r_sum.
  Proof. intros s s' es t t' et;apply KA_eq_sum;assumption. Qed.

  Global Instance r_star_proper : Proper (KA_eq ==> KA_eq) r_star.
  Proof. intros s s' es;apply KA_eq_star;assumption. Qed.

  (** An associated preorder is defined by [e≤f] iff [e+f=f]. *)
   
  Definition KA_inf : relation reg := fun e f => e +r f =KA f.

  Infix " ≤KA " := KA_inf (at level 60).
  
  Global Instance KA_inf_preorder : PreOrder KA_inf.
  Proof.
    split.
    - intro e;apply KA_eq_sum_idem.
    - unfold KA_inf;intros e f g h1 h2.
      transitivity (e +r (f +r g)).
      + rewrite h2;reflexivity.
      + rewrite KA_eq_sum_assoc.
        rewrite h1,h2;reflexivity.
  Qed.

  (** [≤KA] is a partial order w.r.t. [=KA]. *)
  
  Global Instance KA_inf_partialorder : PartialOrder KA_eq KA_inf.
  Proof.
    intros e f;unfold Basics.flip,KA_inf;split.
    - intros E;split;rewrite E;apply KA_eq_sum_idem.
    - intros (E1&E2).
      rewrite <- E1,KA_eq_sum_comm,E2.
      reflexivity.
  Qed.

  (** [+r] is a join operator for the preorder [≤KA]. *)
  
  Lemma KA_inf_join_l e f : e ≤KA e +r f.
  Proof. unfold KA_inf;rewrite KA_eq_sum_assoc,KA_eq_sum_idem;reflexivity. Qed.

  Lemma KA_inf_join_r e f : f ≤KA e +r f.
  Proof. unfold KA_inf;rewrite KA_eq_sum_comm,<-KA_eq_sum_assoc,KA_eq_sum_idem;reflexivity. Qed.

  Lemma KA_inf_join e f g : e ≤KA g -> f ≤KA g -> e +r f ≤KA g.
  Proof. unfold KA_inf;intros h1 h2;rewrite <- h1,<- h2 at 2;symmetry;apply KA_eq_sum_assoc. Qed.

  Lemma KA_inf_sum_l e f g : e ≤KA f -> e ≤KA f +r g.
  Proof. intros ->;apply KA_inf_join_l. Qed.

  Lemma KA_inf_sum_r e f g : e ≤KA g -> e ≤KA f +r g.
  Proof. intros ->;apply KA_inf_join_r. Qed.

  (** Every operator is monotonous w.r.t. [≤KA]. *)

  Global Instance r_prod_mono : Proper (KA_inf ==> KA_inf ==> KA_inf) r_prod.
  Proof.
    unfold KA_inf;intros e1 e2 he f1 f2 hf.
    rewrite <- he,<- hf. 
    repeat rewrite KA_eq_sum_prod||rewrite KA_eq_prod_sum.
    repeat rewrite KA_eq_sum_assoc.
    rewrite KA_eq_sum_idem.
    reflexivity.
  Qed.
 
  Global Instance r_sum_mono : Proper (KA_inf ==> KA_inf ==> KA_inf) r_sum.
  Proof.
    unfold KA_inf;intros e1 e2 he f1 f2 hf.
    rewrite <- he,<- hf. 
    repeat rewrite KA_eq_sum_assoc.
    rewrite (KA_eq_sum_comm e1 f1).
    rewrite <- (KA_eq_sum_assoc f1 e1 e1).
    rewrite KA_eq_sum_idem.
    rewrite (KA_eq_sum_comm _ f1).
    repeat rewrite KA_eq_sum_assoc.
    rewrite KA_eq_sum_idem.
    rewrite (KA_eq_sum_comm _ f1).
    repeat rewrite KA_eq_sum_assoc.
    reflexivity.
  Qed.

  Global Instance r_star_mono : Proper (KA_inf ==> KA_inf) r_star.
  Proof.
    intros e f h.
    rewrite KA_eq_star_unfold_left at 1.
    apply KA_inf_join.
    - rewrite KA_eq_star_unfold_left;apply KA_inf_join_l.
    - rewrite h at 1.
      transitivity (f^*×r e^* );[apply r_prod_mono;[|reflexivity]|].
      + rewrite KA_eq_star_unfold_left,KA_eq_star_unfold_left.
        apply KA_inf_sum_r.
        rewrite <- (KA_eq_prod_e_one) at 1.
        apply r_prod_mono;[reflexivity|].
        apply KA_inf_join_l.
      + apply KA_eq_star_right_ind.
        cut (f ^* ×r e ≤KA f ^* );[intro h';apply h'|].
        rewrite h.
        rewrite KA_eq_star_unfold_right at 2.
        apply KA_inf_join_r.
  Qed.

  (** Below is a collection of useful facts about [=KA] and [≤KA]. *)

  Lemma KA_inf_zero e : 0r ≤KA e.
  Proof. unfold KA_inf;auto with proofs. Qed.
  
  Lemma KA_inf_star_one e : 1r ≤KA e^* .
  Proof. rewrite KA_eq_star_unfold_left;apply KA_inf_join_l. Qed.

  Lemma KA_inf_star_e e : e ≤KA e^* .
  Proof.
    rewrite KA_eq_star_unfold_left.
    rewrite <- KA_inf_star_one,KA_eq_prod_e_one.
    apply KA_inf_join_r.
  Qed.

  Lemma KA_inf_star_left_ind e f : e ×r f ≤KA f -> (e^* ) ×r f ≤KA f.
  Proof. apply (KA_eq_star_left_ind e f). Qed.

  Lemma KA_inf_star_right_ind e f : f ×r e ≤KA f -> f ×r (e^* ) ≤KA f.
  Proof. apply (KA_eq_star_right_ind e f). Qed.

  Lemma KA_inf_star_ind e f : e ×r (f^* ) ≤KA f^* -> e^* ≤KA f^*.
  Proof.
    intro h;apply KA_inf_star_left_ind in h as <-.
    rewrite <- (KA_inf_star_one f),KA_eq_prod_e_one;reflexivity.
  Qed.
  
  Lemma KA_eq_star_prod_star (e : reg) : e^* ×r e^* =KA e^*.
  Proof.
    apply KA_inf_partialorder;unfold Basics.flip;split.
    - apply KA_inf_star_left_ind.
      rewrite (KA_eq_star_unfold_left e) at 2.
      apply KA_inf_join_r.
    - rewrite <- KA_inf_star_one at 2.
      rewrite KA_eq_prod_one_e.
      reflexivity.
  Qed.
  
  Lemma KA_eq_star_star (e : reg) : (e^* )^* =KA e^*.
  Proof.
    apply KA_inf_partialorder;unfold Basics.flip;split.
    - apply KA_inf_star_ind.
      rewrite KA_eq_star_prod_star.
      reflexivity.
    - apply KA_inf_star_e.
  Qed.

  Lemma KA_eq_star_sum_one (e : reg) : (1r +r e)^* =KA e^*.
  Proof.
    apply KA_inf_partialorder;unfold Basics.flip;split.
    - apply KA_inf_star_ind.
      rewrite KA_eq_sum_prod,KA_eq_prod_one_e.
      apply KA_inf_join;[reflexivity|].
      rewrite KA_eq_star_unfold_left at 2.
      apply KA_inf_join_r.    
    - rewrite <- KA_inf_join_r;reflexivity.
  Qed.

  (** * Semantics *)

  (** We now define the language associated with an expression, through a satisfaction *)
  (** predicate [l |=KA e], specifying when a list [l] belongs to the language associated *)
  (** with an expression [e]. *)
  
  Reserved Notation " l |=KA e " (at level 60).
  
  Fixpoint KA_sat (l : list A) (e : reg) : Prop :=
    match e with
    (** The language of [0r] is empty. *)
    | 0r => False
    (** Only the empty list satisfies [1r]. *)
    | 1r => l = []
    (** Variables are satisfied by singleton lists. *)
    | r_var a => l = [a]
    (** Lists satisfying [e ×r f] are concatenations of a list satisfying [e] and one *)
    (** satisfying [f]. *)
    | e ×r f => exists l1 l2, l = l1 ++ l2 /\ l1 |=KA e /\ l2 |=KA f
    (** The language of [e +r f] is the union of the languages of [e] and [f]. *)
    | e +r f => l |=KA e \/ l |=KA f
    (** A list satisfies [e^*] if it can be written as a concatenation of lists that *)
    (** all satisfy [e]. *)
    | e^* => exists L, l = concat L /\ forall k, In k L -> k |=KA e
    end
  where " l |=KA e " := (KA_sat l e).

  (** The axioms of the previous section are sound w.r.t. this semantic interpretation. *)
  Global Instance KA_sound s : Proper (KA_eq ==> iff) (KA_sat s).
  Proof.
    intros e f pr;revert s;induction pr;intro s;simpl;try now firstorder.
    - firstorder.
      + exists (x++x1),x2;repeat split.
        * rewrite H,H1.
          apply app_assoc.
        * exists x, x1;repeat split;auto.
        * assumption.
      + exists x1, (x2++x0);repeat split.
        * rewrite H,H0.
          symmetry;apply app_assoc.
        * assumption.
        * exists x2, x0;repeat split;auto.
    - split.
      + intros (s1&s2&E&h1&h2).
        subst;simpl;assumption.
      + intros h;exists [],s;repeat split;auto.
    - split.
      + intros (s1&s2&E&h1&h2).
        subst;rewrite app_nil_r.
        assumption.
      + intros h;exists s,[];repeat split;auto.
        symmetry;apply app_nil_r.
    - firstorder.
      + destruct x.
        * left;apply H.
        * right;exists l,(concat x).
          repeat split.
          -- apply H.
          -- apply H0;now left.
          -- exists x;split.
             ++ reflexivity.
             ++ intros;apply H0;now right.
      + exists [];split;[apply H|simpl;tauto].
      + exists (x::x1);split;simpl.
        * rewrite H,H1;reflexivity.
        * intros k [->|h];auto.
    - firstorder.
      + destruct (list_last_dec x) as [->|(s'&l'&->)].
        * left;apply H.
        * right;exists (concat l'),s'.
          repeat split.
          -- rewrite H,concat_app;simpl.
             rewrite app_nil_r.
             reflexivity.
          -- exists l';split.
             ++ reflexivity.
             ++ intros;apply H0,in_app_iff; now left.
          -- apply H0,in_app_iff; now right;left.
      + exists [];split;[apply H|simpl;tauto].
      + exists (x1++[x0]);split;simpl.
        * rewrite concat_app;simpl.
          rewrite app_nil_r,<-H0;assumption.
        * intros k h;apply in_app_iff in h as [h|[->|h]];simpl in *;tauto||auto.
    - firstorder.
      revert s H; revert x H0.
      induction x1;intros x H0 s H.
      + simpl in *.
        subst;simpl;assumption.
      + apply IHpr;left.
        exists a,(concat (x1++[x0])).
        split;[|split].
        * rewrite H,H0,concat_app.
          simpl;rewrite app_nil_r.
          symmetry;apply app_assoc.
        * apply H2;now left.
        * eapply IHx1.
          -- intros;apply H2;now right.
          -- reflexivity.
          -- rewrite concat_app;simpl;rewrite app_nil_r.
             reflexivity.
    - firstorder.
      revert x1 s x x0 H H0 H1 H2.
      apply (@rev_ind _
               (fun x1 =>
                  forall (s x x0 : list A),
                    s = x ++ x0 ->
                    x |=KA f -> x0 = concat x1 -> (forall k : list A, In k x1 -> k |=KA e) ->
                    s |=KA f));
        [|intros s' x' IH];intros s x x0 H H0 H1 H2.
      + simpl in *.
        rewrite H1,app_nil_r in H.
        subst;assumption.
      + apply IHpr;left.
        exists (concat (x::x')),s'.
        split;[|split].
        * rewrite H,H1,concat_app.
          simpl;rewrite app_nil_r.
          apply app_assoc.
        * eapply IH.
          -- simpl;reflexivity.
          -- assumption.
          -- reflexivity.
          -- intros;apply H2,in_app_iff; now left.
        * apply H2,in_app_iff; now right;left.
  Qed.

  Global Instance KA_inf_sound s : Proper (KA_inf ==> Basics.impl) (KA_sat s).
  Proof. intros e f he h;unfold KA_inf in he;rewrite <- he;now left. Qed.

  (** * Empty word property *)

  (** It will be useful to be able to identify which expressions satisfy the so-called *)
  (** _empty word property_ (ewp), i.e. expressions [e] such that [[] |=KA e]. We do so *)
  (** using the following boolean predicate. *)
  
  Fixpoint r_ewp (e : reg) : bool :=
    match e with
    | r_var _ | 0r => false
    | _ ^* | 1r => true
    | e ×r f => r_ewp e && r_ewp f
    | e +r f => r_ewp e || r_ewp f
    end.

  (** To establish the correctness of [r_ewp], we first show that it is a morphism from *)
  (** expressions up-to [=KA] to the booleans (up-to equality). *)
 
  Lemma r_ewp_eq : Proper (KA_eq ==> eq) r_ewp.
  Proof.
    intros e f pr;induction pr;simpl;try reflexivity||(now f_equal)||eauto.
    - apply Bool.andb_assoc.
    - apply Bool.orb_assoc.
    - apply Bool.orb_comm.
    - apply Bool.orb_diag.
    - apply Bool.andb_true_r.
    - apply Bool.andb_orb_distrib_r.
    - apply Bool.andb_orb_distrib_l.
    - apply Bool.andb_false_r.
    - apply Bool.orb_diag.
    - rewrite Bool.andb_true_r.
      apply Bool.orb_diag.
  Qed.

  (** We can now establish that [r_ewp e] is [true] exactly when the empty list *)
  (** satisfies the expression [e]. *)
  
  Lemma r_ewp_spec e :
    r_ewp e = true <-> [] |=KA e.
  Proof.
    split;induction e;simpl;try reflexivity||discriminate||tauto.
    - rewrite Bool.andb_true_iff.
      intros (h1&h2);exists [],[];repeat split;auto.
    - rewrite Bool.orb_true_iff.
      intros [h|h];auto.
    - intros _;exists [];split;auto.
      intros k f;exfalso;apply f.
    - intros (l1&l2&E&h1&h2).
      symmetry in E.
      apply app_eq_nil in E as (->&->).
      rewrite IHe1,IHe2 by assumption.
      reflexivity.
    - rewrite Bool.orb_true_iff.
      tauto.
  Qed.

  (** Alternatively, we can specfiy [r_ewp] by stating that this predicate characterizes *)
  (** expressions that are above [1r] in the preorder [≤KA]. *)
  
  Lemma r_ewp_alt_spec e :
    r_ewp e = true <-> 1r ≤KA e.
  Proof.
    split.
    - induction e;simpl;try reflexivity||discriminate.
      + rewrite Bool.andb_true_iff.
        intros (h1&h2);apply IHe1 in h1;apply IHe2 in h2.
        rewrite <- h1,<- h2.
        repeat rewrite KA_eq_sum_prod||rewrite KA_eq_prod_sum
               ||rewrite KA_eq_prod_e_one||rewrite KA_eq_prod_one_e.
        reflexivity.
      + rewrite Bool.orb_true_iff.
        intros [h|h];auto.
        * apply IHe1 in h.
          rewrite <- h.
          apply KA_inf_join_l.
        * apply IHe2 in h.
          rewrite <- h.
          apply KA_inf_join_r.
      + intros _;apply KA_inf_star_one.
    - intro E;apply r_ewp_eq in E as <-;reflexivity.
  Qed.
 
End reg.


Notation "1r" := r_one.
Notation "0r" := r_zero.
Infix "+r" := r_sum (at level 20).
Infix "×r" := r_prod (at level 20).
Notation " e ^* " := (r_star e).

Infix "=KA" := KA_eq (at level 60).
Infix "≤KA" := KA_inf (at level 60).
Infix "|=KA" := KA_sat (at level 60).
Hint Constructors KA_eq : proofs.
Hint Resolve KA_eq_sum_e_zero : proofs.

Arguments reg : clear implicits.
