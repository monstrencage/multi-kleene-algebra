(** * gnl_alg.cka: Classic encodiing of commutative Kleene algebra *)
Require Import prelim ka.
  
Section creg.
  (** * Axiomatisation *)
  Context {A : Set} {decA : decidable_set A}.

  (** ** Definition *)

  (** The axiomatic definition of [=cKA] is almost identical to that of [=KA] *)
  (** with the addition of the commutativity axiom. This addition allows use  *)
  (** to drop a few axioms: only one side of the axioms pertaining to the     *)
  (** interaction between [×r] and the constants is needed, and similary the  *)
  (** star axioms (unfolding and induction) only need one version each, the   *)
  (** other being derivable from the first one and the commutativity axiom.   *)
  Reserved Notation " e =cKA f" (at level 60).
  
  Inductive cKA_eq : relation (reg A) :=
  | cKA_eq_refl e : e =cKA e
  | cKA_eq_sym e f : e =cKA f -> f =cKA e
  | cKA_eq_trans e f g : e =cKA f -> f =cKA g -> e =cKA g
  | cKA_eq_prod e1 f1 e2 f2 : e1 =cKA e2 -> f1 =cKA f2 -> e1 ×r f1 =cKA e2 ×r f2 
  | cKA_eq_sum e1 f1 e2 f2 : e1 =cKA e2 -> f1 =cKA f2 -> e1 +r f1 =cKA e2 +r f2
  | cKA_eq_star e1 e2 : e1 =cKA e2 -> e1^*  =cKA e2^* 
  | cKA_eq_prod_assoc e f g : e ×r (f ×r g) =cKA (e ×r f) ×r g
  | cKA_eq_sum_assoc e f g : e +r (f +r g) =cKA (e +r f) +r g
  (** Commutativity axiom *)
  | cKA_eq_prod_comm e f : e ×r f =cKA f ×r e
  | cKA_eq_sum_comm e f : e +r f =cKA f +r e
  | cKA_eq_sum_idem e : e +r e =cKA e
  | cKA_eq_prod_one_e e : 1r ×r e =cKA e
  | cKA_eq_sum_zero_e e : 0r +r e =cKA e
  | cKA_eq_prod_sum e f g : e ×r (f +r g) =cKA (e ×r f) +r (e ×r g)
  | cKA_eq_prod_e_zero e : e ×r 0r =cKA 0r
  | cKA_eq_star_unfold e : e^* =cKA 1r +r (e ×r (e^* ))
  | cKA_eq_star_ind e f : (e ×r f) +r f =cKA f -> ((e^* ) ×r f) +r f =cKA f
  where " e =cKA f " := (cKA_eq e f).
  
  Hint Constructors cKA_eq : proofs.
  
  (** The order [≤cKA] is defined like [≤KA]. *)

  Definition cKA_inf : relation (reg A) := fun e f => e +r f =cKA f.

  Infix "≤cKA" := cKA_inf (at level 60).

  (** ** Standard properties  *)

  Global Instance cKA_eq_equiv : Equivalence cKA_eq.
  Proof.
    split.
    - intro;apply cKA_eq_refl.
    - intros s t e;apply cKA_eq_sym,e.
    - intros s t u e1 e2;eapply cKA_eq_trans;eassumption.
  Qed.

  Global Instance r_prod_cproper : Proper (cKA_eq ==> cKA_eq ==> cKA_eq) r_prod.
  Proof. intros s s' es t t' et;apply cKA_eq_prod;assumption. Qed.

  Global Instance r_sum_cproper : Proper (cKA_eq ==> cKA_eq ==> cKA_eq) r_sum.
  Proof. intros s s' es t t' et;apply cKA_eq_sum;assumption. Qed.

  Global Instance r_star_cproper : Proper (cKA_eq ==> cKA_eq) r_star.
  Proof. intros s s' es;apply cKA_eq_star;assumption. Qed.

  (** We check that [=KA] is a subrelation of [=cKA], in essence proving that *)
  (** the axioms we dropped can be recovered. *)

  Global Instance KA_incl_cKA : subrelation KA_eq cKA_eq.
  Proof.
    intros e f pr;induction pr;simpl;auto with proofs.
    - eauto with proofs.
    - transitivity (1r ×r e);auto with proofs.
    - transitivity (g ×r (e +r f));auto with proofs.
      transitivity ((g ×r e) +r (g ×r f));auto with proofs.
    - transitivity (e ×r 0r);auto with proofs.
    - transitivity (1r +r (e ×r (e^* )));auto with proofs.
    - transitivity (r_sum ((e^* ) ×r f) f);auto with proofs.
      apply cKA_eq_star_ind.
      transitivity ((f ×r e) +r f);auto with proofs.
  Qed.

  (** ** Properties of the preorder *)

  Global Instance cKA_inf_preorder : PreOrder cKA_inf.
  Proof.
    split.
    - intro e;apply cKA_eq_sum_idem.
    - unfold cKA_inf;intros e f g h1 h2.
      transitivity (e +r (f +r g)).
      + rewrite h2;reflexivity.
      + rewrite cKA_eq_sum_assoc.
        rewrite h1,h2;reflexivity.
  Qed.
  
  Global Instance cKA_inf_partialorder : PartialOrder cKA_eq cKA_inf.
  Proof.
    intros e f;unfold Basics.flip,cKA_inf;split.
    - intros E;split;rewrite E;apply cKA_eq_sum_idem.
    - intros (E1&E2).
      rewrite <- E1,cKA_eq_sum_comm,E2.
      reflexivity.
  Qed.
  
  Global Instance KA_incl_cKA_inf : subrelation KA_inf cKA_inf.
  Proof. unfold cKA_inf,KA_inf;intros e f h;rewrite h;reflexivity. Qed.

  Lemma cKA_inf_join e f g : cKA_inf e g -> cKA_inf f g -> e +r f ≤cKA g.
  Proof. 
    unfold cKA_inf;intros h1 h2;rewrite <- h1,<- h2 at 2;symmetry;
    apply cKA_eq_sum_assoc. 
  Qed.

  Lemma cKA_inf_sum_l e f g : cKA_inf e f -> e ≤cKA f +r g.
  Proof. intros ->;rewrite <-KA_inf_join_l;reflexivity. Qed.
  Lemma cKA_inf_sum_r e f g : cKA_inf e g -> e ≤cKA f +r g.
  Proof. intros ->;rewrite <-KA_inf_join_r;reflexivity. Qed.
  Lemma cKA_inf_star_ind e f : e ×r f ≤cKA f -> e^* ×r f ≤cKA f.
  Proof. apply (cKA_eq_star_ind e f). Qed.

  Global Instance r_prod_cmono : Proper (cKA_inf ==> cKA_inf ==> cKA_inf) r_prod.
  Proof.
    unfold cKA_inf;intros e1 e2 he f1 f2 hf.
    rewrite <- he,<- hf. 
    repeat rewrite KA_eq_sum_prod||rewrite KA_eq_prod_sum.
    repeat rewrite KA_eq_sum_assoc.
    rewrite KA_eq_sum_idem.
    reflexivity.
  Qed.
 
  Global Instance r_sum_cmono : Proper (cKA_inf ==> cKA_inf ==> cKA_inf) r_sum.
  Proof.
    unfold cKA_inf;intros e1 e2 he f1 f2 hf.
    rewrite <- he,<- hf. 
    repeat rewrite cKA_eq_sum_assoc.
    rewrite (cKA_eq_sum_comm e1 f1).
    rewrite <- (cKA_eq_sum_assoc f1 e1 e1).
    rewrite cKA_eq_sum_idem.
    rewrite (cKA_eq_sum_comm _ f1).
    repeat rewrite cKA_eq_sum_assoc.
    rewrite cKA_eq_sum_idem.
    rewrite (cKA_eq_sum_comm _ f1).
    repeat rewrite cKA_eq_sum_assoc.
    reflexivity.
  Qed.


  Global Instance r_star_cmono : Proper (cKA_inf ==> cKA_inf) r_star.
  Proof.
    intros e f h.
    rewrite cKA_eq_star_unfold at 1.
    rewrite cKA_eq_prod_comm.
    apply cKA_inf_join.
    - rewrite <- KA_inf_star_one;reflexivity.
    - rewrite h at 2.
      rewrite (KA_inf_star_e f) at 1.
      apply cKA_inf_star_ind.
      rewrite h;rewrite cKA_eq_star_unfold at 2.
      rewrite <- KA_inf_join_r.
      reflexivity.
  Qed.

  (** ** [cKA] versions of [KA] lemmas, trivially proved by convenient to have. *)

  Lemma cKA_inf_join_l e f : e ≤cKA e +r f.
  Proof. rewrite <- KA_inf_join_l;reflexivity. Qed.
  
  Lemma cKA_inf_join_r e f : f ≤cKA e +r f.
  Proof. rewrite <- KA_inf_join_r;reflexivity. Qed.
  
  Lemma cKA_inf_zero e : 0r ≤cKA e.
  Proof. rewrite <- (KA_inf_zero e);reflexivity. Qed.
  
  Lemma cKA_inf_star_one e : 1r ≤cKA e^* .
  Proof. rewrite <- (KA_inf_star_one e);reflexivity. Qed.

  Lemma cKA_inf_star_e e : e ≤cKA e^* .
  Proof. rewrite <- KA_inf_star_e;reflexivity. Qed.

  Lemma cKA_inf_star_alt_ind e f : e ×r f^* ≤cKA f^* -> e^* ≤cKA f^*.
  Proof.
    intro h;apply cKA_inf_star_ind in h as <-.
    rewrite <- (cKA_inf_star_one f),KA_eq_prod_e_one;reflexivity.
  Qed.
  
  (** * Semantics *)
  
  (** The definition of [|=cKA] is similar to that of [|=KA], except we replace *)
  (** equality between lists with the relation [≈mset] in the cases of   *)
  (** [×r] and [^*]. *)

  Reserved Notation " l |=cKA e " (at level 60).

  Fixpoint cKA_sat (l : list A) (e : reg A) : Prop :=
    match e with
    | 0r => False
    | 1r => l = []
    | r_var a => l = [a]
    | e ×r f => exists l1 l2, l ≈mset l1 ++ l2 /\ l1 |=cKA e /\ l2 |=cKA f
    | e +r f => l |=cKA e \/ l |=cKA f
    | e^* => exists L, l ≈mset concat L /\ forall k, In k L -> k |=cKA e
    end
  where " l |=cKA e " := (cKA_sat l e).

  (** The semantic relation is stable by [≈mset]. *)

  Lemma cKA_sat_eq_list_comm : Proper (eq_list_comm ==> eq ==> iff) cKA_sat.
  Proof.
    cut (forall e l m, l ≈mset m -> l |=cKA e -> m |=cKA e);
      [intros h l m elm e f <-;split;apply h;[|symmetry];assumption|].
    intro e;induction e;intros l m E;simpl.
    - intros ->; apply eq_list_comm_sngl, E.
    - intros ->;apply eq_list_comm_nil,E. 
    - tauto.
    - intros (l1&l2&h1&h2&h3).
      exists l1,l2;repeat split;auto.
      transitivity l;[symmetry|];assumption.
    - intuition.
      + left;eapply IHe1;eassumption.
      + right;eapply IHe2;eassumption.
    - intros (L&h1&h2).
      exists L;repeat split;auto.
      transitivity l;[symmetry|];assumption.
  Qed.

  (** Our axiomatisation is sound with respect to our semantics. *)

  Lemma cKA_sound s : Proper (cKA_eq ==> iff) (cKA_sat s).
  Proof.
    intros e f pr;revert s;induction pr;intro s;simpl;try now firstorder.
    - firstorder.
      + exists (x++x1),x2;repeat split.
        * rewrite H,H1.
          rewrite app_assoc;reflexivity.
        * exists x, x1;repeat split;auto.
        * assumption.
      + exists x1, (x2++x0);repeat split.
        * rewrite H,H0.
          rewrite app_assoc;reflexivity.
        * assumption.
        * exists x2, x0;repeat split;auto.
    - split;intros (l1&l2&h1&h2&h3);exists l2,l1;repeat split;auto;rewrite h1;
        apply eq_list_comm_app_comm.
    - split.
      + intros (s1&s2&E&h1&h2).
        subst;simpl in *.
        eapply cKA_sat_eq_list_comm,h2;auto.
      + intros h;exists [],s;repeat split;auto.
    - firstorder.
      + destruct x.
        * left;simpl in H.
          apply eq_list_comm_nil;symmetry;apply H.
        * right;exists l,(concat x).
          repeat split.
          -- apply H.
          -- apply H0;now left.
          -- exists x;split.
             ++ reflexivity.
             ++ intros;apply H0;now right.
      + exists [];split;[simpl;subst;reflexivity|simpl;tauto].
      + exists (x::x1);split;simpl.
        * rewrite H,H1;reflexivity.
        * intros k [->|h];auto.
    - firstorder.
      revert s H; revert x H0.
      induction x1;intros x H0 s H.
      + simpl in *.
        eapply cKA_sat_eq_list_comm,H1;auto.
        rewrite H,H0;simpl;reflexivity.
      + apply IHpr;left.
        exists a,(concat (x1++[x0])).
        split;[|split].
        * rewrite H,H0,concat_app.
          simpl;rewrite app_nil_r.
          rewrite app_assoc;reflexivity.
        * apply H2;now left.
        * eapply IHx1.
          -- intros;apply H2;now right.
          -- reflexivity.
          -- rewrite concat_app;simpl;rewrite app_nil_r.
             reflexivity.
  Qed.

  (** The previous pair of lemmas can be combined as the following property: *)

  Global Instance cKA_sat_proper : Proper (eq_list_comm ==> cKA_eq ==> iff) cKA_sat.
  Proof.
    intros l1 l2 hl e1 e2 he.
    etransitivity;[eapply cKA_sat_eq_list_comm;[apply hl|reflexivity]|].
    apply cKA_sound,he.
  Qed.

  (** ** Semantic decomposition *)
  (** The semantics of [|=cKA] are essentially that of [|=KA] up-to [≈mset]. *)

  Proposition cKA_sat_KA_sat s e : s |=cKA e <-> exists l, s ≈mset l /\ l |=KA e.
  Proof.
    revert s;induction e;simpl;intros s;try tauto.
    - split;[intros hs|intros (l&E&hs)];subst.
      + exists [a];split;reflexivity.
      + symmetry in E;apply eq_list_comm_sngl in E;auto.
    - split;[intros hs|intros (l&E&hs)];subst.
      + exists [];split;reflexivity.
      + symmetry in E;apply eq_list_comm_nil in E;auto.
    - firstorder.
    - setoid_rewrite IHe1.
      setoid_rewrite IHe2.
      split;[intros (l1&l2&E&(m1&E1&h1)&m2&E2&h2)|intros (l&E&l1&l2&->&hs1&hs2)].
      + setoid_rewrite E;setoid_rewrite E1;setoid_rewrite E2.
        exists (m1++m2);split;[reflexivity|].
        firstorder.
      + exists l1,l2;firstorder.
    - setoid_rewrite IHe1.
      setoid_rewrite IHe2.
      firstorder.
    - setoid_rewrite IHe;clear IHe.
      split.
      + intros (L&EL&hL).
        revert s EL hL;induction L;intros.
        * symmetry in EL.
          apply eq_list_comm_nil in EL;subst.
          exists [];split;[reflexivity|exists [];simpl;tauto].
        * simpl in EL.
          setoid_rewrite EL;clear s EL.
          destruct (IHL (concat L)) as (l&EL&L'&->&hL');[reflexivity|intros;apply hL;now right|].
          setoid_rewrite EL.
          destruct (hL a) as (l&El&hl);[now left|].
          exists (l++concat L');split;[rewrite El;reflexivity|].
          exists (l::L');split;auto.
          intros ? [<-|h];[|apply hL'];auto.
      + intros (l&EL&L&->&hL).
         revert s EL hL;induction L;intros.
        * symmetry in EL.
          apply eq_list_comm_nil in EL;subst.
          exists [];split;[reflexivity|simpl;tauto].
        * simpl in EL.
          setoid_rewrite EL;clear s EL.
          destruct (IHL (concat L)) as (L'&EL'&hL');[reflexivity|intros;apply hL;now right|].
          setoid_rewrite EL'.
          exists (a::L');split;[reflexivity|].
          intros ? [<-|h];[exists a;split;[reflexivity|apply hL;left]|apply hL'];auto.
  Qed.
End creg.
Hint Constructors cKA_eq : proofs. 

Infix "=cKA" := cKA_eq (at level 60).
Infix "≤cKA" := cKA_inf (at level 60).
Infix "|=cKA" := cKA_sat (at level 60).
