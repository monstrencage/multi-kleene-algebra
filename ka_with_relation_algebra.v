(** * gnl_alg.ka : Classic encoding of Kleene algebra *)
Require Import prelim.
From RelationAlgebra Require Import syntax lang regex ka_completeness.

Section reg.
  Context {A : Set}{decA:decidable_set A}.
  
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
  

  Fixpoint support (e : reg) : list A :=
    match e with
    | 1r | 0r => []
    | r_var a => [a]
    | e^* => support e
    | e1 ×r e2 | e1 +r e2 => support e1 ++ support e2
    end.
  
  Definition Sum : list reg -> reg :=
    fold_right r_sum 0r.

  Reserved Notation " e =KA f" (at level 60).
  
  Inductive KA_eq : relation reg :=
  | KA_eq_refl e : e =KA e
  | KA_eq_sym e f : e =KA f -> f =KA e
  | KA_eq_trans e f g : e =KA f -> f =KA g -> e =KA g
  | KA_eq_prod e1 f1 e2 f2 : e1 =KA e2 -> f1 =KA f2 -> e1 ×r f1 =KA e2 ×r f2
  | KA_eq_sum e1 f1 e2 f2 : e1 =KA e2 -> f1 =KA f2 -> e1 +r f1 =KA e2 +r f2
  | KA_eq_star e1 e2 : e1 =KA e2 -> e1^* =KA e2^*
  | KA_eq_prod_assoc e f g : e ×r (f ×r g) =KA (e ×r f) ×r g
  | KA_eq_sum_assoc e f g : e +r (f +r g) =KA (e +r f) +r g
  | KA_eq_sum_comm e f : e +r f =KA f +r e
  | KA_eq_sum_idem e : e +r e =KA e
  | KA_eq_prod_one_e e : 1r ×r e =KA e
  | KA_eq_prod_e_one e : e ×r 1r =KA e
  | KA_eq_sum_zero_e e : 0r +r e =KA e
  | KA_eq_prod_sum e f g : e ×r (f +r g) =KA (e ×r f) +r (e ×r g)
  | KA_eq_sum_prod e f g : (e +r f) ×r g =KA (e ×r g) +r (f ×r g)
  | KA_eq_prod_zero e : e ×r 0r =KA 0r
  | KA_eq_zero_prod e : 0r ×r e =KA 0r
  | KA_eq_star_unfold_left e : e^* =KA 1r +r (e ×r (e^* ))
  | KA_eq_star_unfold_right e : e^* =KA 1r +r ((e^* ) ×r e)
  | KA_eq_star_left_ind e f : (e ×r f) +r f =KA f -> ((e^* ) ×r f) +r f =KA f
  | KA_eq_star_right_ind e f : (f ×r e) +r f =KA f -> (f ×r (e^* )) +r f =KA f
  where " e =KA f " := (KA_eq e f).
               
  Hint Constructors KA_eq : proofs.

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
  Global Instance KA_inf_partialorder : PartialOrder KA_eq KA_inf.
  Proof.
    intros e f;unfold Basics.flip,KA_inf;split.
    - intros E;split;rewrite E;apply KA_eq_sum_idem.
    - intros (E1&E2).
      rewrite <- E1,KA_eq_sum_comm,E2.
      reflexivity.
  Qed.
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
  
  Global Instance r_star_mono : Proper (KA_inf ==> KA_inf) r_star.
  Proof.
    intros e f h.
    apply KA_inf_star_ind.
    rewrite h.
    rewrite KA_eq_star_unfold_left at 2.
    apply KA_inf_join_r.
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

  Reserved Notation " l |=KA e " (at level 60).
  
  Fixpoint KA_sat (l : list A) (e : reg) : Prop :=
    match e with
    | 0r => False
    | 1r => l = []
    | r_var a => l = [a]
    | e ×r f => exists l1 l2, l = l1 ++ l2 /\ l1 |=KA e /\ l2 |=KA f
    | e +r f => l |=KA e \/ l |=KA f
    | e^* => exists L, l = concat L /\ forall k, In k L -> k |=KA e
    end
  where " l |=KA e " := (KA_sat l e).
  
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

  Lemma Sum_sat w L : w |=KA Sum L <-> exists e, w |=KA e /\ In e L.
  Proof.
    induction L;simpl;firstorder.
    subst;tauto.
  Qed.

  Lemma Sum_join_In e L : In e L -> e ≤KA Sum L.
  Proof.
    induction L;simpl;[tauto|].
    intros [<-|h];[apply KA_inf_sum_l|apply KA_inf_sum_r];auto.
    reflexivity.
  Qed.

  Lemma Sum_join_inf e L : Forall (fun f => f ≤KA e) L -> Sum L ≤KA e.
  Proof.
    revert e;induction L as [|f L];intros e hyp.
    - unfold KA_inf;auto with proofs.
    - apply Forall_cons_iff in hyp as (hypf&hypL).
      simpl;apply KA_inf_join;auto.
  Qed.
  
  Section ewp.
    Fixpoint r_ewp (e : reg) : bool :=
      match e with
      | r_var _ | 0r => false
      | _ ^* | 1r => true
      | e ×r f => r_ewp e && r_ewp f
      | e +r f => r_ewp e || r_ewp f
      end.

    Lemma r_ewp_spec e : r_ewp e = true -> [] |=KA e.
    Proof.
      induction e;simpl;try reflexivity||discriminate.
      - rewrite Bool.andb_true_iff.
        intros (h1&h2);exists [],[];repeat split;auto.
      - rewrite Bool.orb_true_iff.
        intros [h|h];auto.
      - intros _;exists [];split;auto.
        intros k f;exfalso;apply f.
    Qed.

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

    Lemma r_ewp_spec_iff e :
      r_ewp e = true <-> [] |=KA e.
    Proof.
      split;[apply r_ewp_spec|].
      induction e;simpl;try discriminate||tauto.
      - intros (l1&l2&E&h1&h2).
        symmetry in E.
        apply app_eq_nil in E as (->&->).
        rewrite IHe1,IHe2 by assumption.
        reflexivity.
      - rewrite Bool.orb_true_iff.
        tauto.
    Qed.

    Lemma r_ewp_eq_iff e :
      r_ewp e = true <-> e +r 1r =KA e.
    Proof.
      split.
      - induction e;simpl;try reflexivity||discriminate.
        + intros _;apply KA_eq_sum_idem.
        + rewrite Bool.andb_true_iff.
          intros (h1&h2);apply IHe1 in h1;apply IHe2 in h2.
          rewrite <- h1,<- h2.
          repeat rewrite KA_eq_sum_prod||rewrite KA_eq_prod_sum
                 ||rewrite KA_eq_prod_e_one||rewrite KA_eq_prod_one_e.
          repeat rewrite <- KA_eq_sum_assoc.
          rewrite KA_eq_sum_idem.
          reflexivity.
        + rewrite Bool.orb_true_iff.
          intros [h|h];auto.
          * apply IHe1 in h.
            rewrite <- h.
            repeat rewrite KA_eq_sum_prod||rewrite KA_eq_prod_sum
                   ||rewrite KA_eq_prod_e_one||rewrite KA_eq_prod_one_e.
            repeat rewrite <- KA_eq_sum_assoc.
            repeat rewrite (KA_eq_sum_comm 1r).
            repeat rewrite <- KA_eq_sum_assoc.
            rewrite KA_eq_sum_idem.
            reflexivity.
          * apply IHe2 in h.
            rewrite <- h.
            repeat rewrite KA_eq_sum_prod||rewrite KA_eq_prod_sum
                   ||rewrite KA_eq_prod_e_one||rewrite KA_eq_prod_one_e.
            repeat rewrite <- KA_eq_sum_assoc.
            rewrite KA_eq_sum_idem.
            reflexivity.
        + intros _.
          rewrite KA_eq_star_unfold_left.
          repeat rewrite <- KA_eq_sum_assoc.
          repeat rewrite (KA_eq_sum_comm 1r).
          repeat rewrite <- KA_eq_sum_assoc.
          rewrite KA_eq_sum_idem.
          reflexivity.
      - intro E;apply r_ewp_eq in E.
        simpl in E.
        rewrite Bool.orb_true_r in E.
        rewrite <- E;reflexivity.
    Qed.
  End ewp.

 
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

Section ka_completeness.

  Definition r_iter {A} (e : reg A) := e ×r e^*.
  
  (* Fixpoint reg_to_regex (e: reg sigma) : lattice.car (monoid.mor regex_tt regex_tt) := *)
  (*   match e with *)
  (*   | 0r => r_zer *)
  (*   | 1r => regex.r_one *)
  (*   | r_var a => regex.r_var a *)
  (*   | e +r f => r_pls (reg_to_regex e) (reg_to_regex f) *)
  (*   | e ×r f => r_dot (reg_to_regex e) (reg_to_regex f) *)
  (*   | e ^* => r_str (reg_to_regex e) *)
  (*   end. *)
  Fixpoint reg_to_expr (e: reg sigma) : expr _ _ _ xH :=  (* @lattice.car (@monoid.mor _ xH xH) := *)
    match e with
    | 0r => e_zer _ _
    | 1r => e_one _
    | r_var a => e_var a
    | e +r f => e_pls (reg_to_expr e) (reg_to_expr f)
    | e ×r f => e_dot (reg_to_expr e) (reg_to_expr f)
    | e ^* => e_str (reg_to_expr e)
    end.
  (* Fixpoint regex_to_reg (e:lattice.car (monoid.mor regex_tt regex_tt)) : reg sigma := *)
  (*   match e with *)
  (*   | r_zer => 0r *)
  (*   | regex.r_one => 1r *)
  (*   | regex.r_var a => r_var a *)
  (*   | r_pls e f => (regex_to_reg e) +r (regex_to_reg f) *)
  (*   | r_dot e f => (regex_to_reg e) ×r (regex_to_reg f) *)
  (*   | r_str e => (regex_to_reg e)^* *)
  (*   end. *)
  
  (* Lemma regex_to_reg_to_regex e : reg_to_regex (regex_to_reg e) = e. *)
  (* Proof. induction e;simpl;try f_equal;auto. Qed. *)
  (* Lemma reg_to_regex_to_reg e : regex_to_reg (reg_to_regex e) = e. *)
  (* Proof. induction e;simpl;try f_equal;auto. Qed. *)

  Set Implicit Arguments.
  Canonical Structure reg_lattice_ops : lattice.ops :=
    {|
      lattice.car := reg sigma;
      lattice.leq := KA_inf;
      lattice.weq := KA_eq;
      lattice.cup := r_sum;
      lattice.bot := 0r;
      lattice.cap := common.assert_false r_sum;
      lattice.top := common.assert_false 0r;
      lattice.neg := common.assert_false id
    |}.

  CoInductive reg_unit := reg_tt.
  Canonical Structure reg_ops :=
    {|
      monoid.ob := reg_unit;
      monoid.mor n m := reg_lattice_ops;
      monoid.dot n m p := r_prod;
      monoid.one n := 1r;
      monoid.itr n := r_iter;
      monoid.str n := r_star;
      monoid.cnv n m := common.assert_false r_star;
      monoid.ldv n m p := common.assert_false r_prod;
      monoid.rdv n m p := common.assert_false r_prod
    |}.

  Instance reg_laws: monoid.laws level.BKA reg_ops.
  Proof.
    split;intros;simpl;auto with proofs;try (now inversion H).
    - split;intros;simpl;auto with proofs;try (now inversion Hl).
      + split;intro;intros.
        * reflexivity.
        * etransitivity;eassumption.
      + apply KA_inf_partialorder.
      + split.
        * intros <-;split;[apply KA_inf_join_l|apply KA_inf_join_r].
        * intros (->&->);rewrite KA_eq_sum_idem;reflexivity.
      + right;apply KA_inf_zero.
    - right;intros.
      apply r_prod_mono;assumption.
    - right;intros.
      rewrite KA_eq_sum_prod;reflexivity.
    - repeat right;intros.
      rewrite KA_eq_prod_sum;reflexivity.
    - repeat right;intros.
      rewrite KA_eq_zero_prod;reflexivity.
    - repeat right;intros.
      rewrite KA_eq_prod_zero;reflexivity.
    - apply KA_inf_star_one.
    - rewrite KA_eq_star_unfold_left at 2.
      apply KA_inf_join_r.
    - apply KA_inf_star_left_ind,H0.
    - repeat right;intros.
      apply KA_inf_star_right_ind,H0.
  Qed.


  Lemma lang_to_sat e l : lang 
  
End ka_completeness.
