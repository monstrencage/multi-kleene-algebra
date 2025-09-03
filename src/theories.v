(** * gnl_alg.theories : Well-known theories *)
Require Import prelim ka cka.
Require Import gnl.  

Section slat.
  (** * Semi-lattices *)
  
  Context {A : Set}{decA:decidable_set A}.

  (** The syntax of semi-lattices simply consists in a constant [zero] and a *)
  (** binary operator [sum], ergo general expressions with no products.  *)

  Definition slat := GExp A Zero.

  (** We define the following shorthands: *)

  Notation " a |=slat= e " := (@gnl_theo_sat A Zero Ø (t_var a) e) (at level 60). 
  Notation " e =slat= f " := (@gnl_theo_eq A Zero Ø e f) (at level 60).
  Notation " e ≤slat f " := (@gnl_theo_inf A Zero Ø e f) (at level 60).

  (** Note that the satisfaction relation [|=slat=] has type [A -> slat -> Prop] instead *)
  (** of [GTerm A Zero -> slat -> Prop]. That is because while the sets [A] and [GTerm A Zero] *)
  (** are isomorphic, [A] is more convenient to manipulate. *)

  (** This satisfaction relation is in fact decidable, thanks to the following procedure: *)
  
  Fixpoint slat_satb (a : A) (s : slat) : bool :=
    match s with
    | ø => false
    | var b => if a =?= b then true else false 
    | e + f => (slat_satb a e) || (slat_satb a f)
    | _ ×{_} _ => false
    | _^{_} => false
    end.

  (** Indeed this boolean function corresponds to the appropriate predicate. *)
  
  Lemma slat_satb_spec a s : slat_satb a s = true <-> a |=slat= s.
  Proof.
    induction s as [| b| |[] |[] ];simpl.
    - split.
      + discriminate.
      + tauto.
    - case_eq (a =?= b).
      + intros ->;split;reflexivity.
      + intros n _;split;[discriminate|].
        intros E;apply get_var_eq in E;simpl in E;inversion E;tauto.
    - rewrite Bool.orb_true_iff,IHs1,IHs2;reflexivity.
  Qed.

  (** Furthermore, we may decide the semantic inclusion of a pair of [slat] expressions. *)
    
  Fixpoint is_inclb (s t : slat) : bool :=
    match s with
    | ø => true
    | var a => slat_satb a t
    | s1 + s2 => is_inclb s1 t && is_inclb s2 t
    | _ ×{_} _ | _^{_} => false
    end.

  (** As before, we check that the above boolean predicate corresponds with our intention. *)

  Lemma is_inclb_spec s t : is_inclb s t = true <-> forall a, a |=slat= s -> a |=slat= t.
  Proof.
    revert t;induction s as [| | |[] |[]].
    - intros t;simpl;split;auto.
      intros _ a f;tauto.
    - intros t;simpl.
      rewrite slat_satb_spec;split;auto.
      + intros h1 a h2.
        apply get_var_eq in h2;inversion h2;subst;auto.
      + intros h;apply h;reflexivity.
    - intros t;simpl;rewrite Bool.andb_true_iff,IHs1,IHs2;split.
      + intros (h1&h2) a [h|h];auto.
      + intros h;split;intros a h';apply h;auto.
  Qed.

  (** Moreover, whenever [is_inclb] deems an expression included in another, we may build a *)
  (** proof that [s ≤slat t]. *)
 
  Lemma is_inclb_slat_eq s t : is_inclb s t = true -> s ≤slat t.
  Proof.
    induction s as [|a | |[]|[]];simpl.
    - induction t as [|b | |[] |[]];simpl;intros _;auto with proofs.
    - intros h;auto with proofs.
      induction t as [|b| |[]|[]];simpl in *;try discriminate.
      + destruct (a =?= b);[|discriminate].
        subst;reflexivity.
      + apply Bool.orb_true_iff in h as [h|h].
        * apply gnl_theo_inf_sum_left;auto.
        * apply gnl_theo_inf_sum_right;auto.
    - rewrite Bool.andb_true_iff;intros (h1&h2);auto with proofs.
  Qed.

  (** This ensures that no theory is necessary to capture all semantic inclusions in [slat]. *)
    
  Theorem slat_exact s t : s ≤slat t <-> forall a, a |=slat= s -> a |=slat= t.
  Proof.
    split.
    - intros E a;rewrite E;tauto.
    - intros e.
      apply is_inclb_slat_eq,is_inclb_spec;apply e.
  Qed.

  (** It also means that the preorder [≤slat] is decidable. *)

  Lemma slat_dec s t : {s ≤slat t} + { ~ s ≤slat t}.
  Proof.
    case_eq (is_inclb s t).
    - intro h1;left;apply is_inclb_slat_eq in h1;auto.
    - intros h;right;intro f;apply Bool.not_true_iff_false in h;apply h;rewrite slat_exact in f;
        apply is_inclb_spec;intros;apply f;assumption.
  Qed.
End slat.
Arguments slat : clear implicits.
Notation " a |=slat= e " := (@gnl_theo_sat _ Zero Ø (t_var a) e) (at level 60). 
Notation " e =slat= f " := (@gnl_theo_eq _ Zero Ø e f) (at level 60).
Notation " e ≤slat f " := (@gnl_theo_inf _ Zero Ø e f) (at level 60).

Section ka_to_gnl.
  (** * Kleene Algebra *)

  (** In this section, we propose an encoding of KA in our syntax. *)

  (** We pose a decidable base set. *)
  Context {A : Set}{decA:decidable_set A}.

  (** We define _regular expressions_ as general expressions with a single operator, *)
  (** over a set of variables [option A].*)
  
  Definition Reg := GExp (option A) One.

  (** Similarly for words. *)

  Definition Word := GTerm (option A) One.

  (** Both for words and expressions, the special variable [var None] is interpreted as *)
  (** the constant [1].*)

  Notation "1_r" := (var None).
  Notation "1_w" := (t_var None).
  Notation var_r := (fun a : A => var (Some a)).
  Notation var_w := (fun a : A => t_var (Some a)).

  (** We introduce special notations for the products and iterators associated with *)
  (** our single operator. *)

  Infix " ** " := (t_prod •) (at level 20).
  Infix " @@ " := (prod •) (at level 20).
  Notation "e ^+" := (iter • e).

  (** The theories [ka] and [KA], defining respecively the axioms for [Words] and those *)
  (** for [Reg] expressions, are simply stating that [1] acts as a unit w.r.t. products. *)
  
  Inductive ka : relation Word :=
  | one_left_w w : ka (1_w ** w) w
  | one_right_w w : ka (w ** 1_w) w. 

  (** Notice that in [ka], to be used in [ka |- _ =T= _], we only need two axioms, while *)
  (** in [KA], to be used in [KA |- _ ≤ _], we need four. *)
  
  Inductive KA : relation Reg :=
  | one_left_r e : KA (1_r @@ e) e
  | one_right_r e : KA (e @@ 1_r) e
  | one_left_inv_r e : KA e (1_r @@ e)
  | one_right_inv_r e : KA e (e @@ 1_r). 

  Hint Constructors ka KA : proofs.

  (** We check that both theories are compatible, in that one is sound w.r.t. the *)
  (** satisfaction relation associated with the other. *)
  
  Global Instance gnl_sat_reg_theo_proper w :
    Proper (KA ==> Basics.impl) (gnl_theo_sat ka w).
  Proof.
    unfold Basics.impl;intros ? ? [] h3;simpl in *.
    + destruct h3 as (s1&s2&h1&h2&h3).
      cut (ka |- w =T= s2).
      * intros ->;assumption.
      * rewrite h1,h2.
        auto with proofs.
    + destruct h3 as (s1&s2&h1&h2&h3).
      cut (ka |- w =T= s1).
      * intros ->;assumption.
      * rewrite h1,h3.
        auto with proofs.
    + exists 1_w,w;repeat split;auto with proofs.
    + exists w,1_w;repeat split;auto with proofs.
  Qed.

  (** We proceed to show that our encoding is faithful, and that there is an isomorphism *)
  (** between it an the more standard version in [gnl_alg.ka]. *)

  (** To that end, we provide two simple translation functions between our two types of *)
  (** expressions. *)
    
  Fixpoint Reg_to_reg (e : Reg) : reg A :=
    match e with
    | ø => 0r
    | 1_r => 1r
    | var (Some a) => r_var a
    | e + f => Reg_to_reg e +r Reg_to_reg f
    | e @@ f => Reg_to_reg e ×r Reg_to_reg f
    | e ^+ => Reg_to_reg e ×r (Reg_to_reg e)^*
    end.

  Fixpoint reg_to_Reg (e : reg A) : Reg :=
    match e with
    | 0r => ø
    | 1r => 1_r
    | r_var a => var_r a
    | e ×r f => reg_to_Reg e @@ reg_to_Reg f
    | e +r f => reg_to_Reg e + reg_to_Reg f
    | e ^* => 1_r + (reg_to_Reg e)^+
    end.

  (** In both cases, the only interesting case is the relationship between [e^*] and [e^+]: *)
  (** - in one direction, [e^*] is translated as [1 + e^+] (recursively), *)
  (** - in the other, we send [e^+] to [e ×r e^*]. *)

  (** We prove that these functions are inverses of each other, w.r.t. the appropriate *)
  (** equivalence relations. *)

  Lemma Reg_to_reg_and_back (e : Reg) :
    KA |- reg_to_Reg(Reg_to_reg e) == e.
  Proof.
    induction e as [|[]| |[] |[]];simpl;
      try rewrite IHe1,IHe2|| rewrite IHe;
      try (now split;auto with proofs).
    rewrite gnl_theo_eq_prod_sum.
    transitivity (e + (e @@ e ^+));split;auto with proofs.
  Qed.
  
  Lemma reg_to_Reg_and_back (e : reg A) :
    Reg_to_reg(reg_to_Reg e) =KA e.
  Proof.
    induction e;simpl;try rewrite IHe1,IHe2|| rewrite IHe;try reflexivity.
    eauto with proofs.
  Qed.

  (** They are also order-morphisms. *)
  Global Instance reg_theo_to_KA :
    Proper (gnl_theo_inf KA ==> KA_inf) Reg_to_reg.
  Proof.
    assert (KA_eq_KA_inf: forall e f : reg A, e =KA f -> e ≤KA f)
      by (intros ? ? ->;reflexivity).
    intros e f pr;induction pr;try destruct i;simpl;auto with proofs;
      try (now apply KA_eq_KA_inf;auto with proofs).
    - rewrite IHpr1,IHpr2;reflexivity.
    - rewrite IHpr1,IHpr2;reflexivity.
    - rewrite IHpr;reflexivity.
    - apply KA_inf_join_l.
    - apply KA_inf_join_r.
    - apply KA_inf_join;assumption.
    - unfold KA_inf;auto with proofs.
    - rewrite KA_eq_star_unfold_left at 2.
      rewrite KA_eq_prod_sum.
      rewrite KA_eq_prod_e_one.
      reflexivity.
    - rewrite KA_eq_star_unfold_right at 2.
      rewrite KA_eq_prod_sum.
      rewrite KA_eq_prod_e_one.
      rewrite KA_eq_prod_assoc.
      reflexivity.
    - simpl in *.
      generalize dependent (Reg_to_reg f);
        generalize dependent (Reg_to_reg e);clear e f pr;intros e f.
      intro h.
      transitivity (e^* ×r f);
        [|apply KA_inf_star_left_ind,h].
      apply r_prod_mono;[|reflexivity].
      rewrite KA_eq_star_unfold_left at 2.
      apply KA_inf_join_r.
    - simpl in *.
      generalize dependent (Reg_to_reg f);
        generalize dependent (Reg_to_reg e);clear e f pr;intros e f.
      intro h.
      transitivity (f ×r e^* );
        [|apply KA_inf_star_right_ind,h].
      apply r_prod_mono;[reflexivity|].
      rewrite KA_eq_star_unfold_left at 2.
      apply KA_inf_join_r.
    - simpl in *.
      generalize dependent (Reg_to_reg f);
        generalize dependent (Reg_to_reg e);clear e f pr;intros e f.
      intro h.
      assert (h1: e ≤KA f) by (rewrite <- h;apply KA_inf_join_l).
      assert (h2: e ×r f ≤KA f) by (rewrite <- h at 2;apply KA_inf_join_r).
      transitivity (e^* ×r f);
        [|apply KA_inf_star_left_ind;rewrite <- h at 2;apply KA_inf_join_r].
      rewrite KA_eq_star_unfold_right at 1.
      rewrite KA_eq_prod_sum.
      rewrite KA_eq_prod_e_one.
      apply KA_inf_join.
      + rewrite h1 at 1.
        rewrite <- KA_eq_prod_one_e at 1.
        apply r_prod_mono;[|reflexivity].
        apply KA_inf_star_one.
      + rewrite KA_eq_prod_assoc.
        rewrite (KA_inf_star_e e) at 1.
        rewrite KA_eq_star_prod_star.
        rewrite h1 at 2.
        reflexivity.
    - simpl in *.
      generalize dependent (Reg_to_reg f);
        generalize dependent (Reg_to_reg e);clear e f pr;intros e f.
      intro h.
      assert (h1: e ≤KA f) by (rewrite <- h;apply KA_inf_join_l).
      assert (h2: f ×r e ≤KA f) by (rewrite <- h at 2;apply KA_inf_join_r).
      rewrite h1 at 1.
      apply KA_inf_star_right_ind.
      apply h2.
    - destruct H;simpl;try (now apply KA_eq_KA_inf;auto with proofs).
  Qed.

  Global Instance reg_theo_to_KA_eq :
    Proper (gnl_theo_eq KA ==> KA_eq) Reg_to_reg.
  Proof.
    intros e f (h1&h2);apply KA_inf_partialorder;unfold Basics.flip;
      split;rewrite h1||rewrite h2;reflexivity.
  Qed.
  
  Global Instance KA_to_reg_theo :
    Proper (KA_eq ==> gnl_theo_eq KA) reg_to_Reg.
  Proof.
    intros e f pr;induction pr;simpl;try (now split;auto with proofs).
    - symmetry;assumption.
    - etransitivity;eassumption.
    - rewrite IHpr1,IHpr2;reflexivity.
    - rewrite IHpr1,IHpr2;reflexivity.
    - rewrite IHpr;reflexivity.
    - split;repeat apply gnl_theo_inf_join;
        eauto with proofs.
    - generalize (reg_to_Reg e);clear e;intro e.
      transitivity (1_r + (e + (e @@ e^+)));[split;auto with proofs|].
      cut (KA |- e + e @@ e ^+ == e @@ (1_r + e ^+));[intros ->;reflexivity|].
      transitivity ((e @@ 1_r) + (e @@ e^+));
        split;auto with proofs.
    - generalize (reg_to_Reg e);clear e;intro e.
      transitivity (1_r + ((1_r@@e)+(e^+@@e)));
        [|split;auto with proofs].
      transitivity (1_r + (e + (e^+@@e)));
        [|split;auto with proofs].
      split;auto with proofs.
    - simpl in IHpr.
      generalize dependent (reg_to_Reg f);
        generalize dependent (reg_to_Reg e);clear e f pr;intros e f.
      intros (h1&h2);split;auto with proofs.
      apply gnl_theo_inf_join;auto with proofs.
      transitivity ((1_r @@ f) + ( e^+@@f));auto with proofs.
      transitivity (f + (e^+@@f));auto with proofs.
      apply gnl_theo_inf_join;auto with proofs.
      apply gnl_theo_inf_iter_left_ind.
      rewrite <- h1 at 2;auto with proofs.
    - simpl in IHpr.
      generalize dependent (reg_to_Reg f);
        generalize dependent (reg_to_Reg e);clear e f pr;intros e f.
      intros (h1&h2);split;auto with proofs.
      apply gnl_theo_inf_join;auto with proofs.
      transitivity ((f @@ 1_r)+(f@@ e^+));auto with proofs.
      transitivity (f + (f@@ e^+));auto with proofs.
      apply gnl_theo_inf_join;auto with proofs.
      apply gnl_theo_inf_iter_right_ind.
      rewrite <- h1 at 2;auto with proofs.
  Qed.

  Global Instance KA_to_reg_theo_inf :
    Proper (KA_inf ==> gnl_theo_inf KA) reg_to_Reg.
  Proof. intros e f h;unfold KA_inf in h;rewrite <- h;simpl;auto with proofs. Qed.

  (** This means that we have our isomorphim between the equational theories. We now show *)
  (** how this carries to the semantics. *)
  
  (** For that purpose, we define functions between lists and [Word]s. *)
    
  Fixpoint Word_to_list (w : Word) : list A :=
    match w with
    | 1_w => []
    | t_var (Some a) => [a]
    | e ** f => (Word_to_list e)++(Word_to_list f)
    end.

  Definition WProd : list Word -> Word := fold_right (t_prod •) 1_w.

  Definition list_to_Word : list A -> Word :=
    fun m => WProd (map var_w m).

  (** Both transformations are morphisms, also in the case of [list_to_Words] it holds trivially *)
  (** since we consider lists up-to strict equality. *)
  
  Lemma Word_to_list_eq :
    Proper (gnl_term_theo_eq ka ==> eq) Word_to_list.
  Proof.
    intros u v pr;induction pr;simpl;auto.
    - etransitivity;eassumption.
    - rewrite IHpr1,IHpr2.
      reflexivity.
    - destruct o;apply app_assoc. 
    - destruct H;simpl;auto using app_nil_r.
  Qed.

  (** We shall need these lemmas further along : *)

  Lemma WProd_app l1 l2 :
    ka |- WProd (l1++l2) =T= WProd l1 ** WProd l2.
  Proof.
    revert l2;induction l1;intros l2;simpl.
    - auto with proofs.
    - rewrite IHl1;clear IHl1.
      auto with proofs.
  Qed.

  Lemma GProd_concat L T :
    GProd • L = Some T -> Word_to_list T = concat (map Word_to_list L).
  Proof.
    revert T;induction L;[discriminate|].
    destruct (L =?= []).
    - subst;simpl.
      intros T E;inversion E;symmetry;apply app_nil_r.
    - apply (GProd_Some _ •) in n as (T&hT).
      simpl;rewrite hT.
      intros T' E;inversion E;subst;clear E.
      simpl.
      rewrite (IHL T hT).
      reflexivity.
  Qed.

  (** Now we prove that our functions are inverses of each other (up-to the *)
  (** appropriate equivalence relation). *)
  
  Lemma list_to_Word_and_back l :
    Word_to_list (list_to_Word l) = l.
  Proof.
    unfold list_to_Word;induction l;simpl.
    - reflexivity.
    - rewrite IHl;reflexivity.
  Qed.

  Lemma Word_to_list_and_back w :
    ka |- list_to_Word (Word_to_list w) =T=  w.
  Proof.
    unfold list_to_Word;induction w as [[|]|[]];simpl;auto with proofs.
    rewrite map_app,WProd_app.
    rewrite IHw1,IHw2.
    reflexivity.
  Qed.

  (** We now show how we can use our functions both on words and on expressions to *)
  (** from one of the semantics to the other : *)
  
  Lemma KA_to_reg_theo_sem w e :
    w |=KA e -> list_to_Word w |=(ka)= reg_to_Reg e.
  Proof.
    unfold list_to_Word;revert w;induction e;intro w;simpl;try (now firstorder).
    - intro h;subst;simpl;auto with proofs.
    - intros ->;simpl;auto with proofs.
    - intros (l1&l2&->&h1&h2).
      exists (list_to_Word l1),(list_to_Word l2);repeat split;auto.
      + rewrite map_app.
        rewrite WProd_app.
        reflexivity.
      + apply IHe1,h1.
      + apply IHe2,h2.
    - intros (L&->&hL);simpl.
      destruct (map list_to_Word L =?= []);
        [left;apply map_eq_nil in e0;subst;reflexivity|right].
      apply (GProd_Some _ •) in n as (t&ht).
      exists t;eexists;split;[apply ht|].
      split.
      + revert t ht;clear e IHe hL.
        induction L;[discriminate|].
        simpl.
        destruct (map list_to_Word L =?= []);
          [repeat apply map_eq_nil in e;subst|].
        * simpl;intros t E;inversion E;subst;clear E.
          rewrite app_nil_r.
          reflexivity.
        * apply (GProd_Some _ •) in n as (t&ht).
          rewrite ht in *.
          intros t' E;inversion E;subst;clear E.
          rewrite map_app,WProd_app.
          rewrite (IHL t) by auto.
          reflexivity.
      + setoid_rewrite in_map_iff.
        intros s'' (l&<-&h);apply IHe,hL,h.
  Qed.

  Lemma reg_theo_to_KA_sem w e :
    w |=(ka)= e -> Word_to_list w |=KA Reg_to_reg e.
  Proof.
    revert w;induction e as [|[|]| |[] |[]];intro w;simpl;try tauto.
    - intros h1;apply Word_to_list_eq in h1;simpl in h1;assumption.
    - intros h1;apply Word_to_list_eq in h1;simpl in h1;assumption.
    - firstorder.
    - intros (s1&s2&h1&h2&h3).
      exists (Word_to_list s1),(Word_to_list s2).
      repeat split;intuition.
      apply Word_to_list_eq in h1;simpl in h1;assumption.
    - intros (s'&L&h1&h2&h3).
      destruct L as [|t L];[inversion h1|].
      destruct (L =?= []).
      + subst;inversion h1;subst;clear h1.
        exists (Word_to_list w),[].
        rewrite app_nil_r;repeat split;auto.
        * apply IHe.
          rewrite h2.
          apply h3;now left.
        * exists [];simpl;split;tauto.
      + apply (GProd_Some _ •) in n as (T&hT).
        simpl in h1;rewrite hT in h1;inversion h1;subst;clear h1.
        exists (Word_to_list t),(Word_to_list T);repeat split.
        * apply Word_to_list_eq in h2 as ->;simpl;reflexivity.
        * apply IHe,h3;now left.
        * exists (map Word_to_list L);repeat split;
            [|intros ? h;apply in_map_iff in h as (?&<-&h);apply IHe,h3;now right].
          eapply GProd_concat,hT.
  Qed.

  (** Using the two implications above, plus the fact that we have functions that are *)
  (** inverses of each other, we can establish the following semantic correspondances. *)

  Theorem KA_reg_semantic_correspondance1 w e :
    w |=(ka)= e <-> Word_to_list w |=KA Reg_to_reg e.
  Proof.
    split;[apply reg_theo_to_KA_sem|].
    intro h;apply KA_to_reg_theo_sem in h.
    rewrite <- Word_to_list_and_back.
    rewrite <- Reg_to_reg_and_back.
    assumption.
  Qed.
  
  Theorem KA_reg_semantic_correspondance2 w e :
    w |=KA e <-> list_to_Word w |=(ka)= reg_to_Reg e.
  Proof.
    split;[apply KA_to_reg_theo_sem|].
    intro h;apply reg_theo_to_KA_sem in h.
    rewrite list_to_Word_and_back in h.
    rewrite reg_to_Reg_and_back in h.
    assumption.
  Qed.

  Definition ewp_r := fun e => r_ewp (Reg_to_reg e).

  Global Instance ewp_r_eq : Proper (gnl_theo_eq KA ==> eq) ewp_r.
  Proof.
    intros e f E;unfold ewp_r.
    apply r_ewp_eq;rewrite E;reflexivity.
  Qed.

  Lemma ewp_r_spec e : ewp_r e = true <-> 1_w |=(ka)= e.
  Proof.
    unfold ewp_r;rewrite r_ewp_spec.
    replace [] with (Word_to_list 1_w) by reflexivity.
    symmetry;apply KA_reg_semantic_correspondance1.
  Qed.
  
  Lemma ewp_r_alt_spec e : ewp_r e = true <-> KA |- 1_r ≤ e.
  Proof.
    unfold ewp_r;rewrite r_ewp_alt_spec;split;intro h.
    - apply KA_to_reg_theo in h.
      simpl in h.
      repeat rewrite Reg_to_reg_and_back in h.
      rewrite <- h;auto with proofs.
    - apply reg_theo_to_KA in h;apply h.
  Qed.
    
End ka_to_gnl.

Arguments Reg : clear implicits. 
Arguments Word : clear implicits.

Notation "1_r" := (var None).
Notation "1_w" := (t_var None).
Notation var_r := (fun a : _ => var (Some a)).
Notation var_w := (fun a : _ => t_var (Some a)).
Infix " ** " := (t_prod •) (at level 20).
Infix " @@ " := (prod •) (at level 20).
Notation "e ^+" := (iter • e).

Definition id_none_plus {X Y : Set} (f : X -> Y) : option X -> option Y :=
  fun xo =>
    match xo with
    | None => None
    | Some x => Some (f x)
    end.

Section Reg_functor.
  Definition Reg_map {X Y : Set} (f : X -> Y) : Reg X -> Reg Y :=
    gnl_map (id_none_plus f).

  Lemma ewp_r_reg_map: forall {X Y : Set} (f : X -> Y) (e : Reg X), ewp_r (Reg_map f e) = ewp_r e.
  Proof.
    unfold ewp_r,Reg_map;intros.
    induction e as [|[]| |[] |[]];simpl;auto with bool.
    - rewrite IHe1,IHe2;reflexivity.
    - rewrite IHe1,IHe2;reflexivity.
    - rewrite IHe;reflexivity.
  Qed.

  Inductive fKA {X O} (r : relation (GExp X O)) : relation (Reg(GExp X O)) :=
  | fKA_KA e f : KA e f -> fKA r e f
  | fKA_r_eq e f : r |- e ≤ f -> fKA r (var_r e) (var_r f)
  | fKA_zero : fKA r (var_r ø) ø
  | fKA_sum e f : fKA r (var_r (e + f)) (var_r e + var_r f).
End Reg_functor.
Hint Constructors fKA : proofs.



Section cka_to_gnl.
  (** * Commutative Kleene algebra *)
  Context {A : Set}{decA:decidable_set A}.

  Inductive cka : relation (Word A) :=
  | one_left_cw w : cka (1_w ** w) w
  | prod_comm_cw u v : cka (u ** v) (v ** u). 

  Inductive cKA : relation (Reg A) :=
  | one_left_cr e : cKA (1_r @@ e) e
  | one_left_inv_cr e : cKA e (1_r @@ e)
  | prod_comm_cr e f : cKA (e @@ f) (f @@ e). 

  Hint Constructors cka cKA : proofs.
  
  Global Instance KA_to_cKA : subrelation (gnl_theo_inf KA) (gnl_theo_inf cKA).
  Proof.
    intros e f pr;induction pr;simpl;auto with proofs.
    - eauto with proofs.
    - destruct H;auto with proofs.
      + transitivity (1_r @@ e);auto with proofs.
      + transitivity (1_r @@ e);auto with proofs.
  Qed.
  
  Global Instance KA_to_cKA_eq : subrelation (gnl_theo_eq KA) (gnl_theo_eq cKA).
  Proof. intros e f (h1&h2);split;rewrite h1||rewrite h2;reflexivity. Qed.

  Global Instance ka_to_cka : subrelation (gnl_term_theo_eq ka) (gnl_term_theo_eq cka).
  Proof.
    intros e f pr;induction pr;simpl;auto with proofs.
    - eauto with proofs.
    - destruct H;auto with proofs.
      transitivity (1_w ** w);auto with proofs.
  Qed.
  
  Global Instance reg_theo_to_cKA :
    Proper (gnl_theo_inf cKA ==> cKA_inf) Reg_to_reg.
  Proof.
    assert (KA_eq_KA_inf: forall e f : reg A, cKA_eq e f -> cKA_inf e f)
      by (intros ? ? ->;reflexivity).
    intros e f pr;induction pr;try destruct i;simpl;auto with proofs;
      try (now apply KA_eq_KA_inf;auto with proofs).
    - rewrite IHpr1,IHpr2;reflexivity.
    - rewrite IHpr1,IHpr2;reflexivity.
    - rewrite IHpr;reflexivity.
    - apply cKA_inf_join_l.
    - apply cKA_inf_join_r.
    - apply cKA_inf_join;assumption.
    - unfold cKA_inf;auto with proofs.
    - rewrite cKA_eq_star_unfold at 2.
      rewrite cKA_eq_prod_sum.
      rewrite cKA_eq_prod_e_one.
      reflexivity.
    - rewrite KA_eq_star_unfold_right at 2.
      rewrite KA_eq_prod_sum.
      rewrite KA_eq_prod_e_one.
      rewrite KA_eq_prod_assoc.
      reflexivity.
    - simpl in *.
      generalize dependent (Reg_to_reg f);
        generalize dependent (Reg_to_reg e);clear e f pr;intros e f.
      intro h.
      transitivity (r_prod (r_star e) f);
        [|apply cKA_inf_star_ind,h].
      apply r_prod_cmono;[|reflexivity].
      rewrite KA_eq_star_unfold_left at 2.
      apply cKA_inf_join_r.
    - simpl in *.
      generalize dependent (Reg_to_reg f);
        generalize dependent (Reg_to_reg e);clear e f pr;intros e f.
      intro h.
      transitivity (r_prod f (r_star e)).
      + apply r_prod_cmono;[reflexivity|].
        rewrite KA_eq_star_unfold_left at 2.
        apply cKA_inf_join_r.
      + transitivity (r_prod (r_star e) f);auto with proofs.
        apply cKA_inf_star_ind.
        transitivity (r_prod f e);auto with proofs.
    - simpl in *.
      generalize dependent (Reg_to_reg f);
        generalize dependent (Reg_to_reg e);clear e f pr;intros e f.
      intro h.
      assert (h1: cKA_inf e f) by (rewrite <- h;apply cKA_inf_join_l).
      assert (h2: cKA_inf (r_prod e f) f) by (rewrite <- h at 2;apply cKA_inf_join_r).
      transitivity (r_prod (r_star e) f);
        [|apply cKA_inf_star_ind;rewrite <- h at 2;apply cKA_inf_join_r].
      rewrite KA_eq_star_unfold_right at 1.
      rewrite KA_eq_prod_sum.
      rewrite KA_eq_prod_e_one.
      apply cKA_inf_join.
      + rewrite h1 at 1.
        rewrite <- KA_eq_prod_one_e at 1.
        apply r_prod_cmono;[|reflexivity].
        apply cKA_inf_star_one.
      + rewrite KA_eq_prod_assoc.
        rewrite (cKA_inf_star_e e) at 1.
        rewrite KA_eq_star_prod_star.
        rewrite h1 at 2.
        reflexivity.
    - simpl in *.
      generalize dependent (Reg_to_reg f);
        generalize dependent (Reg_to_reg e);clear e f pr;intros e f.
      intro h.
      assert (h1: cKA_inf e f) by (rewrite <- h;apply cKA_inf_join_l).
      assert (h2: cKA_inf (r_prod f e) f) by (rewrite <- h at 2;apply cKA_inf_join_r).
      rewrite h1 at 1.
      transitivity (r_prod (r_star e) f);auto with proofs.
      apply cKA_inf_star_ind.
      transitivity (r_prod f e);auto with proofs.
    - destruct H;simpl;try (now apply KA_eq_KA_inf;auto with proofs).
  Qed.

  Global Instance reg_theo_to_cKA_eq :
    Proper (gnl_theo_eq cKA ==> cKA_eq) Reg_to_reg.
  Proof.
    intros e f (h1&h2);apply cKA_inf_partialorder;unfold Basics.flip;
      split;rewrite h1||rewrite h2;reflexivity.
  Qed.
  
  Global Instance cKA_to_reg_theo :
    Proper (cKA_eq ==> gnl_theo_eq cKA) reg_to_Reg.
  Proof.
    intros e f pr;induction pr;simpl;try (now split;auto with proofs).
    - symmetry;assumption.
    - etransitivity;eassumption.
    - rewrite IHpr1,IHpr2;reflexivity.
    - rewrite IHpr1,IHpr2;reflexivity.
    - rewrite IHpr;reflexivity.
    - split;repeat apply gnl_theo_inf_join;
        eauto with proofs.
    - generalize (reg_to_Reg e);clear e;intro e.
      transitivity (1_r + (e + (e @@ e^+)));[split;auto with proofs|].
      cut (cKA |- e + e @@ e ^+ == e @@ (1_r + e ^+));
        [intros ->;reflexivity|].
      transitivity ((e @@ 1_r) + (e @@ e^+));[|split;auto with proofs].
      transitivity ((1_r@@e) + (e @@ e^+));split;auto with proofs.
    - simpl in IHpr.
      generalize dependent (reg_to_Reg f);
        generalize dependent (reg_to_Reg e);clear e f pr;intros e f.
      intros (h1&h2);split;auto with proofs.
      apply gnl_theo_inf_join;auto with proofs.
      transitivity ((1_r @@ f) + ( e^+@@f));auto with proofs.
      transitivity (f + (e^+@@f));auto with proofs.
      apply gnl_theo_inf_join;auto with proofs.
      apply gnl_theo_inf_iter_left_ind.
      rewrite <- h1 at 2;auto with proofs.
  Qed.


  Global Instance Word_to_list_eq_list_comm :
    Proper (gnl_term_theo_eq cka ==> eq_list_comm) Word_to_list.
  Proof.
    intros u v pr;induction pr;simpl;auto.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - destruct o;rewrite IHpr1,IHpr2.
      reflexivity.
    - destruct o;rewrite app_assoc;reflexivity. 
    - destruct H;simpl.
      + reflexivity.
      + apply eq_list_comm_app_comm.
  Qed.

  Global Instance list_to_Word_eq_list_comm :
    Proper (eq_list_comm ==> gnl_term_theo_eq cka) list_to_Word.
  Proof.
    intros l;induction l;simpl;intros m h.
    - apply eq_list_comm_nil in h as ->;reflexivity.
    - apply eq_list_comm_cons in h as (m1&m2&->&h).
      transitivity (list_to_Word (a::m1++m2)).
      + unfold list_to_Word;simpl.
        rewrite (IHl _ h).
        reflexivity.
      + unfold list_to_Word;simpl.
        repeat rewrite map_app,WProd_app;simpl.
        transitivity ((t_var (Some a) ** WProd (map var_w m1)) ** WProd (map var_w m2));
          auto with proofs.
        transitivity ((WProd (map var_w m1)**t_var (Some a)) ** WProd (map var_w m2));
          auto with proofs.
  Qed.
  
  Lemma cKA_to_reg_theo_sem w e :
    cKA_sat w e -> list_to_Word w |=(cka)= reg_to_Reg e.
  Proof.
    intros h;apply cKA_sat_KA_sat in h as (l&el&hl).
    apply gnl_theo_sat_decompose.
    apply KA_to_reg_theo_sem in hl.
    apply gnl_theo_sat_decompose in hl as (t&et&ht).
    exists t;split;auto.
    rewrite el,et;reflexivity.
  Qed.

  Global Instance gnl_sat_creg_theo_proper w :
    Proper (cKA ==> Basics.impl) (gnl_theo_sat cka w).
  Proof.
    unfold Basics.impl;intros ? ? [] h3;simpl in *.
    + destruct h3 as (s1&s2&h1&h2&h3).
      cut (cka |- w =T= s2).
      * intros ->;assumption.
      * rewrite h1,h2.
        auto with proofs.
    + exists 1_w,w;repeat split;auto with proofs.
    + destruct h3 as (s1&s2&h1&h2&h3).
      exists s2,s1;repeat split;eauto with proofs.
  Qed.

  Lemma reg_theo_to_cKA_sem w e :
    w |=(cka)= e -> cKA_sat (Word_to_list w) (Reg_to_reg e).
  Proof.
    intros h;apply cKA_sat_KA_sat.
    apply gnl_theo_sat_decompose in h as (t&et&ht).
    exists (Word_to_list t);split.
    - rewrite et;reflexivity.
    - apply reg_theo_to_KA_sem.
      apply gnl_theo_sat_decompose.
      exists t;split;auto with proofs.
  Qed.

  Theorem cKA_reg_semantic_correspondance1 w e :
    w |=(cka)= e <-> cKA_sat (Word_to_list w) (Reg_to_reg e).
  Proof.
    split;[apply reg_theo_to_cKA_sem|].
    intro h;apply cKA_to_reg_theo_sem in h.
    rewrite <- Word_to_list_and_back.
    rewrite <- Reg_to_reg_and_back.
    assumption.
  Qed.
  
  Theorem cKA_reg_semantic_correspondance2 w e :
    cKA_sat w e <-> list_to_Word w |=(cka)= reg_to_Reg e.
  Proof.
    split;[apply cKA_to_reg_theo_sem|].
    intro h;apply reg_theo_to_cKA_sem in h.
    rewrite list_to_Word_and_back in h.
    rewrite reg_to_Reg_and_back in h.
    assumption.
  Qed.

  Lemma ewp_r_comm_spec e : ewp_r e = true <-> 1_w |=(cka)= e.
  Proof.
    unfold ewp_r;rewrite r_ewp_spec.
    replace [] with (@Word_to_list A 1_w) by reflexivity.
    rewrite cKA_reg_semantic_correspondance1.
    rewrite cKA_sat_KA_sat.
    split;[intro h;exists [];repeat split;auto|].
    intros (l&E&h).
    apply eq_list_comm_nil in E as ->.
    apply h.
  Qed.
  
  Lemma ewp_r_alt_comm_spec e : ewp_r e = true <-> cKA |- 1_r ≤ e.
  Proof.
    unfold ewp_r;split;intro h.
    - rewrite r_ewp_alt_spec in h;apply KA_to_reg_theo in h.
      simpl in h.
      repeat rewrite Reg_to_reg_and_back in h.
      rewrite <- h;auto with proofs.
    - apply ewp_r_comm_spec.
      eapply gnl_theo_sat_proper;[apply gnl_sat_creg_theo_proper|reflexivity|apply h|].
      unfold gnl_theo_sat;reflexivity.
  Qed.

  Lemma cKA_iff_cka_KA w e :
    w |=(cka)= e <-> exists u, cka |- w =T= u /\ u |=(ka)= e.
  Proof.
    rewrite cKA_reg_semantic_correspondance1.
    setoid_rewrite KA_reg_semantic_correspondance1.
    rewrite cKA_sat_KA_sat.
    split;intros (u&E&h).
    - apply list_to_Word_eq_list_comm in E.
      rewrite Word_to_list_and_back in E.
      exists (list_to_Word u);split;auto.
      rewrite list_to_Word_and_back;assumption.
    - apply Word_to_list_eq_list_comm in E.
      exists (Word_to_list u);split;auto.
  Qed.
End cka_to_gnl.
