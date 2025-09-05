(** * gnl_alg.depth : Depth algebra *)

Require Import prelim.

Section depth.
  (** * Definitions *)

  (** The depth algebra is parametrized by a set (type) of operators. *)
  
  Context { O : Set } {decO : decidable_set O}.

  (** The depth algebra has three kinds of elements : *)
  (** - the constants [d_one] and [d_var]; *)
  (** - elements of the shape [d_op o n], where [o] is an operator and [n] is a natural number. *)

  Inductive depth : Set :=
  | d_one | d_var : depth
  | d_op : O -> nat -> depth. 

  (** This set is easily decidable. *)
  
  Global Instance depth_dec : decidable_set depth.
  Proof.
    intro d;induction d;intros [];try (right;discriminate)||(left;reflexivity).
    destruct (eq_dec n n0).
    - destruct (eq_dec o o0).
      + left;subst;reflexivity.
      + right;intro h;inversion h;tauto.
    - right;intro h;inversion h;tauto. 
  Qed.

  (** For every operator [o], a binary product over depth elements is defined. *)
  
  Definition d_prod o : depth -> depth -> depth :=
    fun d1 d2 =>
      match d1,d2 with
      | d_one,d | d,d_one => d
      | d_var,d_var => d_op o 0
      | d_op o' n,d_var | d_var,d_op o' n =>
                            if o' =?= o
                            then d_op o n
                            else d_op o (S n)
      | d_op o1 n,d_op o2 m =>
          if o1 =?= o
          then
            if o2 =?= o
            then d_op o (max n m)
            else d_op o (max n (S m))
          else
            if o2 =?= o
            then d_op o (max (S n) m)
            else d_op o (S (max n m))
      end.

  (** Finally, we define comparison operators between depth elements. *)
  (** The first one is strict while the other is reflexive. *)
  
  Definition depth_lt : relation depth :=
    fun d1 d2 =>
      match d1,d2 with
      | d_one,d_one => False
      | d_one,_ => True
      | _,d_one => False
      | d_var,d_var => False
      | d_var,_ => True
      | _,d_var => False
      | d_op _ n,d_op _ m=> lt n m
      end.

  Definition depth_le : relation depth :=
    fun d1 d2 =>
      match d1,d2 with
      | d_one,_ => True
      | _,d_one => False
      | d_var,_ => True
      | _,d_var => False
      | d_op o n,d_op o' m =>
          if o =?= o'
          then n <= m
          else lt n m
      end.

  (** * Properties of the depth algebra *)

  (** ** Comparison operators *)
  (** [depth_lt] implies [depth_le]. *)

  Global Instance depth_lt_incl_depth_le :
    subrelation depth_lt depth_le.
  Proof.
    intros [] [];simpl;try rewrite PeanoNat.Nat.lt_eq_cases;
      try intuition (tauto||discriminate||auto).
    destruct (o =?= o0);subst;auto.
    lia.
  Qed.

  (** [depth_lt] is a strict order. *)
  
  Global Instance strictorder_depth_lt : StrictOrder depth_lt.
  Proof.
    split.
    - intros [];unfold complement;simpl;try tauto||lia.
    - repeat intros [];simpl;try tauto||lia.
  Qed.
  
  (** [depth_le] is a preorder. *)

  Global Instance preorder_depth_le : PreOrder depth_le.
  Proof.
    split.
    - intros [];simpl;auto.
      rewrite eq_dec_eq;reflexivity.
    - intros [| |o1] [| |o2] [| |o3];simpl;try tauto.
      destruct (o1 =?= o2),(o2=?=o3),(o1=?=o3);subst;try tauto||lia.
  Qed.

  (** [depth_le] and [depth_lt] are tightly connected. *)
  
  Lemma depth_lt_le d1 d2 : depth_le d1 d2 <-> d1 = d2 \/ depth_lt d1 d2.
  Proof.
    destruct d1,d2;simpl;try rewrite PeanoNat.Nat.lt_eq_cases;
      try intuition (tauto||discriminate||auto).
    - destruct (o =?= o0);subst;auto.
      apply PeanoNat.Nat.lt_eq_cases in H as [h| ->];auto.
    - inversion H0;subst;clear H0.
      rewrite (eq_dec_eq o0);reflexivity.
    - destruct (o =?= o0);subst;auto.
      lia.
  Qed.

  Lemma depth_le_lt d1 d2 : depth_lt d1 d2 <-> d1 <> d2 /\ depth_le d1 d2.
  Proof.
    destruct d1,d2;simpl;try rewrite PeanoNat.Nat.lt_eq_cases;
      try intuition (tauto||discriminate||auto).
    - inversion H0;lia.
    - destruct (o =?= o0);subst;lia.
    - destruct (o =?= o0);subst;try lia.
      apply PeanoNat.Nat.lt_eq_cases in H1 as [h| ->];auto.
      exfalso;apply H0;reflexivity.
  Qed.

  (** Heterogeneous forms of transitivity. *)

  Lemma depth_trans_lt_le d1 d2 d3 :
    depth_lt d1 d2 -> depth_le d2 d3 -> depth_lt d1 d3.
  Proof.
    destruct d1,d2,d3;simpl;try tauto||lia.
    destruct (o0 =?= o1);lia.
  Qed.

  Lemma depth_trans_le_lt d1 d2 d3 :
    depth_le d1 d2 -> depth_lt d2 d3 -> depth_lt d1 d3.
  Proof. 
    destruct d1,d2,d3;simpl;try tauto||lia.
    destruct (o =?= o0);lia.
  Qed.

  (** [depth_lt] is a well_founded relation. *)
  
  Lemma well_founded_depth_lt : well_founded depth_lt.
  Proof.
    intros d.
    assert (ho : Acc depth_lt d_one) by (apply Acc_intro;intros [];simpl;tauto).
    assert (hv : Acc depth_lt d_var) by (apply Acc_intro;intros [];simpl;tauto).
    cut (forall N o n, n <= N -> Acc depth_lt (d_op o n)).
    - intros hyp;apply Acc_intro;intros [] h;auto.
      apply (hyp n o);reflexivity.
    - induction N;intros o n hn.
      + replace n with 0 by lia.
        split;apply Acc_intro;intros [] h;simpl in *;lia||auto.
      + split;apply Acc_intro;intros [] h;simpl in *;lia||(apply IHN;lia)||auto.
  Qed.

  (** ** Properties of the products *)

  (** Every product is monotone w.r.t. [depth_le]. *)
  Global Instance d_prod_le_le_le o :
    Proper (depth_le ==> depth_le ==> depth_le) (d_prod o).
  Proof.
    intros [| |i1] [| |i2] h1 [| |j1] [| |j2] h2;simpl in *;
      try destruct (i1 =?= o);
      try destruct (i2 =?= o);
      try destruct (j1 =?= o);
      try destruct (j2 =?= o);
      try destruct (i1 =?= i2);
      try destruct (j1 =?= j2);subst;simpl;
      repeat (rewrite eq_dec_eq in * )
      || (rewrite eq_dec_neq in * by (intros ->;tauto));
      try tauto||lia;
      try (destruct n1;tauto||lia)
      || (destruct n2;tauto||lia).
    - destruct n1,n2;tauto||lia.
    - destruct n1,n2;tauto||lia.
  Qed.

  (** Products are commutative, associative, and [d_one] is their unit. *)

  Lemma d_prod_comm o d1 d2 : d_prod o d1 d2 = d_prod o d2 d1.
  Proof.
    destruct d1,d2;simpl;try rewrite eq_dec_eq;try tauto||lia.
    destruct (o0 =?= o),(o1 =?= o);subst;
      repeat rewrite eq_dec_eq
      || rewrite eq_dec_neq by (intros ->;tauto);f_equal;try lia.
    - destruct n;lia.
    - destruct n0;lia.
  Qed.

  Lemma d_prod_assoc o d1 d2 d3 : d_prod o d1 (d_prod o d2 d3) = d_prod o (d_prod o d1 d2) d3.
  Proof.
    destruct d1 as [| |o1],d2 as [| |o2],d3 as [| |o3];simpl;try rewrite eq_dec_eq;try tauto||lia;
      try destruct (o1 =?= o);try destruct (o2 =?= o);try destruct (o3 =?= o);subst;simpl;
      repeat rewrite eq_dec_eq
      || rewrite eq_dec_neq by (intros ->;tauto);f_equal;try lia.
    - destruct n1;lia.
    - destruct n0,n1;simpl;lia.
    - destruct n0,n1;simpl;lia.
    - destruct n1;lia.
  Qed.

  Lemma d_prod_e_one o d : d_prod o d d_one = d.
  Proof. destruct d;simpl;auto. Qed.

  Lemma d_prod_one_e o d : d_prod o d_one d = d.
  Proof. destruct d;simpl;auto. Qed.
  
  (** Products are increasing with respect to both arguments. *)

  Lemma d_prod_incr_l o d1 d2 : depth_le d1 (d_prod o d1 d2).
  Proof.
    destruct d1,d2;simpl;try rewrite eq_dec_eq;try tauto||lia;
      try (now destruct (o0 =?= o);auto)
      || (now destruct (o =?= o0);tauto||lia).
    - destruct (o0 =?= o).
      + subst;rewrite eq_dec_eq;reflexivity.
      + rewrite eq_dec_neq by assumption.
        lia.
    - destruct (o0 =?= o),(o1 =?= o);subst;
        repeat rewrite eq_dec_eq
        || rewrite eq_dec_neq by (intros ->;tauto);try lia.
      destruct n0;lia.
  Qed.

  Lemma d_prod_incr_r o d1 d2 : depth_le d2 (d_prod o d1 d2).
  Proof. rewrite d_prod_comm;apply d_prod_incr_l. Qed.

  (** The following property will also be useful : *)
  Lemma d_prod_o_d_prod_o'_lt o o' d1 d2 d3 :
    o' <> o -> depth_lt d_one d1 -> depth_lt d_one d2 -> depth_lt d_one d3 ->
    depth_lt (d_prod o' d1 d2) (d_prod o (d_prod o' d1 d2) d3).
  Proof.
    intros n h1 h2 h3.
    destruct d1 as [| |o1 n1], d2 as [| |o2 n2], d3 as [| |o3 n3];
      simpl in *;auto;
      try destruct (o1 =?= o);try destruct (o2 =?= o);try destruct (o3 =?= o);subst;simpl;
      repeat (rewrite eq_dec_neq by (intros ->;tauto);simpl)
      || rewrite eq_dec_eq;
      try destruct (o1 =?= o');try destruct (o2 =?= o');subst;simpl;
      repeat (rewrite eq_dec_neq by (intros ->;tauto);simpl)
      || rewrite eq_dec_eq;
      simpl;try tauto||lia;
      try (destruct n1;simpl;tauto||lia);
      try (destruct n2;simpl;tauto||lia);
      try (destruct n3;simpl;tauto||lia);
      try (destruct n1,n2;simpl;tauto||lia);
      try (destruct n1,n3;simpl;tauto||lia);
      try (destruct n2,n3;simpl;tauto||lia);
      try (destruct n1,n2,n3;simpl;tauto||lia);
      try (destruct n3 as [|[|]];simpl;tauto||lia).
  Qed.
  
  (** * Lists of depth elements *)

  (** ** Basic operations and properties *)

  (** We now turn our attention to _lists of depth elements_, interpreted as   *)
  (** finite sets, i.e. considered up-to [≈set]]. *)

  (** We will (strictly) order such lists as follows : [l] is smaller than [m] *)
  (** if [m] is not empty and if every element in [l] is strictly smaller than *)
  (** some element in [m]. *)
  
  Definition depth_list_inf : relation (list depth) :=
    fun l m =>
      m <> [] /\ (forall d, In d l -> exists d', In d' m /\ depth_lt d d').

  (** This definition does yield a strict order. *)
  
  Global Instance strict_order_depth_list_inf : StrictOrder depth_list_inf.
  Proof.
    split;unfold depth_list_inf;simpl.
    - intros l h.
      cut (exists d, In d l /\ depth_lt d d);
        [intros (d&h1&h2);apply strictorder_depth_lt in h2;tauto|].
      induction l as [|d l];[tauto|destruct l as [|d' l]].
      + exists d;split;[now left|].
        assert (In d [d]) as ih by now left.
        apply h in ih as (d'&[<-|f]&ih);auto.
        exfalso;apply f.
      + destruct h as (_&h).
        exfalso.
        assert (In d (d::d'::l)) as hd by (now left).
        apply h in hd as (?&hd1&hd2).
        assert (In d' (d::d'::l)) as hd' by (now right;left).
        apply h in hd' as (?&hd1'&hd2').
        destruct hd1 as [<-|hd1];[apply strictorder_depth_lt in hd2;tauto|].
        destruct hd1' as [<-|hd1'].
        * destruct IHl as (D&hD1&hD2).
          -- split;[discriminate|].
             intros x' hx1.
             assert (hx2 : In x' (d::d'::l)) by now right.
             apply h in hx2 as (x''&hx2&hx3).
             destruct hx2 as [<-|hx2].
             ++ exists x;split;auto.
                transitivity d;auto.
             ++ exists x'';auto.
          -- apply strictorder_depth_lt in hD2;tauto.
        * destruct IHl as (D&hD1&hD2).
          -- split;[discriminate|].
             intros x' hx1.
             assert (hx2 : In x' (d::d'::l)) by now right.
             apply h in hx2 as (x''&hx2&hx3).
             destruct hx2 as [<-|hx2].
             ++ exists x;split;auto.
                transitivity d;auto.
             ++ exists x'';auto.
          -- apply strictorder_depth_lt in hD2;tauto.
    - intros l1 l2 l3 h1 h2;split;[tauto|].
      intros d hd.
      apply h1 in hd as (d'&hd&hlt1).
      apply h2 in hd as (d''&hd&hlt2).
      exists d'';split;auto.
      transitivity d';auto.
  Qed.

  (** This ordering is impervious to commutativity and idempotency. *)

  Global Instance eq_list_depth_list_lt :
    Proper (eq_list ==> eq_list ==> iff) depth_list_inf.
  Proof.
    cut (Proper (eq_list ==> eq_list ==> Basics.impl) depth_list_inf).
    - intros hyp  l l' h1 m m' h2;split;apply hyp;rewrite h1||rewrite h2;reflexivity.
    - intros l l' h1 m m' h2 (n1&h3);split.
      + intros ->.
        destruct m;[tauto|].
        pose proof (h2 d) as f;simpl in f;tauto.
      + intros d hd.
        apply h1,h3 in hd as (d'&hd&hlt).
        exists d';split;auto.
        apply h2,hd.
  Qed.

  (** We define products and stars for each operator : *)
  
  Definition DProd o : list depth -> list depth -> list depth :=
    fun l1 l2 => concat (map (fun d => map (d_prod o d) l2) l1).

  Definition DStar o : list depth -> list depth :=
    fun l => [d_one]++l++DProd o l l.

  Definition DIter o : list depth -> list depth :=
    fun l => l++DProd o l l.

  (** The elements of [DProd o l m] are the results of taking a pair of elements from *)
  (** [l] and [m] and taking their [o]-product. *)
  
  Lemma DProd_spec o l m d :
    In d (DProd o l m) <-> exists d1 d2, d = d_prod o d1 d2 /\ In d1 l /\ In d2 m.
  Proof.
    unfold DProd.
    rewrite in_concat.
    setoid_rewrite in_map_iff.
    firstorder.
    - subst.
      apply in_map_iff in H0.
      firstorder.
    - subst.
      exists (map (d_prod o x) m);firstorder.
      apply in_map_iff;exists x0;tauto.
  Qed.

  (** Crucial property of the star : [star o l] is equivalent to its [o]-product *)
  (** with the list [d_one::l]. *)

  Ltac simpl_depth :=
    simpl;repeat rewrite eq_dec_eq;repeat rewrite eq_dec_neq by (intros -> ;tauto);
    simpl.
  Ltac solve_depth :=
    now simpl_depth;auto.

  Lemma DIter_spec o l d : In d (DIter o l) <-> exists L, d = fold_right (d_prod o) d_one L 
                                                          /\ incl L l
                                                          /\ L <> [].
  Proof.
    split.
    - unfold DIter;rewrite in_app_iff;intros [h|h].
      + exists [d];repeat split;auto.
        * simpl;symmetry;apply d_prod_e_one.
        * intros ? [<-|F];[|exfalso];auto.
        * discriminate.
      + apply DProd_spec in h as (d1&d2&->&h1&h2).
        exists [d1;d2];simpl.
        rewrite d_prod_e_one.
        repeat split.
        * intros ? [<-|[<-|F]];[| |exfalso];auto.
        * discriminate.
    - intros (L&->&h&n);revert h n;induction L;simpl;intros h n;[tauto|].
      clear n;apply incl_cons_inv in h as (h1&h2).
      assert (L = [] \/ L <> []) as [->|n] by (destruct L;[now left|right;discriminate]).
      + clear h2;simpl.
        rewrite d_prod_e_one.
        apply in_app_iff;now left.
      + pose proof (IHL h2 n) as h3.
        apply in_app_iff in h3 as [h3|h3].
        * apply in_app_iff;right;apply DProd_spec.
          exists a, (fold_right (d_prod o) d_one L);repeat split;auto.
        * apply DProd_spec in h3 as (d1&d2&->&h3&h4).
          unfold DIter.
          repeat setoid_rewrite DProd_spec||setoid_rewrite in_app_iff.
          clear IHL h2 n L.
          destruct a as [| |i n],d1 as [| |j m],d2 as [| |k k'];simpl;try (now firstorder);
            try destruct (i =?= o);try destruct (j =?= o);try destruct (k=?=o);subst;
            repeat rewrite eq_dec_eq;
            repeat
              (let E := fresh "E" in
               let h := fresh "h" in
               match goal with
               | |- (In (d_op o (Nat.max ?k (Nat.max ?n ?m))) l) \/ _ =>
                   destruct (PeanoNat.Nat.max_spec n m) as [h|h];
                   destruct h as (h&->)||destruct h as (h&E);
                   try (tauto||lia)
               | |- (In (d_op o (Nat.max (Nat.max ?n ?m) ?k)) l) \/ _ =>
                   destruct (PeanoNat.Nat.max_spec n m) as [h|h];
                   destruct h as (h&->)||destruct h as (h&E);
                   try (tauto||lia)
               | |- (In (d_op o (Nat.max ?n ?m)) l) \/ _ =>
                   destruct (PeanoNat.Nat.max_spec n m) as [h|h];
                   destruct h as (h&->)||destruct h as (h&E);
                   try (tauto||lia)
               | |- (In (d_op o (S (Nat.max ?n ?m))) l) \/ _ =>
                   destruct (PeanoNat.Nat.max_spec n m) as [h|h];
                   destruct h as (h&->)||destruct h as (h&E);
                   try (tauto||lia)
               | |- (In (d_op o (match ?k with 0 => _ | S _ => _ end)) l) \/ _ =>
                   case_eq k;intros;subst;simpl;try (tauto||lia)
               end;simpl);repeat right;
            try (now exists d_var,d_var;repeat split;auto)
            || (exists (d_op o k'),d_var;repeat split;simpl;auto;solve_depth)
            || (exists (d_op k k'),d_var;repeat split;simpl;auto;solve_depth)
            || (exists (d_op o m),d_var;repeat split;simpl;auto;solve_depth)
            || (exists (d_op j m),d_var;repeat split;simpl;auto;solve_depth)
            || (exists (d_op i n),d_var;repeat split;simpl;auto;solve_depth)
            || (exists (d_op o n),d_var;repeat split;simpl;auto;solve_depth)
            || (exists (d_op k k'),(d_op o n);repeat split;simpl_depth;auto;destruct n;f_equal;lia)
            || (exists (d_op j m),(d_op o n);repeat split;simpl_depth;auto;destruct n;f_equal;lia)
            || (exists (d_op k k'),(d_op o m);repeat split;simpl_depth;auto;destruct m;f_equal;lia)
            || (exists (d_op i n),(d_op o m);repeat split;simpl_depth;auto;destruct m;f_equal;lia)
            || (exists (d_op j m),(d_op o k');repeat split;simpl_depth;auto;destruct k';f_equal;lia)
            || (exists (d_op i n),(d_op o k');repeat split;simpl_depth;auto;destruct k';f_equal;lia).
          -- destruct (PeanoNat.Nat.max_spec m k') as [h5|h5];destruct h5 as (h5&E);
               rewrite E in H;subst.
             ++ exists (d_op o (S n1)),(d_op o m);repeat split;simpl_depth;auto;destruct m;
                  f_equal;lia.
             ++ exists (d_op o (S n1)),(d_op o k');repeat split;simpl_depth;auto;destruct m;
                  f_equal;lia.
          -- (exists (d_op k k'),(d_op i n);repeat split;simpl_depth;auto;destruct n;f_equal;lia).
          -- (exists (d_op k k'),(d_op j m);repeat split;simpl_depth;auto;destruct n;f_equal;lia).
          -- (exists (d_op k k'),(d_op i n);repeat split;simpl_depth;auto;destruct n;f_equal;lia).
  Qed.

  Lemma DIter_unfold_left o l : l++DProd o l (DIter o l) ≈set DIter o l. 
  Proof.
    intro d.
    repeat setoid_rewrite DIter_spec||setoid_rewrite DProd_spec||setoid_rewrite in_app_iff.
    split.
    - intros [h|(d1&d2&->&h1&L&->&h2&h3)].
      + exists [d];repeat split;simpl;auto using d_prod_e_one.
        * intros ? [<-|F];[|exfalso];auto.
        * discriminate.
      + exists (d1::L);simpl;repeat split.
        * intros ? [<-|h];[|apply h2];auto.
        * discriminate.
    - intros ([|d1 [|d2 L]]&->&h1&h2);[tauto| |];clear h2.
      * simpl;rewrite d_prod_e_one;left.
        apply h1;now left.
      * right.
        exists d1,(fold_right (d_prod o) d_one (d2::L));repeat split;auto.
        -- apply h1;now left.
        -- exists (d2::L);repeat split;auto.
           ++ intros ? ?;apply h1;now right.
           ++ discriminate.
  Qed.

  Lemma DStar_spec o l d : In d (DStar o l) <-> exists L, d = fold_right (d_prod o) d_one L 
                                                          /\ incl L l.
  Proof.
    unfold DStar.
    replace (l++DProd o l l) with (DIter o l) by reflexivity.
    repeat setoid_rewrite DIter_spec||setoid_rewrite DProd_spec||setoid_rewrite in_app_iff.
    split.
    - intros [[<-|F]|(L&->&h1&h2)];[exists []|exfalso;auto|exists L];repeat split;auto.
      intros ? F;exfalso;auto.
    - intros ([|d' L]&->&h).
      + left;simpl;auto.
      + right;exists (d'::L);repeat split;auto.
        discriminate.
  Qed.


  Lemma DStar_unfold_left o l : DProd o (d_one::l) (DStar o l) ≈set DStar o l. 
  Proof.
    intro d.
    repeat setoid_rewrite DStar_spec||setoid_rewrite DProd_spec||setoid_rewrite in_app_iff.
    split.
    - intros (d1&d2&->&[<-|h1]&L&->&h2).
      + exists L;repeat split;auto.
      + exists (d1::L);repeat split;auto.
        intros ? [<-|h];[|apply h2];auto.
    - intros ([|d' L]&->&h).
      + exists d_one,d_one;simpl;repeat split;auto.
        exists [];repeat split;auto.
      + exists d',(fold_right (d_prod o) d_one L);repeat split;auto.
        * right;apply h;now left.
        * exists L;repeat split;auto.
          intros ? ?;apply h;now right.
  Qed.

  (** ** Well-founded order on lists of depth elements *)

  (** We now set out to show that [depth_list_inf] is a well founded relation. *)

  (** We start by defining the following function. It takes a list of operators [Op] *)
  (** and a depth element [d] and returns the list of all the depth elements smaller *)
  (** than [d] that only use operators from [Op]. *)
  
  Definition smaller_elt Op d :=
    match d with
    | d_one => []
    | d_var => [d_one]
    | d_op o 0 => [d_one;d_var]
    | d_op o (S n) =>
        d_one::d_var::concat(map (fun d => map d (List.seq 0 (S n)))
                               (map d_op Op))
    end.

  (** To analyse this function we formalize what it means to _only use operators from [Op]_.*)
  (** Towards that end, we extract from a depth element the operator it carries, if any. *)
  
  Definition get_op d :=
    match d with
    | d_one | d_var => None
    | d_op o _ => Some o
    end.

  (** Then we define the predicate [in_sig d Op], which signifies that any operator present *)
  (** in [d] belongs to the list [Op]. *)
  
  Definition in_sig d Op :=
    match get_op d with
    | None => True
    | Some o => In o Op
    end.

  (** The specification of [smaller_elt] is as follows : a depth element belongs to the list *)
  (** [smaller_elt Op d'] iff it is strictly smaller than [d'] and only uses operators *)
  (** from [Op]. *)
    
  Lemma smaller_elt_spec Op d d' :
    In d (smaller_elt Op d') <-> depth_lt d d' /\ in_sig d Op.
  Proof.
    unfold smaller_elt,depth_lt.
    destruct d as [| |o n],d' as [| |o' [|m]];simpl;try rewrite in_app_iff;simpl;
      repeat rewrite in_map_iff; repeat setoid_rewrite in_seq;
      try (now firstorder (discriminate||lia||auto));try (inversion H;subst;lia).
    split.
    - intros [E|[E|h]];try inversion E.
      apply in_concat in h as (l&hl&h).
      apply in_map_iff in hl as (d'&<-&h2).
      apply in_map_iff in h2 as (o''&<-&h2).
      destruct h as [E|h];[|apply in_map_iff in h as (k&E&h)];
        inversion E;subst;clear E.
      + split;[lia|unfold in_sig;simpl];auto.
      + apply in_seq in h;split;[lia|unfold in_sig;simpl];auto.
    - intros (hn&hI).
      unfold in_sig in hI;simpl in hI.
      repeat right.
      apply in_concat.
      eexists;split.
      + apply in_map_iff.
        exists (d_op o);split;[reflexivity|].
        apply in_map_iff;exists o;split;auto.
      + destruct n.
        * now left.
        * right;apply in_map_iff;exists (S n);split;auto.
          apply in_seq;lia.
  Qed.

  (** [smaller_elt] enjoys some monotonicity property: *)
  
  Lemma smaller_elt_proper :
    Proper (@incl _ ==> depth_le ==> @incl _) smaller_elt.
  Proof.
    intros O1 O2 h d1 d2 h' d;repeat rewrite smaller_elt_spec.
    intros (D&S);split;auto.
    - eapply depth_trans_lt_le;eauto.
    - unfold in_sig;destruct d;simpl in *;auto.
  Qed.

  (** The function [Operators] extracts from a list of depth elements *)
  (** the list of operators used in its elements. *)

  Fixpoint Operators (l : list depth) : list O :=
    match l with
    | [] => []
    | d_one::l | d_var::l => Operators l
    | d_op o _:: l => o::Operators l
    end.

  (** Indeed, [o] belongs to [Operators l] iff [d_op o n] belongs to [l] for some [n]. *)
  
  Lemma Operators_spec o l : In o (Operators l) <-> exists n, In (d_op o n) l.
  Proof.
    induction l as [|[]];simpl;auto.
    - firstorder.
    - rewrite IHl;clear IHl;firstorder discriminate.
    - rewrite IHl;clear IHl;firstorder discriminate.
    - rewrite IHl;clear IHl.
      destruct (o0 =?= o);subst.
      + split;auto.
        intros _;exists n;now left.
      + split.
        * intros [F|(k&h)];[exfalso;tauto|].
          exists k;right;auto.
        * intros (k&[E|h]);[inversion E;subst;clear E;tauto|].
          right;exists k;tauto.
  Qed.

  (** As a result, every element in [l] only uses operators from [Operators l]. *)
  
  Lemma Operators_in_sig d l : In d l -> in_sig d (Operators l).
  Proof.
    intro h;destruct d;unfold in_sig;simpl;auto.
    apply Operators_spec;exists n;auto.
  Qed.

  (** We now start proving that [depth_list_inf] is well founded. That means showing *)
  (** the predicate [Acc depth_list_inf l] (called _accessibility_) for every list of *)
  (** depth elements. *)

  (** We first show that if [l] is accessible and [m] is contained in [l], then [m] is *)
  (** also accessible. *)

  Lemma Acc_inf :
    forall l m, Acc depth_list_inf l -> (incl m l) -> Acc depth_list_inf m.
  Proof.
    intros l m hl;revert m;induction hl;intros.
    apply Acc_intro.
    intros y hy.
    apply H.
    split.
    - intros ->.
      destruct m.
      + apply hy;auto.
      + apply (H1 d);now left.
    - intros d hd.
      apply hy in hd as (d'&hd&hlt).
      exists d';split;auto.
  Qed.

  (** Then we show that some well-chosen lists are accessible. *)

  (** The empty list is accessible. *)
    
  Lemma Acc_nil : Acc depth_list_inf [].
  Proof. apply Acc_intro;intros m h; exfalso;apply h;reflexivity. Qed.

  (** The list [d_one] also is. *)
  
  Lemma Acc_one : Acc depth_list_inf [d_one].
  Proof.
    apply Acc_intro.
    intros [|d] h;simpl.
    - apply Acc_nil.
    - exfalso.
      assert (f : In d (d::l)) by now left.
      apply h in f as (d'&[<-|f]&h').
      + destruct d;simpl in h';tauto.
      + apply f.
  Qed.

  (** So is the list [d_one;d_var]. *)
  
  Lemma Acc_one_var : Acc depth_list_inf [d_one;d_var].
  Proof.
    apply Acc_intro.
    intros [|d] h;simpl.
    - apply Acc_nil.
    - apply (Acc_inf [d_one]).
      + apply Acc_one.
      + intros d' hd'.
        apply h in hd'.
        destruct hd' as (d''&[<-|[<- |f']]&h').
        * destruct d';simpl in h';tauto.
        * destruct d';simpl in *;tauto.
        * exfalso;apply f'.
  Qed.
  
  (** By performing an induction on [n], and leveraging our results so far, *)
  (** we may prove that every list of the form [smaller_elt Op (d_op o n)]  *)
  (** is accessible. *)

  Lemma Acc_smaller_seq Op o n : Acc depth_list_inf (smaller_elt Op (d_op o n)).
  Proof.
    revert Op;induction n;intros.
    - simpl;apply Acc_one_var.
    - apply Acc_intro.
      intros y hy.
      apply Acc_intro;intros z hz.
      apply (Acc_inf (smaller_elt (Operators z) (d_op o n)) z);auto.
      intros d hd.
      apply smaller_elt_spec.
      split;[|apply Operators_in_sig;auto].
      apply hz in hd as (d'&h1&h2).
      apply hy in h1 as (d''&h1&hlt).
      apply smaller_elt_spec in h1.
      destruct d,d',d'';simpl in *;tauto||lia.
  Qed.

  (** As it turns out, every list of depth element is included in some list of the above form. *)
    
  Lemma smaller_super_set o l :
    exists m, incl l (smaller_elt (Operators l) (d_op o m)). 
  Proof.
    induction l.
    - exists 0;intro;simpl;tauto.
    - destruct IHl as (m&ih).
      destruct a.
      + exists m;intros d [<-|hd].
        * destruct m;simpl;auto.
        * apply ih;auto.
      + exists m;intros d [<-|hd].
        * destruct m;simpl;auto.
        * apply ih;auto.
      + destruct (PeanoNat.Nat.lt_ge_cases n m).
        * exists m;intros d [<-|hd].
          -- apply smaller_elt_spec.
             split;[simpl;assumption|].
             unfold in_sig;simpl;auto.
          -- apply ih in hd.
             eapply smaller_elt_proper,hd;[|reflexivity].
             intros i hi;now right.
        * exists (S n);intros d [<-|hd].
          -- apply smaller_elt_spec.
             split.
             ++ simpl;lia.
             ++ unfold in_sig;simpl;auto.
          -- apply smaller_elt_spec.
             apply ih in hd.
             apply smaller_elt_spec in hd as (h1&h2).
             split.
             ++ transitivity (d_op o m);auto.
                simpl;lia.
             ++ unfold in_sig in * ;simpl.
                destruct (get_op d);simpl in *;auto.
  Qed.

  (** Therefore, every list is accessible hence [depth_list_inf] is well founded. *)
  
  Theorem well_founded_depth_list_inf : well_founded depth_list_inf.
  Proof.
    intros l.
    cut ((exists o : O, True) \/ incl l [d_one;d_var]).
    intros [(o&_)|h].
    - destruct (smaller_super_set o l) as (m&hm).
      apply (Acc_inf (smaller_elt (Operators l) (d_op o m))).
      + apply Acc_smaller_seq.
      + intros d;apply hm.
    - eapply Acc_inf;[apply Acc_one_var|apply h].
    - case_eq (Operators l).
      + intros h;right.
        induction l as [|[]];[intro;simpl;tauto| | |];simpl in h.
        * intros ? [<-|h'];[left;reflexivity|].
          apply IHl;auto.
        * intros ? [<-|h'];[right;left;reflexivity|].
          apply IHl;auto.
        * discriminate.
      + intros o _ _;left;exists o;auto.
  Qed.

  (** * Extra result *)

  (** If a list [l] is below a concatenation [m1++m2], it can be decomposed in *)
  (** two sublists that are respectively below [m1] and [m2]. *)
  
  Lemma depth_list_inf_app l m1 m2 :
    m1 <> [] -> m2 <> [] -> depth_list_inf l (m1++m2) ->
    exists l1 l2, l ≈set l1++l2
                  /\ depth_list_inf l1 m1
                  /\ depth_list_inf l2 m2.
  Proof.
    induction l;simpl;intros n1 n2 (h1&h2).
    - exists [],[];split;[|split].
      + reflexivity.
      + split;[assumption|simpl;tauto].
      + split;[assumption|simpl;tauto].
    - assert (h : In a (a::l)) by now left.
      apply h2 in h as (d&hd&hlt).
      destruct IHl as (l1&l2&E&hl1&hl2);auto.
      + split;auto.
        intros d' h.
        apply h2;now right.
      + apply in_app_iff in hd as [hd|hd].
        * exists (a::l1),l2.
          split;[|split].
          -- intro x;simpl.
             rewrite (E x);tauto.
          -- split;auto.
             intros d' [<-|h].
             ++ exists d;tauto.
             ++ apply hl1,h.
          -- assumption.
        * exists l1,(a::l2).
          split;[|split].
          -- intro x;simpl.
             rewrite (E x);repeat (rewrite in_app_iff;simpl);tauto.
          -- assumption.
          -- split;auto.
             intros d' [<-|h].
             ++ exists d;tauto.
             ++ apply hl2,h.
  Qed.
End depth.

