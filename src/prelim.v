(** * gnl_alg.prelim : Preliminaries *)

From Stdlib Require Export Relations.Relation_Definitions RelationClasses Classes.Morphisms.
From Stdlib Require Export List Decidable Lists.ListDec.
From Stdlib Require Export Psatz.
Export ListNotations.

Create HintDb proofs.

(** We will need to perform case analysis on lists from the right hand side. *)

Lemma list_last_dec {A} (l : list A) : {l = []} + {exists a l', l = l' ++ [a]}.
Proof.
  induction l.
  - left;reflexivity.
  - right.
    destruct IHl as [->|(b&l'&->)].
    + exists a, [];reflexivity.
    + exists b,(a::l');reflexivity.
Qed.

(** Levi's lemma is always handy. *)

Lemma Levi {X : Set} (a b c d : list X) :
  a ++ b = c ++ d ->
  (exists m, a = c++m /\ d = m++b) \/ (exists m, c = a++m /\ b = m++d).
Proof.
  revert b c d;induction a;intros b c d e;simpl in *;subst.
  - right;exists c;split;reflexivity.
  - destruct c;simpl in e.
    + subst;left;exists (a::a0);simpl;split;reflexivity.
    + inversion e;subst.
      apply IHa in H1 as [(m&->&->)|(m&->&->)].
      * left;exists m;split;reflexivity.
      * right;exists m;split;reflexivity.
Qed.

(** We will routinely need to lift relations from a type to the *)
(** corresponding option type. *)

Definition or_none {A : Set} (r : relation A) : relation (option A) :=
  fun a b =>
    match a,b with
    | None,None => True
    | Some a,Some b => r a b
    | _,_ => False
    end.

(** This operation preserves equivalence relations. *)

Global Instance or_none_equiv {X : Set} (r : relation X) :
  Equivalence r -> Equivalence (or_none r).
Proof.
  intros eq;split.
  - intros [];simpl;tauto||reflexivity.
  - intros [] [];simpl;tauto||(symmetry;assumption).
  - intros [] [] [];simpl;tauto||(intros;etransitivity;eassumption).  
Qed.

(* (** For every partial order, the corresponding equivalence relation is included in the order. *) *)

(* Global Instance partial_order_subrelation *)
(*   {X} (r s : relation X) {eq: Equivalence r} {po : PreOrder s}: *)
(*   PartialOrder r s -> subrelation r s. *)
(* Proof. intros PO e f E;rewrite E;reflexivity. Qed. *)

(** For every partial order, any map that is monotone with respect to the preorder is also *)
(** monotone with respect to the equivalence relation. *)

Global Instance partial_order_monotone_map_are_proper 
  {X} (rx sx : relation X) {eqx: Equivalence rx} {pox : PreOrder sx} {POx: PartialOrder rx sx}
  {Y} (ry sy : relation Y) {eqy: Equivalence ry} {poy : PreOrder sy} {POy: PartialOrder ry sy}
  (f : X -> Y) :
  Proper (sx ==> sy) f -> Proper (rx ==> ry) f.
Proof.
  intros proper x y h.
  apply POy;unfold Basics.flip;split;apply proper;rewrite h;reflexivity.
Qed.

Global Instance partial_order_monotone_map_are_proper_bin 
  {X} (rx sx : relation X) {eqx: Equivalence rx} {pox : PreOrder sx} {POx: PartialOrder rx sx}
  {Y} (ry sy : relation Y) {eqy: Equivalence ry} {poy : PreOrder sy} {POy: PartialOrder ry sy}
  {Z} (rz sz : relation Z) {eqz: Equivalence rz} {poz : PreOrder sz} {POz: PartialOrder rz sz}
  (f : X -> Y -> Z) :
  Proper (sx ==> sy ==> sz) f -> Proper (rx ==> ry ==> rz) f.
Proof.
  intros proper x x' hx y y' hy.
  apply POz;unfold Basics.flip;split;apply proper;rewrite hx||rewrite hy;reflexivity.
Qed.

(** * Decidable sets : types with decidable equality *)

Section dec.

  Class decidable_set (A : Set) := eq_dec : forall a b : A, {a = b} + {a <> b}.

  Infix " =?= " := eq_dec (at level 40).

  Lemma eq_dec_eq {A} {d: decidable_set A} {B} a (p q : B) :
    (if a =?= a then p else q) = p.
  Proof.
    case_eq (a =?= a).
    - reflexivity.
    - intros n _;exfalso;apply n;reflexivity.
  Qed.
  
  Lemma eq_dec_neq {A} {d: decidable_set A} {B} a b (p q : B) :
    a <> b -> (if a =?= b then p else q) = q.
  Proof.
    intro n;case_eq (a =?= b).
    - intros -> _;exfalso;apply n;reflexivity.
    - reflexivity.
  Qed.
  
End dec.

Infix " =?= " := eq_dec (at level 40).
(** Both the natural numbers and the booleans are decidable. *)
Global Instance nat_dec : decidable_set nat.
Proof.
  intro n;induction n;intros [|m].
  - left;reflexivity.
  - right;discriminate.
  - right;discriminate.
  - destruct (IHn m).
    + left;subst;reflexivity.
    + right;intro f;inversion f;apply n0,H0.
Qed.

Global Instance bool_dec : decidable_set bool.
Proof. intros [] [];(left;reflexivity)||(right;discriminate). Qed.

(** The sum, product or option of decidable sets is decidable. *)
Global Instance sum_dec {X Y} : decidable_set X -> decidable_set Y -> decidable_set (X+Y).
Proof.
  intros h1 h2 [] [];try (right;discriminate).
  - destruct (x =?= x0).
    + subst;left;reflexivity.
    + right;intro E;inversion E;tauto.
  - destruct (y =?= y0).
    + subst;left;reflexivity.
    + right;intro E;inversion E;tauto.
Qed.

Global Instance prod_dec {X Y} : decidable_set X -> decidable_set Y -> decidable_set (X*Y).
Proof.
  intros h1 h2 (x,y) (x',y'); destruct (x =?= x');destruct (y =?= y');
    try (subst;left;reflexivity);
    right;intro E;inversion E;tauto.
Qed.

Global Instance option_dec {X} : decidable_set X -> decidable_set (option X).
Proof.
  intros h1 [] [];try (right;discriminate).
  - destruct (x =?= x0).
    + subst;left;reflexivity.
    + right;intro E;inversion E;tauto.
  - left;reflexivity.
Qed.

(** The type with no element, is decidable. *)

Inductive Zero : Set := .

Global Instance dec_Zero : decidable_set Zero.
Proof. intros []. Qed.

(** The type with a single element, is decidable. *)
Inductive One : Set := sngl_elt.

Notation "•" := sngl_elt.

Global Instance One_dec : decidable_set One.
Proof. intros [] [];left;reflexivity. Qed.

(** * Decidable lists *)
Section dec_lists.
  Context {A:Set}{decA:decidable_set A}.

  (** When [A] is decidable, [list A] also is. *)
  Global Instance list_dec : decidable_set (list A).
  Proof.
    intros l;induction l;intros [|b m];try (left;reflexivity)||(right;discriminate).
    destruct (IHl m) as [->|h].
    - case_eq (a =?= b).
      + intros -> _ ;left;reflexivity.
      + intros n _;right;intro h;inversion h;tauto.
    - right;intro E;inversion E;tauto.
  Qed.
  
  (** We can also decide memebership. *)

  Fixpoint inb (a: A) l :=
    match l with [] => false | b::l => if a =?= b then true else inb a l end.

  Lemma inb_In a l : In a l <-> inb a l = true.
  Proof.
    induction l;simpl.
    - split;[tauto|discriminate].
    - case_eq (a =?= a0);intuition.
  Qed.

End dec_lists.

(** * Comparing lists up-to commutativity and idempotency *)

Section eq_list.
  Context {A:Set}.

  (** In this section we consider two lists equivalent if their membership *)
  (** predicates coincide. *)
  
  Definition eq_list : relation (list A) :=
    fun l m => forall a, In a l <-> In a m.

  (** This is indeed an equivalence relation. *)
  
  Global Instance eq_list_equiv : Equivalence eq_list.
  Proof. split;intro;intros;firstorder. Qed.

  (** The concatenation operation preserves this relation. *)
  
  Global Instance app_proper_eq_list : Proper (eq_list ==> eq_list ==> eq_list) (@app A).
  Proof.
    intros l1 l2 hl m1 m2 hm a.
    repeat rewrite in_app_iff.
    rewrite (hl a),(hm a);tauto.
  Qed.

  (** It is a commutative and idempotent operator with respect to this relation. *)
  
  Lemma app_comm l1 l2 : eq_list (l1++l2) (l2++l1).
  Proof. intro a;repeat rewrite in_app_iff;tauto. Qed.

  Lemma app_idem l : eq_list (l++l) l.
  Proof. intro a;repeat rewrite in_app_iff;tauto. Qed.

  (** If the base set is decidable, then the equivalence is decidable. *)
  
  Context {decA : decidable_set A}.
  
  Lemma dec_eq_list l m : {eq_list l m} + { ~ eq_list l m}.
  Proof.
    revert l;induction m as [|b m];intros l.
    - destruct l as [|a l].
      + left;intro a;simpl;tauto.
      + right;intros f.
        pose proof (f a) as h;simpl in h.
        apply h;now left.
    - case_eq (inb b m);intro h.
      + case_eq (inb b l);intro h'.
        * case_eq (IHm l);intros ih _.
          -- left;apply inb_In in h.
             intros a;simpl.
             rewrite (ih a).
             case_eq (b =?= a);simpl.
             ++ intros -> _;split;auto.
             ++ intros f _;split;auto.
                intros [<-|hyp];auto.
          -- right;apply inb_In in h,h'.
             intro f.
             apply ih;intro a.
             destruct (b =?= a).
             ++ subst;tauto.
             ++ pose proof (f a) as hyp;simpl in hyp.
                tauto.
        * right;rewrite <- Bool.not_true_iff_false in h';rewrite <- inb_In in h,h'.
          intros f;apply h',f;now left.
      + case_eq (inb b l);intro h'.
        * case_eq (IHm (filter (fun x => if x =?= b then false else true) l));intros ih _.
          -- left;rewrite <- Bool.not_true_iff_false in h;rewrite <- inb_In in h,h'.
             intros a;simpl.
             rewrite <- (ih a).
             rewrite filter_In.
             case_eq (a =?= b);simpl;intuition.
             ++ subst;auto.
             ++ subst;exfalso;auto.
          -- right;rewrite <- Bool.not_true_iff_false in h;rewrite <- inb_In in h,h'.
             intros hyp.
             apply ih;clear ih.
             intro a;rewrite filter_In.
             rewrite (hyp a);simpl.
             destruct (a =?= b);intuition try discriminate.
             ++ subst;tauto.
             ++ subst;tauto.
        * right;rewrite <- Bool.not_true_iff_false in h,h';rewrite <- inb_In in h,h'.
          intros hyp;simpl.
          pose proof (hyp b) as f;simpl in f;tauto.
  Qed.
  
End eq_list.

(** * Comparing lists up-to commutativity *)

Section eq_list_comm.
  (** Requires the base type to be decidable. *)

  Context {A:Set}{decA:decidable_set A}.

  (** ** Main definitions and results. *)
  
  (** Two lists are deemed equivalent if for any base element, *)
  (** they have the same number of occurences. *)

  Definition eq_list_comm (l m : list A) :=
    forall a, count_occ eq_dec l a = count_occ eq_dec m a.

  (** This constitutes an equivalence relation. *)

  Global Instance equivalence_eq_list_comm : Equivalence eq_list_comm.
  Proof.
    split.
    - intros l a;reflexivity.
    - intros l m h a;rewrite (h a);reflexivity.
    - intros l m n h1 h2 a;rewrite (h1 a),(h2 a);reflexivity.
  Qed.

  (** Concatenation is a morphism with respect to this relation : *)
  (** that is concatenating equivalent lists yields equivalent lists. *)

  Global Instance app_proper :
    Proper (eq_list_comm ==> eq_list_comm ==> eq_list_comm) (@app A).
  Proof. intros l l' hl m m' hm a;repeat rewrite count_occ_app;rewrite hl,hm;reflexivity. Qed.

  (** Appending an element in front of equivalent lists also yields equivalent lists. *)

  Global Instance cons_proper :
    Proper (eq ==> eq_list_comm ==> eq_list_comm) (@cons A).
  Proof. intros b c -> m m' hm a;repeat rewrite count_occ_app;simpl;rewrite hm;reflexivity. Qed.

  (** As expected, concatenation is commutative up-to this relation. *)

  Lemma eq_list_comm_app_comm l m : eq_list_comm (l++m) (m++l).
  Proof. intro a;repeat rewrite count_occ_app;apply PeanoNat.Nat.add_comm. Qed.

  (** For singleton lists, [eq_list_comm] is equality. *)

  Lemma eq_list_comm_sngl m a : eq_list_comm [a] m -> m = [a]. 
  Proof.
    intro E;destruct m as [|b [|c]];[exfalso| |exfalso];pose proof (E a) as f;simpl in f;
      rewrite eq_dec_eq in f.
    + discriminate.
    + case_eq (b =?= a).
      * intros -> _ ;reflexivity. 
      * intros n h;rewrite h in f;discriminate.
    + case_eq (b =?= a).
      * intros -> _;rewrite eq_dec_eq in f.
        case_eq (c =?= a).
        -- intros -> _;rewrite eq_dec_eq in f.
           discriminate.
        -- intros n _.
           pose proof (E c) as f';simpl in f'.
           repeat rewrite eq_dec_neq in f' by (intros ->;apply n;reflexivity).
           rewrite eq_dec_eq in f';discriminate.
      * intros n _;clear f;pose proof (E b) as f.
        simpl in f.
        repeat rewrite eq_dec_neq in f by (intros ->;apply n;reflexivity).
        rewrite eq_dec_eq in f;discriminate.
  Qed.

  (** The same holds for the empty list. *)

  Lemma eq_list_comm_nil m : eq_list_comm [] m -> m = [].
  Proof.
    intro E; destruct m as [|a];[reflexivity|].
    exfalso;pose proof (E a) as f;simpl in f;rewrite eq_dec_eq in f.
    discriminate.
  Qed.

  (** The following decomposition lemma will prove very handy : if a list is equivalent *)
  (** to a list [a::l], then a sub list equivalent to [l] can be extracted from it. *)

  Lemma eq_list_comm_cons a l m :
    eq_list_comm (a::l) m ->
    exists m1 m2, m = m1 ++ a::m2 /\ eq_list_comm l (m1++m2).
  Proof.
    intros h;cut (In a m).
    - intro h'.
      apply in_split in h' as (m1&m2&->).
      exists m1,m2;split;[reflexivity|].
      intro b;pose proof (h b) as e;revert e.
      simpl;repeat rewrite count_occ_app;simpl.
      case_eq (a =?= b);intros h' _;lia.
    - rewrite (count_occ_In eq_dec).
      rewrite <- h;simpl.
      rewrite eq_dec_eq;lia.
  Qed.

  (** [forallb f] and [length] are impervious to/compatible with equivalence. *)

  Global Instance eq_list_comm_forallb f : Proper (eq_list_comm ==> eq) (forallb f).
  Proof.
    intros l;induction l;simpl;intros m hm.
    - apply eq_list_comm_nil in hm as ->;reflexivity.
    - apply eq_list_comm_cons in hm as (m1&m2&->&hm).
      rewrite (IHl _ hm).
      repeat rewrite forallb_app;simpl.
      repeat rewrite Bool.andb_assoc.
      rewrite (Bool.andb_comm (f a)).
      reflexivity.
  Qed.

  Global Instance eq_list_comm_length : Proper (eq_list_comm ==> eq) (@length A).
  Proof.
    intros l;induction l;simpl;intros m hm.
    - apply eq_list_comm_nil in hm as ->;reflexivity.
    - apply eq_list_comm_cons in hm as (m1&m2&->&hm).
      rewrite (IHl _ hm).
      repeat rewrite length_app;simpl;lia.
  Qed.
  
  (** ** Deciding equivalence *)

  (** We now set out to design a decision procedure for equivalence up-to commutativity. *)

  (** First, we define the following procedure to simultaneously check membership and, *)
  (** if possible, remove the first occurence of an element. *) 

  Fixpoint rm_first a l :=
    match l with
    | [] => None
    | b::l => if (a =?= b)
              then Some l
              else match rm_first a l with
                   | None => None
                   | Some m => Some (b::m)
                   end
    end.

  (** When an element is absent from the list, [rm_first] returns [None]. *)
  Lemma rm_first_None a l : ~ In a l -> rm_first a l = None.
  Proof.
    induction l;simpl.
    - tauto.
    - intros h;case_eq (a =?= a0).
      + intros <-;exfalso;apply h;now left.
      + intros;rewrite IHl;auto.
  Qed.

  (** Otherwise, it returns the list with the first occurence of the element removed. *)

  Lemma rm_first_Some a l :
    In a l ->
    exists l1 l2, l = l1 ++ a::l2 /\ ~ In a l1 /\ rm_first a l = Some (l1++l2).
  Proof.
    induction l;simpl.
    - tauto.
    - intros h;case_eq (a =?= a0).
      + intros <- _;exists [],l;split;auto.
      + intros;destruct IHl as (l1 & l2 & -> & h1 & h2);auto.
        * destruct h as [<-|h];[exfalso;apply n;reflexivity|apply h].
        * exists (a0::l1),l2;repeat split;auto.
          -- intros [<-|h'];auto.
          -- rewrite h2;reflexivity.
  Qed.

  (** We can now define the procedure to check whether two lists are equivalent. *)

  Fixpoint test_eq_comm l m :=
    match l with
    | [] =>
        match m with
        | [] => true
        | _ => false
        end
    | a::l =>
        match rm_first a m with
        | None => false
        | Some m' => test_eq_comm l m'
        end
    end.

  (** This procedure is correct. *)

  Lemma test_eq_comm_spec l m : test_eq_comm l m = true <-> eq_list_comm l m.
  Proof.
    revert m;induction l;intro m.
    - destruct m;split;auto.
      + reflexivity.
      + discriminate.
      + intro h;apply eq_list_comm_nil in h;discriminate.
    - simpl.
      case_eq (inb a m);[|rewrite <- Bool.not_true_iff_false];rewrite <- inb_In;intro h.
      + apply rm_first_Some in h as (l1&l2&->&h1&->).
        rewrite IHl.
        split.
        * intro E.
          rewrite E.
          rewrite (eq_list_comm_app_comm l1 (a::l2)),eq_list_comm_app_comm.
          reflexivity.
        * intros E x;pose proof (E x) as h;revert h.
          simpl;repeat rewrite count_occ_app;simpl.
          destruct (a =?= x);lia.
      + pose proof h as h';apply rm_first_None in h' as ->.
        split;[discriminate|].
        intro h'.
        exfalso;apply h.
        apply (count_occ_In eq_dec).
        rewrite <- h';simpl.
        rewrite eq_dec_eq;lia.
  Qed.

  (** Thus equivalence of lists is decidable. *)
  
  Lemma dec_eq_list_comm l m : {eq_list_comm l m} + {~ eq_list_comm l m}.
  Proof.
    case_eq (test_eq_comm l m);intro E;[left|right];rewrite <- test_eq_comm_spec;rewrite E;
      [reflexivity|discriminate].
  Qed.
End eq_list_comm.

(** * Lifting relations to lists *)

Section list_lift.

  (** We define two ways of extending a relation [r: A -> B -> Prop] *)
  (** to a relation [list A -> list B -> Prop]. *)

  (** The fist way is the straightforward element-wise lifting: *)
  (** two lists [l,m] of the same lenght are related if for every index, *)
  (** [l_i] and [m_i] are related. *) 

  Fixpoint list_lift {A B} (r : A -> B -> Prop) l m : Prop :=
    match l,m with
    | [],[] => True
    | a::l,b::m => r a b /\ list_lift r l m
    | _,_ => False
    end.

  (** The second way allows the two lists to be related similarly as before, but adds the *)
  (** possibility to re-shuffle the elements. In other words, it ``closes'' the relation by *)
  (** list commutativity. Note that this require the type [B] to be a decidable set, in *)
  (** order to use our previously defined notion of equivalence of lists up-to commutativity. *)
  
  Definition multiset_lift {A B : Set} {decB : decidable_set B} :
    (A -> B -> Prop) -> list A -> list B -> Prop :=
    fun r l m => exists l', list_lift r l l' /\ eq_list_comm l' m.

  (** ** Properties of the plain lifting *)

  (** Lifting an equivalence relation yields another equivalence relation. *)
  
  Global Instance list_lift_eq {A} {r : relation A} {e : Equivalence r} :
    Equivalence (list_lift r).
  Proof.
    split.
    - intro l;induction l;simpl.
      + tauto.
      + split;[reflexivity|assumption].
    - intros l;induction l;intros [|b m];simpl;try tauto.
      intros (h1&h2);split;[symmetry|apply IHl];assumption.
    - intros l;induction l;intros [|b m] [|c n];simpl;try tauto.
      intros (h1&h2) (h3&h4);split;[etransitivity;eassumption|].
      apply (IHl m);assumption. 
  Qed.

  (** The following lemmas lift some properties of relations to properties *)
  (** of their lifted versions. *)

  Global Instance list_lift_proper {A B} (r : relation A) (s : relation B) (R : A -> B -> Prop) :
    Proper (r ==> s ==> iff) R -> Proper (list_lift r ==> list_lift s ==> iff) (list_lift R).
  Proof.
    intros h l1 l2 El m1 m2 Em.
    revert l2 m1 m2 El Em.
    induction l1;intros [] [] [];simpl;try tauto.
    intros (h1&h2) (h3&h4).
    rewrite IHl1 by eassumption.
    rewrite (h _ _ h1 _ _ h3).
    reflexivity.
  Qed.
  
  Global Instance list_lift_map_proper {A B} (r : relation A) (s : relation B) (f : A -> B ) :
    Proper (r ==> s) f -> Proper (list_lift r ==> list_lift s) (map f).
  Proof.
    intros h l1 l2 El.
    revert l2 El.
    induction l1;intros [];simpl;try tauto.
    intros (h1&h2).
    split;[apply h,h1|apply IHl1,h2].
  Qed.

  
  (** If a list is lift-related to a concatenation, it can be decomposed into a *)
  (** concatenation such that the components are lift-related to each other. *)
  
  Lemma list_lift_app {A B} (r : A -> B -> Prop) l l1 l2 :
    list_lift r l (l1++l2) ->
    exists m1 m2, l = m1++m2 /\ list_lift r m1 l1 /\ list_lift r m2 l2.
  Proof.
    revert l l2;induction l1 as [|a l1];simpl;intros l l2 h.
    - exists [],l;simpl;repeat split;auto.
    - destruct l as [|b l];[simpl in *;tauto|].
      destruct h as (h1&h2).
      apply IHl1 in h2 as (m1&m2&->&h2&h3).
      exists (b::m1),m2;simpl;repeat split;auto.
  Qed.
  
  Lemma list_lift_app_l {A B} (r : A -> B -> Prop) l l1 l2 :
    list_lift r (l1++l2) l ->
    exists m1 m2, l = m1++m2 /\ list_lift r l1 m1 /\ list_lift r l2 m2.
  Proof.
    revert l l2;induction l1 as [|a l1];simpl;intros l l2 h.
    - exists [],l;simpl;repeat split;auto.
    - destruct l as [|b l];[simpl in *;tauto|].
      destruct h as (h1&h2).
      apply IHl1 in h2 as (m1&m2&->&h2&h3).
      exists (b::m1),m2;simpl;repeat split;auto.
  Qed.

  (** Conversely, concatenating related lists yields related lists. *)
  
  Lemma app_list_lift {A B} (r : A -> B -> Prop) l1 l2 m1 m2 :
    list_lift r l1 m1 -> list_lift r l2 m2 -> list_lift r (l1++l2) (m1++m2).
  Proof.
    revert l2 m1 m2;induction l1;intros l2 [|b m] m2;simpl;try tauto.
    intros (h1 & h2) h.
    split;[assumption|].
    apply IHl1;assumption.
  Qed.

  Global Instance app_proper_list_lift {A} r :
    Proper (list_lift r ==> list_lift r ==> list_lift r) (@app A).
  Proof. intros l1 l2 h1 m1 m2 h2;apply app_list_lift;assumption. Qed.

  (** For a relation [r], appending [r]-related elements to lift-related lists *)
  (** yields lift-related lists. *)
  
  Global Instance cons_proper_list_lift {A} r :
    Proper (r ==> list_lift r ==> list_lift r) (@cons A).
  Proof. intros a b h1 l m h2;split;assumption. Qed.

  (** If two lists are lift-related, they have the same length. *)
    
  Lemma list_lift_length {X Y} (r : X -> Y -> Prop) l m :
    list_lift r l m -> length l = length m.
  Proof.
    revert m;induction l;intros [];simpl;try tauto.
    intros (h1&h2);apply IHl in h2 as ->;reflexivity.
  Qed.

  (** If a relation can be written as a composite of two relations, that the *)
  (** same decomposition can be done on the lifted relation. *)

  Lemma list_lift_composition {A B C}
    (r : A -> C -> Prop)
    (s : A -> B -> Prop)
    (t : B -> C -> Prop) :
    (forall a c, r a c -> exists b, s a b /\ t b c) ->
      forall l m, list_lift r l m -> exists k, list_lift s l k /\ list_lift t k m.
  Proof.
    intros hyp l;induction l;intros [|c m];simpl;try tauto.
    - exists [];repeat split;auto.
    - intros (h1&h3).
      apply hyp in h1 as (b&h1&h2).
      apply IHl in h3 as (k&h3&h4).
      exists (b::k);repeat split;auto.
  Qed.

  Lemma list_lift_composition_inv {A B C}
    (r : A -> C -> Prop)
    (s : A -> B -> Prop)
    (t : B -> C -> Prop) :
    (forall a c b, s a b -> t b c -> r a c) ->
      forall l m k, list_lift s l k -> list_lift t k m -> list_lift r l m.
  Proof.
    intros hyp l;induction l;intros [|c m] [|b k];simpl;try tauto.
    intros (h1&h3) (h2&h4).
    split;[apply (hyp a c b)|apply (IHl m k)];auto.
  Qed.
  
  (** ** Properties of the multiset lifting *)

  (** We pose a decidable set [A] for the remainder of the section. *)

  Context {A : Set}{decA:decidable_set A}.

  (** Lifting a symmetric relation yields a symmetric lifted relation. *)

  Lemma multiset_lift_sym {r : relation A} {s : Equivalence r} :
    Symmetric (multiset_lift r).
  Proof.
    intros l;induction l;intros m (k&h1&h2);simpl.
    + destruct k as [|b k];simpl in h1;[|tauto].
      apply eq_list_comm_nil in h2 as -> ;exists [];split;reflexivity.
    + destruct k as [|b k];simpl in h1;[tauto|destruct h1 as (ha&hl)].
      apply eq_list_comm_cons in h2 as (m1&m2&->&h2).
      assert (h1:multiset_lift r (m1++m2) l) by (apply IHl;exists k;split;assumption).
      destruct h1 as (k' & hk1 & hk2).
      symmetry in hk1;apply list_lift_app in hk1 as (k1&k2&->&h3&h4).
      exists (k1++a::k2);split.
      * rewrite ha,h3,h4.
        reflexivity.
      * rewrite <- hk2.
        rewrite eq_list_comm_app_comm;simpl.
        rewrite eq_list_comm_app_comm;simpl.
        reflexivity.
  Qed.

  (** Lifting an equivalence relation yields an equivalence relation. *)

  Global Instance multiset_lift_eq {r : relation A} {e : Equivalence r} :
    Equivalence (multiset_lift r).
  Proof.
    split.
    - intro l;exists l;split;reflexivity.
    - apply multiset_lift_sym.
    - intros l1 l2 l3 (k1&h11&h12) (k2&h21&h22).
      assert (multiset_lift r k1 k2) as (l&h1&h2)
        by now (apply multiset_lift_sym;exists l2;split;symmetry).
      exists l;split.
      + transitivity k1;assumption.
      + transitivity k2;assumption.
  Qed.

  (** Concatenating related lists yields related lists. *)
  
  Lemma app_multiset_lift {X : Set} (r : X -> A -> Prop) l1 l2 m1 m2 :
    multiset_lift r l1 m1 -> multiset_lift r l2 m2 ->
    multiset_lift r (l1++l2) (m1++m2).
  Proof.
    intros (k1& h1 & h2) (k2&h3&h4).
    exists (k1++k2);split.
    - apply app_list_lift;assumption.
    - apply app_proper;assumption.
  Qed.

  Global Instance app_proper_multiset_lift r :
    Proper (multiset_lift r ==> multiset_lift r ==> multiset_lift r) (@app A).
  Proof.
    intros l1 l2 (k1& h1 & h2) m1 m2 (k2&h3&h4).
    exists (k1++k2);split.
    - apply app_proper_list_lift;assumption.
    - apply app_proper;assumption.
  Qed.

  (** For a relation [r], appending [r]-related elements to lift-related lists *)
  (** yields lift-related lists. *)
  
  Global Instance cons_proper_multiset_lift r :
    Proper (r ==> multiset_lift r ==> multiset_lift r) (@cons A).
  Proof.
    intros a b h1 l m (k&h2&h3).
    exists (b::k);split;auto.
    - apply cons_proper_list_lift;assumption.
    - clear a h1 l h2 r;intros a;simpl.
      rewrite (h3 a);reflexivity.
  Qed.

  (** Applying the same function to the elements of equivalent lists yields equivalent lists. *)

  Global Instance eq_list_comm_map {X Y}
    {decX : decidable_set X} {decY : decidable_set Y} (f : X -> Y) :
    Proper (eq_list_comm ==> eq_list_comm) (map f).
  Proof.
    intros l;induction l;simpl;intros m hm.
    - apply eq_list_comm_nil in hm as ->;reflexivity.
    - apply eq_list_comm_cons in hm as (m1&m2&->&hm).
      rewrite (IHl _ hm).
      repeat rewrite map_app.
      rewrite (eq_list_comm_app_comm  _ (map f(_::_))).
      rewrite (eq_list_comm_app_comm  (map f m1)).
      reflexivity.
  Qed.

  (** It will sometimes be useful to decompose the lifted relation as follows. *)

  Lemma multiset_lift_inv {X Y} {decX : decidable_set X} {decY : decidable_set Y}
    (r : X -> Y -> Prop):
    forall l m, multiset_lift r l m <-> exists k, eq_list_comm l k /\ list_lift r k m.
  Proof.
    induction l;intros m;split.
    - intros (k&h1&h2).
      destruct k;[|exfalso;apply h1].
      apply eq_list_comm_nil in h2 as ->.
      exists [];split;[reflexivity|tauto].
    - intros (k&h1&h2).
      apply eq_list_comm_nil in h1 as ->.
      exists m;split;[assumption|reflexivity].
    - intros (k&h1&h2).
      destruct k as [|b k];[exfalso;apply h1|].
      destruct h1 as (h1&h3).
      apply eq_list_comm_cons in h2 as (m1&m2&->&h2).
      cut (multiset_lift r l (m1++m2));[|exists k;split;auto].
      intros ih;apply IHl in ih as (k'&hk1&hk2).
      apply list_lift_app in hk2 as (k1&k2&->&hk2&hk3).
      exists (k1++a::k2);split.
      + rewrite hk1.
        intro x;repeat (rewrite count_occ_app;simpl).
        destruct (a =?= x);lia.
      + apply app_list_lift;try split;auto.
    - intros (k&hk1&hk2).
      apply eq_list_comm_cons in hk1 as (m1&m2&->&h2).
      apply list_lift_app_l in hk2 as (k1&k2&->&hk2&hk3).
      destruct k2 as [|b k2];[exfalso;apply hk3|].
      destruct hk3 as (hab&hk3).
      assert (multiset_lift r l (k1++k2)) as (k&ih1&ih2)
          by (apply IHl;exists (m1++m2);split;[|apply app_list_lift];auto).
      exists (b::k);repeat split;auto.
      rewrite ih2.
      rewrite eq_list_comm_app_comm.
      rewrite (eq_list_comm_app_comm k1).
      reflexivity.
  Qed.

End list_lift.
