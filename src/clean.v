Require Import prelim gnl theories.

Section clean.
  Context {X O : Set} {decX: decidable_set X} {decO: decidable_set O}.

  Fixpoint is_deep_clean (e : GExp X O) : bool :=
    match e with
    | ø => false
    | var _ => true
    | e + f | e ×{_} f => (is_deep_clean e && is_deep_clean f)%bool
    | e ^{_} => is_deep_clean e
    end.

  Definition is_clean e :=
    match e with
    | ø => true
    | e => is_deep_clean e
    end.

  Fixpoint clean_exp (e : GExp X O) : option (GExp X O) :=
    match e with
    | ø => None
    | var a => Some (var a)
    | e + f =>
        match (clean_exp e),(clean_exp f) with
        | None,None => None
        | Some g,None | None,Some g => Some g
        | Some g1,Some g2 => Some (g1+g2)
        end
    | e ×{o} f => 
        match (clean_exp e),(clean_exp f) with
        | None,None | Some _,None | None,Some _ => None
        | Some g1,Some g2 => Some (g1 ×{o} g2)
        end
    |e ^{o} =>
       match (clean_exp e) with
       | None => None
       | Some g => Some (g^{o})
       end
    end.

  Definition Clean e :=
    match (clean_exp e) with
    | None => ø
    | Some e => e
    end.

  Lemma Clean_is_eq e : Ø |- Clean e == e.
  Proof.
    unfold Clean;induction e;simpl;(try now split;auto with proofs).
    - destruct (clean_exp e1),(clean_exp e2);rewrite <- IHe1,<- IHe2;split;auto with proofs.
    - destruct (clean_exp e1),(clean_exp e2);rewrite <- IHe1,<- IHe2;split;auto with proofs.
    - destruct (clean_exp e);rewrite <- IHe;split;auto with proofs.
  Qed.

  Lemma Clean_is_clean e : is_clean (Clean e) = true.
  Proof.
    unfold Clean;case_eq (clean_exp e);[|reflexivity].
    intros g E;cut (is_deep_clean g = true);[destruct g;tauto|].
    revert g E;induction e;simpl;try discriminate.
    - intros;inversion E;subst;reflexivity.
    - destruct (clean_exp e1),(clean_exp e2);intros;inversion E;subst;clear E;auto.
      simpl;rewrite IHe1,IHe2 by reflexivity; reflexivity.
    - destruct (clean_exp e1),(clean_exp e2);intros;inversion E;subst;clear E;auto.
      simpl;rewrite IHe1,IHe2 by reflexivity; reflexivity.
    - destruct (clean_exp e);intros;inversion E;subst;clear E;auto.
      simpl;rewrite IHe by reflexivity; reflexivity.
  Qed.
  

End clean.
