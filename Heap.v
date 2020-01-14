
Require Import FunctionalExtensionality.
Require Import PeanoNat.



Section Heap.
  (* Entries in the heap can be of arbitrary type 'S': *)
  Inductive hentry := he : forall {S : Set}, S -> hentry.

  (* We model heaps as partial maps: *)
  Definition heap := nat -> option hentry.

  Definition htype : heap -> (nat -> option Set) :=
    fun h p => match h p with
                 | Some (@he T _) => Some T
                 | None => None
               end.

  Definition empty : heap := fun _ => None.

  Definition single {S : Set} (p : nat) (v : S) :=
    fun q => if (q =? p) then Some (he v) else None.

  Definition disjoint (h1 h2 : heap) : Prop :=
    (forall n, (exists x, h1 n = Some x) -> h2 n = None) /\
    (forall n, (exists x, h2 n = Some x) -> h1 n = None).

  Definition union (h1 h2 : heap) : heap :=
    fun p => match (h1 p) with None => h2 p | _ => h1 p end.

  Definition hext {S : Set} (h : heap) (p : nat) (v : S) : heap :=
    fun q => if (q =? p) then Some (he v) else h q.
End Heap.


Notation "(| h | p -> v |)" := (hext _ h p v)
                               (left associativity, at level 30)
                               : heap_scope.


(* We prove a few simple lemmata to convince ourselves
   that the definitions of our heap operations make sense: *)
Section heap_lemmata.
  Lemma disj_comm' : forall (h1 h2 : heap),
    disjoint h1 h2 -> disjoint h2 h1.
  Proof with auto.
    unfold disjoint; intuition.
  Qed.

  Lemma disj_comm : forall (h1 h2 : heap),
    disjoint h1 h2 <-> disjoint h2 h1.
  Proof with auto.
    intuition; apply disj_comm'...
  Qed.

  Lemma disj_empty_neutral_left : forall (h : heap), disjoint empty h.
  Proof with auto.
    intro h; unfold disjoint, empty; intuition.
    destruct H. inversion H.
  Qed.

  Lemma disj_empty_neutral_right : forall (h : heap), disjoint h empty.
  Proof with auto.
    intro h; unfold disjoint, empty; intuition.
    destruct H. inversion H.
  Qed.

  (* Because of our choice to represent heaps as partial maps, equality
     between heaps is not decidable. Moreover, for proving heaps equal,
     we have to rely on functional extensionality in the following:     *)

  Lemma union_empty_neutral_left : forall (h : heap), union empty h = h.
  Proof with auto.
    intuition; apply functional_extensionality.
  Qed.

  Lemma union_empty_neutral_right : forall (h : heap), union h empty = h.
  Proof with auto.
    intuition; apply functional_extensionality. intro n.
    unfold union. unfold empty. destruct (h n)...
  Qed.

  Lemma union_assoc_1 : forall (h1 h2 h3 : heap),
    disjoint h1 h2 -> disjoint (union h1 h2) h3 ->
      union (union h1 h2) h3 = union h1 (union h2 h3).
  Proof with auto.
    intuition; apply functional_extensionality; intro n; unfold union.
    destruct (h1 n) eqn:?...
  Qed.

  Lemma union_assoc_2 : forall (h1 h2 h3 : heap),
    disjoint h2 h3 -> disjoint h1 (union h2 h3) ->
      union h1 (union h2 h3) = union (union h1 h2) h3.
  Proof with auto.
    intuition; apply functional_extensionality; intro n; unfold union.
    destruct (h1 n) eqn:?...
  Qed.

  Lemma union_comm : forall (h1 h2 : heap),
    disjoint h1 h2 -> union h1 h2 = union h2 h1.
  Proof with auto.
    intuition; apply functional_extensionality; intro n; unfold union.
    destruct (h1 n) eqn:?, (h2 n) eqn:?...
    destruct H.
    assert(exists x, h1 n = Some x) by (exists h; auto).
    apply H in H1; rewrite H1 in Heqo0; inversion Heqo0...
  Qed.

  Lemma disj_union_disj_1 : forall (h1 h2 h3 : heap),
    disjoint h1 h2 -> disjoint (union h1 h2) h3 -> disjoint h1 h3.
  Proof with auto.
    intros h1 h2 h3 H H'. unfold disjoint. split; intros n [x Hex].
    + assert(exists x, union h1 h2 n = Some x)
        by (exists x; unfold union; rewrite Hex; auto).
      apply H' in H0...
    + destruct (union h1 h2 n) eqn:?.
      - assert(exists x, union h1 h2 n = Some x) by (exists h; auto).
        apply H' in H0; rewrite Hex in H0; inversion H0.
      - destruct (h1 n) eqn:?...
        * unfold union in Heqo; rewrite Heqo0 in Heqo; inversion Heqo.
  Qed.

  Lemma disj_union_disj_2 : forall (h1 h2 h3 : heap),
    disjoint h1 h2 -> disjoint (union h1 h2) h3 -> disjoint h2 h3.
  Proof with auto.
    intros h1 h2 h3 H. rewrite union_comm...
    apply disj_union_disj_1; apply disj_comm...
  Qed.

  Lemma disj_union_disj_3 : forall (h1 h2 h3 : heap),
    disjoint h2 h3 -> disjoint h1 (union h2 h3) -> disjoint h1 h3.
  Proof with auto.
    intros h1 h2 h3 H H'.
    apply disj_comm in H'.
    rewrite disj_comm.
    apply disj_union_disj_2 with (h1:=h2)...
  Qed.

  Lemma disj_assoc_1 : forall (h1 h2 h3 : heap),
    disjoint h1 h2 -> disjoint (union h1 h2) h3 -> disjoint h1 (union h2 h3).
  Proof with auto.
    intuition; unfold disjoint; intuition.
    + assert(exists x, union h1 h2 n = Some x)
        by (destruct H1 as [x H']; exists x; unfold union; rewrite H'; auto).
      apply H in H1.
      apply H0 in H2.
      unfold union; rewrite H1; rewrite H2...
    + destruct (h1 n) eqn:?...
      assert(exists x, h1 n = Some x) by (exists h; auto).
      apply H in H2.
      unfold union in H1. rewrite H2 in H1.
      apply H0 in H1. unfold union in H1. rewrite Heqo in H1. inversion H1.
  Qed.

  Lemma disj_assoc_2 : forall (h1 h2 h3 : heap),
    disjoint h2 h3 -> disjoint h1 (union h2 h3) -> disjoint (union h1 h2) h3.
  Proof with auto.
    intuition; unfold disjoint; intuition.
    + destruct (h1 n) eqn:?...
      - assert(exists x, h1 n = Some x) by (exists h; auto).
        apply H0 in H2.
        unfold union in H2.
        destruct (h2 n) eqn:?...
        inversion H2.
      - destruct (h2 n) eqn:?...
        * assert(exists x, h2 n = Some x) by (exists h; auto).
          apply H in H2...
        * destruct H1 as [x H1].
          unfold union in H1. rewrite Heqo in H1. rewrite Heqo0 in H1.
          inversion H1.
    + assert(h2 n = None) by (apply H in H1; auto).
      destruct H1 as [x H1].
      assert(exists x, union h2 h3 n = Some x)
        by (exists x; unfold union; rewrite H2; rewrite H1; auto).
      apply H0 in H3.
      unfold union. rewrite H3...
  Qed.

  Lemma union_empty_empty : forall (h1 h2 : heap),
   union h1 h2 = empty -> (h1 = empty /\ h2 = empty).
  Proof with auto.
    intros h1 h2 H.
    split; apply functional_extensionality; intro p;
      assert(H1: union h1 h2 p = empty p) by (rewrite H; auto);
      unfold union in H1;
      destruct (h1 p).
    + inversion H1.
    + unfold empty...
    + inversion H1.
    + auto.
  Qed.

  Lemma single_not_empty : forall {S : Set} (p : nat) (a : S),
    (@single S p a) <> empty.
  Proof with auto.
    intuition.
    assert(H1: single p a p = empty p) by (rewrite H; auto).
    unfold single, empty in H1. rewrite Nat.eqb_refl in H1. inversion H1.
  Qed.
End heap_lemmata.



Section Assertions.
  (* Heap assertions: *)

  Definition hass := (heap -> Prop).

  Definition emp : hass := fun h => h = empty.

  Definition htrue : hass := fun _ => True.

  Definition hor (P Q : hass) : hass := fun h => P h \/ Q h.

  Definition singleton (p : nat) {S : Set} (v : S) : hass :=
    fun h => h = single p v.

  Definition pure (P : Prop) : hass := fun h => P /\ h = empty.

  Definition sep (P Q : hass) : hass := 
    fun h => exists h1 h2, disjoint h1 h2 /\ h = union h1 h2 /\ P h1 /\ Q h2.

  Definition ex {A} (P : A -> hass) : hass :=
    fun h => exists x, P x h.

  Definition wand (P Q : hass) : hass :=
    fun h => forall h', disjoint h h' -> P h' -> Q (union h h').

  Definition imply (P Q : hass) : Prop :=  forall h, P h -> Q h.
  Definition equiv (P Q : hass) : Prop :=  forall h, P h <-> Q h.
End Assertions.


Notation "<[ P ]>" := (pure P) : heap_scope.
Notation "P || Q" := (hor P Q )
                     (at level 50, left associativity) : heap_scope.
Notation "[[ p |-> v ]]" := (singleton p v) (at level 30) : heap_scope.
Notation "P * Q" := (sep P Q) (at level 40, left associativity) : heap_scope.
Notation "'exist' x .. y , P" := (ex (fun x => .. (ex (fun y => P)) ..))
                                 (at level 50, x binder, y binder)
                                 : heap_scope.
Notation "P ==> Q" := (imply P Q) (no associativity, at level 70)
                                  : heap_scope.
Notation "P === Q" := (equiv P Q) (no associativity, at level 70)
                                  : heap_scope.



(* We prove a few simple lemmata to convince ourselves that our
   heap assertions and some of their combinations make sense:   *)
Section assertions_lemmata.

  Open Scope heap_scope.

  Lemma sep_comm : forall (P Q : hass),
    P * Q === Q * P.
  Proof with auto.
    unfold equiv. intros P Q h.
    unfold sep; intuition;
      destruct H as [h1 [h2 [Hdis [Hun [HP HQ] ] ] ] ];
      exists h2, h1; intuition; auto;
      try (apply disj_comm; auto);
      try (rewrite Hun; apply union_comm)...
  Qed.

  Lemma hass_ex_falso : forall (P : hass), <[False]> ==> P.
  Proof.
    unfold imply. intros p h H.
    inversion H; contradiction.
  Qed.

  Lemma hass_ex_falso_framed_left : forall (P Q : hass), P * <[False]> ==> Q.
  Proof.
    unfold sep, imply. intuition.
    destruct H as [h1 [h2 [Hdisj [Hun [_ HFalse] ] ] ] ].
    destruct HFalse; contradiction.
  Qed.

  Lemma hass_ex_falso_framed_right : forall (P Q : hass), <[False]> * P ==> Q.
  Proof.
    unfold sep, imply. intuition.
    destruct H as [h1 [h2 [Hdisj [Hun [HFalse _] ] ] ] ].
    destruct HFalse; contradiction.
  Qed.

  Lemma hass_imply_taut : forall (P : hass), P ==> P.
  Proof with auto.
    unfold imply...
  Qed.

  Lemma hass_singleton_exclusive :
    forall {S1 S2 : Set} p (v : S1) (w : S2) (P : hass),
      [[p |-> v]] * [[p |-> w]] ==> P.
  Proof with auto.
    unfold imply. intuition.
    unfold sep in *.
    destruct H as [h1 [h2 [Hdis [Hun [Hpv Hpw] ] ] ] ].
    unfold singleton in *. subst.
    inversion Hdis.
    assert(exists x, single p v p = Some x).
      exists (he v); unfold single...
      rewrite Nat.eqb_refl...
    apply H in H1.
      unfold single in H1. rewrite Nat.eqb_refl in H1. inversion H1.
  Qed.

  Lemma hass_pure_contraction : forall (P : Prop),
    <[P]> * <[P]> ==> <[P]>.
  Proof with auto.
    unfold imply, sep. intuition.
    destruct H as [h1 [h2 [Hdis [Hun [HP1 HP2] ] ] ] ].
    destruct HP1; subst...
  Qed.

  Lemma hass_pure_conj_equiv_sep : forall (P Q : Prop),
    <[P /\ Q]> === <[P]> * <[Q]>.
  Proof with auto.
    unfold equiv, sep. intuition.
    + destruct H; subst.
      exists empty, empty; intuition; try (unfold pure; auto).
      apply disj_empty_neutral_left.
    + unfold pure; intuition;
        destruct H as [h1 [h2 [_ [Hun [HP HQ] ] ] ] ];
        destruct HP, HQ...
      subst; rewrite union_empty_neutral_left...
  Qed.

  Lemma hass_imply_trans : forall (P Q R : hass),
    P ==> Q -> Q ==> R -> P ==> R.
  Proof with auto.
    unfold imply; intuition.
  Qed.

  Lemma hass_imply_imply_equiv : forall (P Q : hass),
    (P ==> Q /\ Q ==> P) <-> P === Q.
  Proof with auto.
    unfold imply, equiv; intuition; apply H...
  Qed.

  Lemma hass_equiv_imply : forall (P Q : hass),
    (P === Q) -> P ==> Q.
  Proof with auto.
    unfold imply, equiv; intuition; apply H...
  Qed.

  Lemma hass_equiv_trans : forall (P Q R : hass),
    P === Q -> Q === R -> P === R.
  Proof with auto.
    unfold equiv; intuition.
    + apply H0; apply H...
    + apply H; apply H0...
  Qed.

  Lemma hass_equiv_symm : forall (P Q : hass),
    (P === Q) <-> (Q === P).
  Proof with auto.
    unfold equiv; intuition; apply H...
  Qed.

  Lemma hass_imply_framed_right : forall (P Q R : hass),
    P ==> Q -> P * R ==> Q * R.
  Proof with auto.
    unfold imply. intros P Q R H h Hsep.
    unfold sep in *.
    destruct Hsep as [h1 [h2 [Hdis [Hun [HP HR] ] ] ] ].
    apply H in HP.
    exists h1, h2...
  Qed.

  Lemma hass_equiv_framed_right : forall (P Q R : hass),
    P === Q -> P * R === Q * R.
  Proof with auto.
    unfold equiv, sep; intuition;
      destruct H0 as [h1 [h2 [Hdis [Hun [HP HR] ] ] ] ];
      exists h1, h2; intuition; apply H...
  Qed.

  Lemma hass_imply_framed_left : forall (P Q R : hass),
    P ==> Q -> R * P ==> R * Q.
  Proof with auto.
    unfold imply. intros P Q R H h Hsep.
    unfold sep in *.
    destruct Hsep as [h1 [h2 [Hdis [Hun [HR HP] ] ] ] ].
    apply H in HP.
    exists h1, h2...
  Qed.

  Lemma hass_equiv_framed_left : forall (P Q R : hass),
    P === Q -> R * P === R * Q.
  Proof with auto.
    unfold equiv, sep; intuition;
      destruct H0 as [h1 [h2 [Hdis [Hun [HR HP] ] ] ] ];
      exists h1, h2; intuition; apply H...
  Qed.

  Lemma sep_assoc_1 : forall (P Q R : hass),
    (P * Q) * R ==> P * (Q * R).
  Proof with auto.
    unfold imply. intros P Q R h. unfold sep; intuition.
    destruct H  as [h1 [h2 [Hdis  [Hun  [H' HR] ] ] ] ].
    destruct H' as [h3 [h4 [Hdis' [Hun' [HP HQ] ] ] ] ].
    exists h3, (union h4 h2); intuition; rewrite Hun' in Hdis.
    - apply disj_assoc_1...
    - rewrite Hun' in Hun; rewrite Hun.
      apply union_assoc_1...
    - exists h4, h2; intuition.
      eapply disj_union_disj_2. apply Hdis'. exact Hdis.
  Qed.

  Lemma sep_assoc_2 : forall (P Q R : hass),
    P * (Q * R) ==> (P * Q) * R.
  Proof with auto.
    unfold imply. intros P Q R h. unfold sep; intuition.
    destruct H  as [h1 [h2 [Hdis  [Hun  [HP H'] ] ] ] ].
    destruct H' as [h3 [h4 [Hdis' [Hun' [HQ HR] ] ] ] ].
    exists (union h1 h3), h4; intuition; rewrite Hun' in Hdis.
    - apply disj_assoc_2...
    - rewrite Hun' in Hun; rewrite Hun.
      apply union_assoc_2...
    - exists h1, h3; intuition.
      eapply disj_union_disj_3 with (h2:=h4).
      apply disj_comm...
      rewrite union_comm... apply disj_comm...
  Qed.

  Lemma sep_assoc : forall (P Q R : hass),
    (P * Q) * R === P * (Q * R).
  Proof with auto.
    intros P Q R. apply hass_imply_imply_equiv. intuition.
    apply sep_assoc_1. apply sep_assoc_2.
  Qed.

  Lemma sep_empty_neutral_left : forall (P : hass), emp*P === P.
  Proof with auto.
    unfold sep, emp, equiv. intuition.
    + destruct H as [h1 [h2 [_ [Hun [Hemp HP] ] ] ] ].
      subst. rewrite union_empty_neutral_left...
    + exists empty, h. intuition...
      apply disj_empty_neutral_left.
  Qed.

  Lemma sep_empty_neutral_right : forall (P : hass), P*emp === P.
  Proof with auto.
    unfold sep, emp, equiv. intuition.
    + destruct H as [h1 [h2 [_ [Hun [HP Hemp] ] ] ] ].
      subst. rewrite union_empty_neutral_right...
    + exists h, empty. intuition...
      apply disj_empty_neutral_right.
      rewrite union_empty_neutral_right...
  Qed.

  Lemma sep_pure_left : forall (P : hass) (Q : Prop),
    Q -> forall h, P h -> (sep <[Q]> P) h.
  Proof with auto.
    unfold sep. intuition.
    exists empty, h. firstorder.
    inversion H1.
  Qed.

  Lemma sep_pure_right : forall (P : hass) (Q : Prop),
    Q -> forall h, P h -> (sep P <[Q]>) h.
  Proof with auto.
    unfold sep. intuition.
    exists h, empty. firstorder.
    + inversion H1.
    + rewrite union_empty_neutral_right...
  Qed.

  Close Scope heap_scope.
End assertions_lemmata.


