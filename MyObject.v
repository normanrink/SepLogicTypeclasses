
Require Import SepLogicTC.Heap.
Require Import SepLogicTC.Triples.

Require Import List.
Require Import PeanoNat.

Import ListNotations.



Open Scope heap_scope.
Open Scope hoare_scope.


(* We say that data of type 'T' is an object if it comes with methods
     - 'new' for creating an object of type 'T' on the heap and
     - 'del' for deleting an object of type 'T' at a given address
        on the heap.
   Furthermore, the specifications of 'new' and 'del' require another
   method 'isa' that asserts that a heaplet contains an object of type
   'T'. The specifications of 'new' and 'del' themselves are given as
   Hoare triples, the proofs of which are labelled 'ht_new' and 'ht_del'
   respectively:                                                         *)

Class MyObject (T : Set) :=
{
  isa : T -> nat -> hass ;
  new : T -> cmd nat ;
  del : T -> nat -> cmd unit ;

  ht_new : forall t, {{emp}} (new t) {{r, isa t r}} ;
  ht_del : forall t p, {{isa t p}} (del t p) {{r, <[r = tt]>}}
}.


(* Straightforward assertion that a heap represents a list 'ls' containing
   objects of type 'T' that satisfies the typeclass 'MyObject'. We adopt
   the convention that a null pointer represents the empty list:           *)

Fixpoint isList {T : Set} `{MyObject T} (ls : list T) (p : nat) : hass :=
  match ls with
    | []     => <[p = 0]>
    | t::ls' => <[p <> 0]> * (exist tp q, [[p |-> (tp,q)]]
                                          * isa t tp * isList ls' q)
  end.


(* Programs 'newList' and 'delList' for constructing lists on the heap: *)

Definition newList {T : Set} `{MyObject T} : list T -> cmd nat :=
  fix f ls :=
  match ls with
    | [] => Return 0
    | t::ls' => q <- f ls';
                tp <- new t;
                p <- Alloc (tp,q);
                Return p
  end.

Definition delList {T : Set} `{MyObject T} : list T -> nat -> cmd unit :=
  fix f ls q :=
  match ls with
    | []    => Return tt
    | t::ls' => if q =? 0 then Return tt
                          else p <- Read (nat*nat)%type q;
                               let (tp,p') := p in del t tp;;
                                                   Free (nat*nat)%type q;;
                                                   f ls' p'
  end.


(* Proofs of specification for 'newList' and 'delList' repectively: *)

Lemma ht_newList {T : Set} `{MyObject T} : forall (ls : list T), 
  {{emp}} (newList ls) {{r, isList ls r}}.
Proof with auto.
  induction ls; simpl.
  + apply HtReturn.
  + eapply HtBind.
    - apply IHls.
    - intro s. eapply HtBind.
      -- eapply hoare_cancel_empty_left_pre. apply HtFrame. apply (ht_new a).
      -- intro t. simpl. eapply HtBind.
         * eapply hoare_cancel_empty_left_pre. apply HtFrame. apply HtAlloc.
         * intro p. simpl.
           eapply HtConsequence.
           ** eapply hoare_return.
           ** apply hass_imply_taut.
           ** intro r. simpl.
              unfold imply, ex, sep. intuition...
              destruct H0 as [h1 [h2 [Hdis [Hun [H0 Hpure] ] ] ] ].
              destruct Hpure; subst. clear Hdis.
                rewrite union_empty_neutral_right.
              destruct H0 as [h2 [h3 [Hdis [Hun [H0 H1] ] ] ] ].
              destruct H0 as [h4 [h5 [Hdis' [Hun' [Hpure Hsing] ] ] ] ].
              destruct Hpure; subst. clear Hdis'.
                rewrite union_empty_neutral_left in *.
              destruct H1 as [h6 [h7 [Hdis' [Hun' [Hisa Hlist] ] ] ] ].
              exists empty, (union h5 h3). intuition.
              *** apply disj_empty_neutral_left.
              *** unfold pure...
              *** exists t, s, (union h5 h6), h7. intuition.
                  **** apply disj_assoc_2...
                       rewrite <- Hun'...
                  **** rewrite Hun'. apply union_assoc_2...
                       rewrite <- Hun'...
                  **** exists h5, h6. intuition.
                       apply disj_union_disj_3 with (h2 := h7).
                       ***** apply disj_comm...
                       ***** rewrite union_comm in Hun'...
                             rewrite <- Hun'...
Qed.

Lemma ht_delList {T : Set} `{MyObject T} : forall (ls : list T) (p : nat),
  {{isList ls p}} (delList ls p) {{r, <[r = tt]>}}.
Proof with auto.
  induction ls; intro p.
  + simpl. eapply HtConsequence.
    ++ apply HtReturn.
    ++ unfold imply. intuition.
       repeat destruct H0.
       subst. unfold emp...
    ++ unfold imply...
  + simpl. destruct (Nat.eqb_spec p 0).
    ++ eapply HtConsequence.
       * apply HtReturn.
       * unfold imply, emp. intuition...
         repeat destruct H0.
         destruct H1; repeat destruct H3...
       * simpl. intro r. apply hass_imply_taut.
    ++ eapply HtBind.
       * apply hoare_frame_left. 
         eapply HtConsequence with (P := exist v, [[p |-> v]]
                                                  * isa a (fst v)
                                                  * isList ls (snd v)).
         ** eapply HtConsequence.
            - apply HtRead with (P := fun v => isa a (fst v)
                                               * isList ls (snd v)).
            - unfold imply, ex, sep. intuition...
              destruct H0 as [x [h1 [h2 [Hdis [Hun [H' Hlist] ] ] ] ] ].
              destruct H' as [h3 [h4 [Hdis' [Hun' [Hsing Hisa] ] ] ] ].
              exists x, h3, (union h4 h2). intuition.
              -- apply disj_assoc_1...
                 rewrite <- Hun'...
              -- rewrite Hun' in Hun.
                 rewrite Hun.
                 apply union_assoc_1...
                 rewrite <- Hun'...
              -- exists h4, h2. intuition.
                 apply disj_union_disj_2 with (h1 := h3)...
                 rewrite Hun' in Hdis...
            - intro r. simpl. apply hass_imply_taut.
         ** unfold imply, ex, sep. intuition...
            destruct H0 as [tp [p' [h1 [h2 [Hdis [Hun [H' Hlist] ] ] ] ] ] ].
            destruct H' as [h3 [h4 [Hdis' [Hun' [Hsing Hisa] ] ] ] ].
            exists (tp,p'), (union h3 h4), h2. intuition.
            -- rewrite Hun' in Hdis...
            -- rewrite <- Hun'...
            -- exists h3, h4. intuition.
         ** intro r. simpl. apply hass_imply_taut.
       * destruct s as (tp,p'); simpl.
         eapply HtBind.
         ** eapply HtConsequence with (P := <[ p <> 0 ]> * [[p |-> (tp, p')]]
                                            * isList ls p' * isa a tp)
                                      (Q := fun r => <[ p <> 0 ]>
                                                     * [[p |-> (tp, p')]]
                                                     * isList ls p'
                                                     * <[r = tt]>).
            - apply hoare_frame_left.
              apply ht_del.
            - unfold imply, ex, sep. intuition...
              destruct H0 as [h1 [h2 [Hdis [Hun [Hpure H'] ] ] ] ].
              destruct Hpure; subst.
                rewrite union_empty_neutral_left. clear Hdis.
              destruct H' as [h3 [h4 [Hdis [Hun [Hsing H'] ] ] ] ].
              destruct H' as [h5 [h6 [Hdis' [Hun' [Hisa Hlist] ] ] ] ].
              exists (union h3 h6), h5. intuition...
              -- rewrite Hun' in Hdis.
                 rewrite union_comm in Hdis...
                 apply disj_assoc_2...
                 apply disj_comm...
              -- rewrite union_assoc_1.
                 --- rewrite union_comm in Hun'...
                     rewrite <- Hun'...
                 --- rewrite Hun' in Hdis.
                     apply disj_union_disj_3 with (h2 := h5)...
                 --- apply disj_assoc_2.
                     ---- apply disj_comm...
                     ---- rewrite Hun' in Hdis. rewrite union_comm...
                          apply disj_comm...
              -- exists h3, h6. intuition.
                 --- rewrite Hun' in Hdis.
                     apply disj_union_disj_3 with (h2 := h5)...
                 --- exists empty, h3. intuition.
                     ---- apply disj_empty_neutral_left.
                     ---- unfold pure...
            - intro r. apply hass_imply_taut.
         ** destruct s.
            eapply HtBind with (Q := fun _ => (isList ls p')).
            *** eapply HtConsequence with (P := isList ls p'
                                                * exist v, [[p |-> v]])
                                          (Q := fun _ => isList ls p'
                                                         * emp).
                - apply hoare_frame_left.
                  apply HtFree.
                - unfold imply, sep. intuition...
                  destruct H0 as [h1 [h2 [Hdis [Hun [H' H''] ] ] ] ].
                  destruct H''; subst. clear H0; clear Hdis.
                    rewrite union_empty_neutral_right.
                  destruct H' as [h3 [h4 [Hdis [Hun [H' Hlist] ] ] ] ].
                  destruct H' as [h5 [h6 [Hdis' [Hun' [Hpure Hsing] ] ] ] ].
                  destruct Hpure; subst. clear Hdis'.
                    rewrite union_empty_neutral_left in *.
                  exists h4, h6. intuition.
                  -- apply disj_comm...
                  -- apply union_comm...
                  -- exists (tp,p')...
                - unfold imply, sep. intuition.
                  destruct H0 as [h1 [h2 [Hdis [Hun [Hlist Hemp] ] ] ] ].
                  unfold emp in Hemp. subst.
                  rewrite union_empty_neutral_right...
            *** intro. apply IHls.
Qed.


(* With the previous proofs, 'list T' satisfies the
   typeclass 'MyObject' whenever 'T' does so:       *)

Instance myListObject {T : Set} `{MyObject T} : MyObject (list T) :=
{
  isa := isList ;
  new := newList ;
  del := delList ;

  ht_new := ht_newList ;
  ht_del := ht_delList ;
}.


(* Lists of lists can now also be proven to satisfy
   the typeclass 'MyObject' in two equivalent ways: *)

Instance myListOfListsObject {T : Set} `{MyObject T}
  : MyObject (list (list T)) :=
{
  isa := isList ;
  new := newList ;
  del := delList ;

  ht_new := ht_newList ;
  ht_del := ht_delList ;
}.

Instance myListOfListsObject' {T : Set} `{MyObject T}
  : MyObject (list (list T)) :=
{
  isa := isa ;
  new := new ;
  del := del ;

  ht_new := ht_new ;
  ht_del := ht_del ;
}.


Close Scope hoare_scope.
Close Scope heap_scope.


