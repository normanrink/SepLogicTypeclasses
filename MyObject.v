
Require Import SepLogicTC.Heap.
Require Import SepLogicTC.Triples.

Require Import FunctionalExtensionality.
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
  + repeat (eapply HtBind; intuition; auto).
    - apply IHls...
    - eapply hoare_cancel_empty_left_pre.
      * apply HtFrame. apply ht_new...
    - eapply hoare_cancel_empty_left_pre. 
      * apply HtFrame. apply HtAlloc.
    - simpl. eapply HtConsequence.
      2: apply hass_imply_taut.
      * eapply hoare_cancel_empty_left_pre.
        apply hoare_return.
      * unfold imply. intuition.
        apply sep_pure_left.
        ** firstorder. subst...
        ** exists s0, s. firstorder.
           unfold emp in *; subst...
           repeat (rewrite union_empty_neutral_left in * ||
                   rewrite union_empty_neutral_right in *).
           apply sep_assoc.
           unfold sep...
           exists x8, (union x5 x6). firstorder.
Qed.

Lemma ht_delList {T : Set} `{MyObject T} : forall (ls : list T) (p : nat),
  {{isList ls p}} (delList ls p) {{r, <[r = tt]>}}.
Proof with auto.
  induction ls; intro p; simpl.
  + eapply HtConsequence with (P := emp).
    apply HtReturn.
    1,2: firstorder.
  + destruct (Nat.eqb_spec p 0).
    ++ eapply HtConsequence.
       apply HtReturn.
        1,2: firstorder.
    ++ repeat (eapply HtBind; intuition; auto).
       * apply hoare_frame_left.
         eapply HtConsequence with (P := exist v, [[p |-> v]]
                                                  * (isa a (fst v)
                                                     * isList ls (snd v))).
         ** apply HtRead.
         ** unfold ex, imply; intuition.
            destruct H0 as [x1 [x2 H0] ]. exists (x1,x2).
            apply sep_assoc...
         ** intro. apply hass_imply_taut.
       * intuition; simpl.
         apply hoare_frame_left. apply hoare_frame_left. apply HtFrame.
           apply ht_del.
       * intuition; simpl.
         apply hoare_frame_left. apply HtFrame. eapply HtConsequence.
         ** apply HtFree.
         ** firstorder.
         ** intro. simpl. apply hass_imply_taut.
       * intuition; simpl.
         eapply HtConsequence.
         ** apply IHls.
         ** unfold imply.
            firstorder.
            unfold emp in *. subst...
         ** firstorder.
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


