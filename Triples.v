
Require Import SepLogicTC.Heap.



Open Scope heap_scope.

(* Define a simple language that models heap operations: *)
Inductive cmd : Set -> Type :=
  | Return {S : Set} (r : S) : cmd S
  | Bind {Res Res' : Set}
         (c1 : cmd Res')
         (c2 : Res' -> cmd Res) : cmd Res
  | Read (S : Set) (p : nat) : cmd S
  | Write (p : nat) {S : Set} (v : S) : cmd unit
  | Alloc {S : Set} (v : S) : cmd nat
  | Free (S : Set) (p : nat) : cmd unit.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2))
                           (right associativity, at level 80) : hoare_scope.
Notation "c1 ;; c2" := (Bind c1 (fun _ => c2))
                       (right associativity, at level 80) : hoare_scope.


Reserved Notation "{{ P }} c {{ r , Q }}" (at level 90, c at next level).

(* Fairly standard definition of Hoare triples, loosely based on Chapter 14 of
   "Formal Reasoning About Programs"by Adam Chlipala, 2015-2017:
   (see also: https://github.com/achlipala/frap/blob/master/SeparationLogic.v)
*)
Inductive hoare_triple : forall {res : Set},
  hass -> cmd res -> (res -> hass) -> Prop :=
  | HtReturn : forall {res : Set} {v : res},
               {{emp}} (Return v) {{r, <[ r = v ]>}}
  | HtBind : forall P {res' res} (c1 : cmd res') (c2 : res' -> cmd res) Q R,
             {{P}} c1 {{r, Q r}} ->
             (forall s, {{Q s}} (c2 s) {{r, R r}}) ->
             {{P}} (x <- c1; c2 x) {{r, R r}}
  | HtRead : forall {S : Set} a P,
             {{exist v, [[a |-> v]] * P v}} (Read S a) {{r, [[a |-> r]] * P r}}
  | HtWrite : forall {S : Set} a (w : S),
              {{exist (v:S), [[a |-> v]]}} (Write a w) {{_, [[a |-> w]]}}
  | HtAlloc : forall {S : Set} (v : S),
              {{emp}} (Alloc v) {{p, <[p <> 0]> * [[p |-> v]]}}
  | HtFree : forall {S : Set} p,
             {{exist (v:S), [[p |-> v]]}} (Free S p) {{_, emp}}
  | HtConsequence : forall {res} (c : cmd res) P Q
                                               (P' : hass) (Q' : _ -> hass),
                    {{P}} c {{r, Q r}} ->
                    P' ==> P ->
                    (forall r, Q r ==> Q' r) ->
                    {{ P' }} c {{r, Q' r}}
  | HtFrame : forall {res} (c : cmd res) P Q R,
              {{P}} c {{r , Q r}} ->
              {{P * R}} c {{r , Q r * R}}

where "{{ P }} c {{ r , Q }}" := (hoare_triple P c (fun r => Q)) 
                                 : hoare_scope.


Lemma hoare_equiv_left' {res : Set} : forall P Q (R : res -> hass) c,
  P === Q -> hoare_triple Q c R -> hoare_triple P c R.
Proof with auto.
  intuition.
  apply hass_equiv_imply in H.
  apply (HtConsequence c Q R P R H0) in H...
  intro r; apply hass_imply_taut.
Qed.

Lemma hoare_equiv_left {res : Set} : forall P Q (R : res -> hass) c,
  P === Q -> (hoare_triple Q c R <-> hoare_triple P c R).
Proof with auto.
  intuition; eapply hoare_equiv_left'.
  + exact H...
  + auto.
  + apply hass_equiv_symm in H. exact H.
  + auto.
Qed.

Lemma hoare_equiv_right' {res : Set} : forall P (Q R : res -> hass) c,
  (forall r, Q r === R r) -> hoare_triple P c Q -> hoare_triple P c R.
Proof with auto.
  intuition.
  apply (HtConsequence c P Q P R) in H0...
  apply hass_imply_taut...
  intro r; specialize H with r; apply hass_equiv_imply...
Qed.

Lemma hoare_equiv_right {res : Set} : forall P (Q R : res -> hass) c,
  (forall r, Q r === R r) -> (hoare_triple P c Q <-> hoare_triple P c R).
Proof with auto.
  intuition; eapply hoare_equiv_right'.
  + exact H.
  + auto.
  + intro r. apply hass_equiv_symm...
  + auto.
Qed.

Lemma hoare_frame_left {res : Set} : forall P (Q : res -> hass) R c,
  hoare_triple P c Q -> hoare_triple (R*P) c (fun r => R*(Q r)).
Proof with auto.
  intuition.
  eapply hoare_equiv_left'. exact (sep_comm R P).

  assert(forall r, (fun x => R * Q x) r === (fun x => (Q x) * R) r).
    intro r. apply sep_comm.
  eapply hoare_equiv_right' with (Q0 := fun x => (Q x) * R).
  + intro r. simpl. apply sep_comm.
  + apply HtFrame. apply H.
Qed.

Lemma hoare_cancel_empty_left {res : Set} : forall P (Q : res -> hass) c,
  hoare_triple (emp*P) c (fun r => emp*(Q r)) -> hoare_triple P c Q.
Proof.
  intuition.
  pose proof (sep_empty_neutral_left P).
  apply hass_equiv_symm in H0. apply (hoare_equiv_left' _ _ Q c H0).
  assert(forall r, emp * (Q r) === Q r).
    intro r. apply sep_empty_neutral_left...
  eapply hoare_equiv_right'.
    intro r. exact (H1 r).
  exact H.
Qed.

Lemma hoare_cancel_empty_left_pre {res : Set} : forall P (Q : res -> hass) c,
  hoare_triple (emp*P) c (fun r => (Q r)) -> hoare_triple P c Q.
Proof.
  intuition.
  pose proof (sep_empty_neutral_left P).
  apply hass_equiv_symm in H0. apply (hoare_equiv_left' _ _ Q c H0).
  exact H.
Qed.

Lemma hoare_cancel_empty_right {res : Set} : forall P (Q : res -> hass) c,
  hoare_triple (P*emp) c (fun r => (Q r)*emp) -> hoare_triple P c Q.
Proof.
  intuition.
  pose proof (sep_empty_neutral_right P).
  apply hass_equiv_symm in H0. apply (hoare_equiv_left' _ _ Q c H0).
  assert(forall r, (Q r)*emp === Q r).
    intro r. apply sep_empty_neutral_right...
  eapply hoare_equiv_right'.
    intro r. exact (H1 r).
  exact H.
Qed.

Lemma hoare_cancel_empty_right_pre {res : Set} : forall P (Q : res -> hass) c,
  hoare_triple (P*emp) c (fun r => (Q r)) -> hoare_triple P c Q.
Proof.
  intuition.
  pose proof (sep_empty_neutral_right P).
  apply hass_equiv_symm in H0. apply (hoare_equiv_left' _ _ Q c H0).
  exact H.
Qed.

Lemma hoare_return {res : Set} : forall (P : hass) (v : res),
  hoare_triple P (Return v) (fun r => P * <[r = v]>).
Proof with auto.
  intuition.
  apply hoare_cancel_empty_right_pre.
  apply hoare_frame_left.
  apply HtReturn.
Qed.


Open Scope hoare_scope.

Lemma hoare_read : forall {S : Set} p v,
  {{[[p |-> v]]}} (Read S p) {{r, [[p |-> v]] * <[r = v]>}}.
Proof with auto.
  intuition.
  eapply HtConsequence with (P := exist w, [[p |-> w]] * <[w = v]>).
  + apply HtRead.
  + unfold ex, imply, sep. intuition.
    exists v, h, empty. intuition...
    - apply disj_empty_neutral_right.
    - rewrite union_empty_neutral_right...
    - unfold pure...
  + unfold imply, sep.
    firstorder; subst.
    exists x, empty; firstorder.
Qed.

Lemma hoare_read_frame_right : forall {S : Set} p (v : S) P,
  {{[[p |-> v]] * P}} (Read S p) {{r, [[p |-> v]] * <[r = v]> * P}}.
Proof with auto.
  intuition.
  eapply HtFrame.
  apply hoare_read.
Qed.

Lemma hoare_read_frame_left' : forall {S : Set} p (v : S) P,
  {{P * [[p |-> v]]}} (Read S p) {{r, P * ([[p |-> v]] * <[r = v]>)}}.
Proof with auto.
  intuition.
  eapply hoare_frame_left.
  apply hoare_read.
Qed.

Lemma hoare_read_frame_left : forall {S : Set} p (v : S) P,
  {{P * [[p |-> v]]}} (Read S p) {{r, P * [[p |-> v]] * <[r = v]>}}.
Proof with auto.
  intuition.
  eapply HtConsequence with (Q := fun r => P * ([[p |-> v]] * <[r = v]>)).
  + apply hoare_read_frame_left'.
  + apply hass_imply_taut.
  + intro r.
    unfold imply, sep.
    firstorder; subst.
    exists (union x x1), empty; firstorder.
    - inversion H0.
    - repeat rewrite union_empty_neutral_right...
    - exists x, x1; firstorder.
      * destruct (x1 n) eqn:?...
        assert(union x1 empty n = None) by firstorder.
        unfold union in H4; rewrite Heqo in H4...
      * apply H3. exists x0. unfold union. rewrite H0...
Qed.


Ltac hoare_false_pre_subgoal tac :=
   eapply HtConsequence ;
   (apply HtFrame; apply tac) ||
   (apply hass_ex_falso) ||
   (intuition; apply hass_ex_falso_framed_left).

Lemma hoare_false_pre {S : Set} : forall (c : cmd S) (Q : S -> hass),
  {{<[False]>}} c {{r, Q r}}.
Proof with auto.
  intros c Q. induction c.
  + hoare_false_pre_subgoal (@HtReturn S).
  + apply HtBind with (Q := fun _ => <[False]>).
    - apply IHc.
    - intro; apply H.
  + hoare_false_pre_subgoal (@HtRead S).
  + hoare_false_pre_subgoal (@HtWrite S).
  + hoare_false_pre_subgoal (@HtAlloc S).
  + hoare_false_pre_subgoal (@HtFree S).
  Unshelve. exact Q.
Qed.

Lemma hoare_false_pre' {res : Set} : forall (c : cmd res) P Q,
  P ==> <[False]> -> {{P}} c {{r, Q r}}.
Proof with auto.
  intros.
  eapply HtConsequence.
  + apply hoare_false_pre.
  + exact H.
  + intro r. apply hass_imply_taut.
Qed.

Close Scope hoare_scope.
Close Scope heap_scope.
