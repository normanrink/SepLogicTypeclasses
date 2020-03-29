
Require Import Coq.Program.Equality.
Require Import PeanoNat.
Require Import List.

Import ListNotations.


Definition Output := list nat. (* Program output is a sequence of naturals. *)
Definition State  := list nat. (* Simple model of program state. *)


(* Simple language with state and output: *)

Inductive cmd : Set -> Type :=
  | Return {S : Set} (r : S) : cmd S
  | Bind {res res' : Set}
         (c1 : cmd res') (c2 : res' -> cmd res) : cmd res
  | GetState : cmd State
  | SetState (s : State) : cmd unit
  | Write (m : nat) : cmd unit. (* for writing output *)


Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2))
                           (right associativity, at level 80).
Notation "c1 ;; c2" := (Bind c1 (fun _ => c2))
                       (right associativity, at level 80).


(* Operational semantics,
   defining how 'cmd' modifies state and output: *)

Inductive evalCmd : forall {S : Set},
  State * Output -> cmd S -> (S * State * Output) -> Prop :=
  | EReturn : forall {res : Set} s m (r : res),
                evalCmd (s,m) (Return r) (r,s,m)
  | EGetState : forall s m, evalCmd (s,m) GetState (s,s,m)
  | ESetState : forall s s' m, evalCmd (s,m) (SetState s') (tt,s',m)
  | EWrite : forall s m n, evalCmd (s,m) (Write n) (tt,s,n::m)
  | EBind : forall {res' res : Set} s0 s1 s2 m0 m1 m2 c1 c2 (x : res') (y : res),
              evalCmd (s0,m0) c1     (x,s1,m1) ->
              evalCmd (s1,m1) (c2 x) (y,s2,m2) ->
                evalCmd (s0,m0) (Bind c1 c2) (y,s2,m2).



(* Simple example programs,
   together with proofs of their specifications
   with respect to the operation semantics as
   defined by relation 'evalCmd':               *)

Definition two_words :=
  Write 0;;
  Write 1.

Lemma spec_two_words : forall s m,
  evalCmd (s, m) two_words (tt, s, 1::0::m).
Proof with auto.
  intros.
  eapply EBind.
  * apply EWrite.
  * apply EWrite.
Qed.


Definition is_zero :=
  x <- GetState;
  match x with
    | []     => Return 0
    | x0::tl => (if (x0 =? 0)
                    then (Write 0;; SetState tl)
                    else Write 1);;
                Return 1
  end.

Lemma spec_is_zero_1 : forall m,
  evalCmd ([], m) is_zero (0, [], m).
Proof with auto.
  intros.
  eapply EBind.
  * apply EGetState.
  * simpl.
    apply EReturn...
Qed.

Lemma spec_is_zero_2 : forall s' m,
  evalCmd (0::s', m) is_zero (1, s', 0::m).
Proof with auto.
  intros.
  eapply EBind.
  * apply EGetState.
  * simpl.
    eapply EBind.
    + eapply EBind.
      - apply EWrite.
      - apply ESetState.
    + apply EReturn...
Qed.

Lemma spec_is_zero_3 : forall (n : nat) s' m,
  evalCmd (S n::s', m) is_zero (1, S n::s', 1::m).
Proof with auto.
  intros.
  eapply EBind.
  * apply EGetState.
  * simpl.
    eapply EBind.
    - apply EWrite.
    - apply EReturn...
Qed.


(* Recursive programs can be defined, provided
   they pass Coq's termination checker:        *)
Definition fact :=
  fix f (n : nat) :=
    match n with
      | 0   => SetState [1]
      | S k => f k;; 
               x <- GetState;
               match head x with
                 | Some s => SetState [n*s]
                 | _ => Return tt
               end
    end.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => 1
    | S n => S n * factorial n
  end.

Lemma spec_fact : forall n s m,
  evalCmd (s, m) (fact n) (tt, [factorial n], m).
Proof with auto.
  induction n; simpl; intuition.
  + constructor.
  + eapply EBind.
    - apply IHn.
    - eapply EBind.
      * apply EGetState.
      * simpl.
        apply ESetState.
Qed.


Definition message_or_update :=
  fun x n => if x =? 0
                then s <- GetState;
                     Write (hd 42 s) (* default value '42' *)
                     (* Our specification for 'mesage_or_update' below
                        assumes that the state is non-empty. Therefore
                        the default value '42' is not used in proving
                        the specification.                             *)
                else fact n.

Lemma spec_message_or_update_1 : forall s0 s m n,
  evalCmd (s0::s, m)
          (message_or_update 0 n)
          (tt, s0::s, s0::m).
Proof with auto.
  intros.
  unfold message_or_update. simpl.
  eapply EBind.
  + apply EGetState.
  + simpl.
    apply EWrite.
Qed.

Lemma spec_message_or_update_2 : forall k s m n,
  evalCmd (s, m)
          (message_or_update (S k) n)
          (tt, [factorial n], m).
Proof with auto.
  intros.
  unfold message_or_update. simpl.
  apply spec_fact.
Qed.



Definition assertion := State -> Output -> Prop.

(* Axiomatic semantics for 'cmd',
   in terms of Hoare-syle triples: *)

Inductive triple : forall {res : Set},
  assertion -> cmd res -> (res -> assertion) -> Prop :=
  | TReturn : forall {res : Set} {v : res} (ass : assertion),
                triple ass (Return v) (fun r s m => r = v /\ ass s m)

  | TGetState : forall (ass : assertion),
                  triple ass GetState (fun r s m => r = s /\ ass s m)

  | TSetState : forall (mass : Output -> Prop) (s' : State),
                  triple (fun _ m => mass m)
                        (SetState s')
                        (fun r s m => r = tt /\ s = s' /\ mass m)

  | TWrite : forall (ass : assertion) (n : nat),
              triple ass (Write n) (fun r s m => r = tt /\ head m = Some n /\ ass s (tl m))

  | TBind : forall {res' res}
                   (c1 : cmd res') (c2 : res' -> cmd res)
                   sa1 sa2 sa3,
            triple sa1 c1 sa2 ->
            (forall x, triple (sa2 x) (c2 x) sa3) ->
              triple sa1 (x <- c1; c2 x) sa3

  | TConseq : forall {res} (c : cmd res)
                     (sa1 sa1' : assertion) (sa2 sa2' : res -> assertion),
              triple sa1 c sa2 ->
              (forall s m, sa1' s m -> sa1 s m) ->
              (forall r m s, sa2 r m s -> sa2' r m s) ->
                triple sa1' c sa2'.


(* Triples are sound with respect to the operational semantics: *)

Lemma triple_sound : forall {res: Set} ass (c : cmd res) ass',
  triple ass c ass' ->
    forall  s m (r :res) s' m',
      ass s m -> evalCmd (s,m) c (r,s',m') ->
        ass' r s' m'.
Proof with auto.
  intros res ass c ass' Ht. induction Ht; intros.
  * inversion H0.
    dependent destruction H5. dependent destruction H6. subst.
    intuition.
  * inversion H0.
    dependent destruction H2. subst.
    intuition.
  * inversion H0.
    dependent destruction H5. subst.
    intuition.
  * inversion H0.
    dependent destruction H5. subst.
    intuition.
  * inversion H2.
    dependent destruction H8. dependent destruction H9. dependent destruction H10.
    subst.
    eapply H0.
    + eapply IHHt.
      - exact H1.
      - apply H7.
    + apply H13.
  * apply H0.
    eapply IHHt.
    + apply H. exact H1.
    + exact H2.
Qed.


(* Weakest precondition 'wp': *)

Definition wp {res : Set} (c : cmd res) (ass' : res -> assertion) : assertion :=
  fun s m => forall r s' m', evalCmd (s,m) c (r,s',m') -> ass' r s' m'.


(* 'wp' is indeed the weakest preconsition: *)
Lemma wp_weakest : forall {res : Set} (c : cmd res) ass (ass' : res -> assertion),
  (forall s m (r : res) s' m',
     ass s m -> evalCmd (s,m) c (r,s',m') -> ass' r s' m') ->
  (forall s m, ass s m -> wp c ass' s m).
Proof with auto.
  unfold wp.
  intuition.
  eapply H.
  * exact X.
  * exact H0.
Qed.

(* 'wp' satisfies 'triple': *)
Lemma wp_triple : forall {res : Set} (c : cmd res) (ass' : res -> assertion),
  triple (wp c ass') c ass'.
Proof with auto.
  induction c; intro ass'.
  * eapply TConseq with (sa1 := ass' r).
    + apply TReturn.
    + unfold wp. intuition. apply H. constructor.
    + intuition. destruct H. rewrite H...
  * eapply TConseq with (sa1 := wp c (fun r => wp (c2 r) ass')).
    + apply TBind with (sa2 := fun r => wp (c2 r) ass').
      - apply IHc.
      - intro x. apply H.
    + intros s m. unfold wp. intuition.
      apply H0.
      eapply EBind. apply H1. apply H2.
    + intuition.
  * eapply TConseq.
    + apply TGetState.
    + intuition. unfold wp in H. apply H. apply EGetState.
    + intuition. destruct H. rewrite H...
  * eapply TConseq.
    + apply TSetState.
    + intuition. unfold wp in H. apply H. apply ESetState.
    + intuition. destruct H as [H1 [H2 H3]]. rewrite H1. rewrite H2...
  * eapply TConseq.
    + apply TWrite.
    + intuition. unfold wp in H. apply H. apply EWrite.
    + intuition. destruct H as [H1 [H2 H3]].
      pose proof (hd_error_tl_repr s m (tl s)).
      assert (hd_error s = Some m /\ tl s = tl s).
        split; intuition.
      apply H in H0.
      rewrite H0. rewrite H1...
Qed.


(* Triples are complete with respect to the operational semantics: *)

Lemma triple_complete : forall {res: Set} (ass : assertion) 
                               (c : cmd res) (ass' : res -> assertion),
  (forall s m (r :res) s' m',
    ass s m -> evalCmd (s,m) c (r,s',m') -> ass' r s' m') ->
      triple ass c ass'.
Proof with auto.
  intros res ass c ass' H.
  pose proof (@wp_weakest res c ass ass' H).
  apply TConseq with (sa1 := wp c ass') (sa2 := ass').
  + apply wp_triple.
  + exact H0.
  + intuition.
Qed.


Lemma triple_ex_falso : forall {res : Set} (c : cmd res)
                               (ass' : res -> assertion),
  triple (fun _ _ => False) c ass'.
Proof with auto.
  induction c; intro ass'.
  + eapply TConseq with (sa1 := ass' r).
    - apply TReturn.
    - intuition.
    - intuition. destruct H. rewrite H...
  + eapply TConseq.
    - eapply TBind.
      * apply IHc.
      * intro x. apply H.
    - intuition.
    - intuition. apply H0.
  + eapply TConseq with (sa1 := fun s m => ass' s s m).
    - apply TGetState.
    - intuition.
    - simpl. intuition. rewrite H0. apply H1.
  + eapply TConseq.
    - apply TSetState with (mass := ass' tt s).
    - intuition.
    - simpl. intuition. rewrite H0. rewrite H. apply H2.
  + eapply TConseq with (sa1 := fun s m' => ass' tt s (m::m')).
    - apply TWrite.
    - intuition.
    - simpl. intuition.
      pose proof (hd_error_tl_repr s m (tl s)).
      assert (hd_error s = Some m /\ tl s = tl s).
        split; intuition.
      apply H1 in H3.
      rewrite H3. rewrite H0...
Qed.


Lemma spec'_two_words : forall s m,
  triple (fun s' m' => s' = s /\ m' = m)
        two_words
        (fun r s' m' => r = tt /\ s' = s /\ m' = 1::0::m).
Proof with auto.
  intros.
  eapply TBind.
  + apply TWrite.
  + destruct x.
    eapply TConseq with (sa1 := fun s' m' => s' = s /\ m' = 0::m)
                        (sa2 := fun r s' m' => r = tt /\ head m' = Some 1 /\ (s' = s /\ tl m' = 0::m)).
    all: intuition.
    - eapply TWrite.
    - pose proof (hd_error_tl_repr m0 0 (tl m0)).
      assert (hd_error m0 = Some 0 /\ tl m0 = tl m0).
        split; intuition.
      apply H2 in H4.
      rewrite <- H3...
    - pose proof (hd_error_tl_repr s0 1 (tl s0)).
      assert (hd_error s0 = Some 1 /\ tl s0 = tl s0).
        split; intuition.
      apply H2 in H4.
      rewrite H3 in H4...
Qed.


Lemma spec'_is_zero_1 : forall (m : Output),
  triple (fun s' m' => s' = [] /\ m' = m)
        is_zero
        (fun r s' m' => r = 0 /\ s' = [] /\ m' = m).
Proof with auto.
  intros.
  eapply TBind.
  * apply TGetState.
  * simpl. destruct x eqn:?.
    + eapply TConseq with (sa1 := fun s' m' => s' = [] /\ m' = m).
      - apply TReturn.
      - intuition.
      - simpl. intuition.
    + eapply TConseq with (sa1 := fun _ _ => False)
                          (sa2 := fun r s' m' => r = 0 /\ s' = [] /\ m' = m).
      - apply triple_ex_falso.
      - intuition.
        rewrite H in H0. inversion H0.
      - intuition.
Qed.

Lemma spec'_is_zero_2 : forall (s : State) (m : Output),
  triple (fun s' m' => s' = 0::s /\ m' = m)
        is_zero
        (fun r s' m' => r = 1 /\ s' = s /\ m' = 0::m).
Proof with auto.
  intros.
  eapply TBind.
  * apply TGetState.
  * simpl. destruct x eqn:?.
    + eapply TConseq with (sa1 := fun _ _ => False).
      - apply TReturn.
      - intuition.
        rewrite <- H0 in H. inversion H.
      - intuition; destruct H; inversion H0.
    + destruct n eqn:?; simpl.
      - eapply TBind with (sa2 := fun r s' m' => r = tt /\ s' = s0 /\ s' = s /\ m' = 0::m).
        ** eapply TBind with (sa2 := fun r s' m' => s' = 0::s0 /\ s' = 0::s /\ m' = 0::m /\ s0 = s).
           ++ eapply TConseq with (sa1 := fun s' m' => s' = 0::s /\ m' = m /\ s0 = s).
              -- apply TWrite.
              -- intuition. rewrite H in H0. inversion H0...
              -- intuition.
                 all: destruct H as [H1 [H2 [H3 [H4 H5]]]]; subst; auto.
                 pose proof (hd_error_tl_repr s1 0 (tl s1)).
                 assert (hd_error s1 = Some 0 /\ tl s1 = tl s1).
                   split; intuition.
                 apply H in H0...
           ++ intuition.
              eapply TConseq with (sa1 := fun _ m' => m' = 0::m /\ s0 = s).
              -- apply TSetState.
              -- intuition.
              -- intuition.
                 all: destruct H as [H1 [H2 [H3 H4]]]; subst; auto.
       ** destruct x0.
          eapply TConseq with (sa1 := fun s' m' => s' = s0 /\ s0 = s /\ m' = 0::m).
          ++ apply TReturn.
          ++ intuition.
             rewrite H in H1...
          ++ intuition.
             all: destruct H as [H1 [H2 [H3 H4]]]; subst; auto.
      - eapply TConseq with (sa1 := fun _ _ => False)
                            (sa2 := fun r s' m' => r = 1 /\ s' = s /\ m' = 0::m).
        all: intuition.
        ** apply triple_ex_falso.
        ** rewrite H in H0. inversion H0.
Qed.

Lemma spec'_is_zero_3 : forall (n : nat) (s : State) (m : Output),
  triple (fun s' m' => s' = S n::s /\ m' = m)
        is_zero
        (fun r s' m' => r = 1 /\ s' = S n::s /\ m' = 1::m).
Proof with auto.
  intros.
  eapply TBind.
  * apply TGetState.
  * simpl. destruct x eqn:?.
    + eapply TConseq with (sa1 := fun _ _ => False)
                          (sa2 := fun r s' m' => r = 1 /\ s' = S n::s /\ m' = 1::m).
      all: intuition.
      - apply triple_ex_falso.
      - rewrite H in H0. inversion H0.
    + destruct n0 eqn:?; simpl.
      - eapply TConseq with (sa1 := fun _ _ => False)
                            (sa2 := fun r s' m' => r = 1 /\ s' = S n::s /\ m' = 1 :: m).
        all: intuition.
        ** apply triple_ex_falso.
        ** rewrite H in H0. inversion H0.
      - apply TBind with (sa2 := fun r s' m' => s' = S n1::s0 /\ s = s0 /\ n = n1 /\ m' = 1::m).
        ** eapply TConseq.
           ++ apply TWrite with (ass := fun s' m' => s' = S n1::s0 /\ s = s0 /\ n = n1 /\ m' = m).
           ++ intuition.
              all: rewrite H in H0; inversion H0; auto.
           ++ intuition.
              all: destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]; subst; auto.
              pose proof (hd_error_tl_repr s1 1 (tl s1)).
              assert (hd_error s1 = Some 1 /\ tl s1 = tl s1).
                split; intuition.
              apply H in H0...
        ** intuition. 
           eapply TConseq with (sa2 := fun r s' m' => r = 1 /\ s' = S n::s /\ s = s0 /\ n = n1 /\ m' = 1::m).
           ++ apply TReturn.
           ++ intuition; subst...
           ++ intuition.
Qed.


Lemma spec'_fact : forall n s m,
  triple (fun s' m' => s' = s /\ m' = m)
        (fact n)
        (fun r s' m' => r = tt /\ s' = [factorial n] /\ m' = m).
Proof with auto.
  induction n; simpl; intuition.
  + eapply TConseq.
    - apply TSetState with (mass := fun m' => m' = m).
    - intuition.
    - intuition.
      all: destruct H as [H1 [H2 H3]]; auto.
  + eapply TBind.
    - apply IHn.
    - destruct x.
      eapply TBind.
      * apply TGetState.
      * simpl. destruct x eqn:?.
        ++ eapply TConseq with (sa1 := fun _ _ => False)
                               (sa2 := fun r s' m' => r = tt /\
                                                      s' = [factorial n + n * factorial n] /\ 
                                                      m' = m).
           -- apply triple_ex_falso.
           -- intuition.
              rewrite H1 in H0. inversion H0.
           -- intuition.
        ++ eapply TConseq with (sa1 := fun s' m' => s' = [factorial n] /\
                                                    m' = m /\
                                                    n0 = factorial n /\
                                                    s0 = [])
                               (sa2 := fun r s' m' => r = tt /\
                                                      s' = [factorial n + n * factorial n] /\ 
                                                      m' = m).
           -- simpl; subst.
              destruct (Nat.eq_dec n0 (factorial n)) eqn:?.
              ** subst.
                 eapply TConseq.
                 +++ apply TSetState with (mass := fun m' => m' = m).
                 +++ intuition.
                 +++ intuition.
                     all: destruct H as [H1 [H2 H3]]; auto.
              ** eapply TConseq with (sa1 := fun _ _ => False)
                                     (sa2 := fun r s' m' => r = tt /\
                                                            s' = [factorial n + n * factorial n] /\ 
                                                            m' = m).
                 +++ apply triple_ex_falso.
                 +++ intuition.
                 +++ intuition.
           -- intuition.
              all: rewrite H1 in H0; inversion H0; auto.
           -- intuition.
Qed.


Lemma spec'_message_or_update_1 : forall s0 s m n,
  triple (fun s' m' => s' = s0::s /\ m' = m)
        (message_or_update 0 n)
        (fun r s' m' => r = tt /\ s' = s0::s /\ m' = s0::m).
Proof with auto.
  intros.
  unfold message_or_update. simpl.
  eapply TBind.
  + apply TGetState.
  + intro x.
    simpl.
    eapply TConseq with (sa1 := fun s' m' => x = s' /\ s' = s0 :: s /\ m' = m).
    - apply TWrite.
    - intuition.
    - intuition.
      all: destruct H as [H1 [H2 [H3 [H4 H5]]]]; subst; auto.
      simpl in H2.
      pose proof (hd_error_tl_repr s1 s0 (tl s1)).
      assert (hd_error s1 = Some s0 /\ tl s1 = tl s1).
        split; intuition.
      apply H in H0...
Qed.

Lemma spec'_message_or_update_2 : forall k s m n,
  triple (fun s' m' => s' = s /\ m' = m)
        (message_or_update (S k) n)
        (fun r s' m' => r = tt /\ s' = [factorial n] /\ m' = m).
Proof with auto.
  intros.
  unfold message_or_update. simpl.
  apply spec'_fact.
Qed.

