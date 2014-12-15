Set Implicit Arguments.
Require Import Arith.
Require Import CpdtTactics.
Inductive color : Set := Red | Black.
Inductive rbtree : color -> nat -> Set :=
| Leaf : rbtree Black 0
| RedNode : forall n, rbtree Black n -> nat -> rbtree Black n -> rbtree Red n
| BlackNode : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rbtree Black (S n).

Require Import Max Min.
Section depth.
  Variable f : nat -> nat -> nat.

  Fixpoint depth c n (t : rbtree c n) : nat :=
    match t with
      | Leaf => 0
      | RedNode _ t1 _ t2 => S (f (depth t1) (depth t2))
      | BlackNode _ _ _ t1 _ t2 => S (f (depth t1) (depth t2))
    end.
End depth.

Theorem depth_min : forall c n (t : rbtree c n), depth min t >= n.
  induction t; crush;
    match goal with
      | [ |- context[min ?X ?Y] ] => destruct (min_dec X Y)
    end; crush.
Qed.

Lemma depth_max' : forall c n (t : rbtree c n), match c with
                                                  | Red => depth max t <= 2 * n + 1
                                                  | Black => depth max t <= 2 * n
                                                end.
  induction t; crush;
    match goal with
      | [ |- context[max ?X ?Y] ] => destruct (max_dec X Y)
    end; crush;
    repeat (match goal with
              | [ H : context[match ?C with Red => _ | Black => _ end] |- _ ] =>
                destruct C
            end; crush).
Qed.

Theorem depth_max : forall c n (t : rbtree c n), depth max t <= 2 * n + 1.
  intros; generalize (depth_max' t); destruct c; crush.
Qed.

Theorem balanced : forall c n (t : rbtree c n), 2 * depth min t + 1 >= depth max t.
  intros; generalize (depth_min t); generalize (depth_max t); crush.
Qed.

Inductive rtree : nat -> Set :=
| RedNode' : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rtree n.

Section present.
  Variable x : nat.

  Fixpoint present c n (t : rbtree c n) : Prop :=
    match t with
      | Leaf => False
      | RedNode _ a y b => present a \/ x = y \/ present b
      | BlackNode _ _ _ a y b => present a \/ x = y \/ present b
    end.

  Definition rpresent n (t : rtree n) : Prop :=
    match t with
      | RedNode' _ _ _ a y b => present a \/ x = y \/ present b
    end.
End present.

Notation "{< x >}" := (existT _ _ x).

Definition balance1 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n
    -> { c : color & rbtree c (S n) } with
    | RedNode' _ c0 _ t1 y t2 =>
      match t1 in rbtree c n return rbtree c0 n -> rbtree c2 n
        -> { c : color & rbtree c (S n) } with
        | RedNode _ a x b => fun c d =>
          {<RedNode (BlackNode a x b) y (BlackNode c data d)>}
        | t1' => fun t2 =>
          match t2 in rbtree c n return rbtree Black n -> rbtree c2 n
            -> { c : color & rbtree c (S n) } with
            | RedNode _ b x c => fun a d =>
              {<RedNode (BlackNode a y b) x (BlackNode c data d)>}
            | b => fun a t => {<BlackNode (RedNode a y b) data t>}
          end t1'
      end t2
  end.

Definition balance2 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n -> { c : color & rbtree c (S n) } with
    | RedNode' _ c0 _ t1 z t2 =>
      match t1 in rbtree c n return rbtree c0 n -> rbtree c2 n
        -> { c : color & rbtree c (S n) } with
        | RedNode _ b y c => fun d a =>
          {<RedNode (BlackNode a data b) y (BlackNode c z d)>}
        | t1' => fun t2 =>
          match t2 in rbtree c n return rbtree Black n -> rbtree c2 n
            -> { c : color & rbtree c (S n) } with
            | RedNode _ c z' d => fun b a =>
              {<RedNode (BlackNode a data b) z (BlackNode c z' d)>}
            | b => fun a t => {<BlackNode t data (RedNode a z b)>}
          end t1'
      end t2
  end.


Section insert.
  Variable x : nat.

  (** Most of the work of insertion is done by a helper function [ins], whose return types are expressed using a type-level function [insResult]. *)

  Definition insResult c n :=
    match c with
      | Red => rtree n
      | Black => { c' : color & rbtree c' n }
    end.

  (** That is, inserting into a tree with root color [c] and black depth [n], the variety of tree we get out depends on [c].  If we started with a red root, then we get back a possibly invalid tree of depth [n].  If we started with a black root, we get back a valid tree of depth [n] with a root node of an arbitrary color.

     Here is the definition of [ins].  Again, we do not want to dwell on the functional details. *)

  Fixpoint ins c n (t : rbtree c n) : insResult c n :=
    match t with
      | Leaf => {< RedNode Leaf x Leaf >}
      | RedNode _ a y b =>
        if le_lt_dec x y
          then RedNode' (projT2 (ins a)) y b
          else RedNode' a y (projT2 (ins b))
      | BlackNode c1 c2 _ a y b =>
        if le_lt_dec x y
          then
            match c1 return insResult c1 _ -> _ with
              | Red => fun ins_a => balance1 ins_a y b
              | _ => fun ins_a => {< BlackNode (projT2 ins_a) y b >}
            end (ins a)
          else
            match c2 return insResult c2 _ -> _ with
              | Red => fun ins_b => balance2 ins_b y a
              | _ => fun ins_b => {< BlackNode a y (projT2 ins_b) >}
            end (ins b)
    end.

  (** The one new trick is a variation of the convoy pattern.  In each of the last two pattern matches, we want to take advantage of the typing connection between the trees [a] and [b].  We might %\%naive%{}%ly apply the convoy pattern directly on [a] in the first [match] and on [b] in the second.  This satisfies the type checker per se, but it does not satisfy the termination checker.  Inside each [match], we would be calling [ins] recursively on a locally bound variable.  The termination checker is not smart enough to trace the dataflow into that variable, so the checker does not know that this recursive argument is smaller than the original argument.  We make this fact clearer by applying the convoy pattern on _the result of a recursive call_, rather than just on that call's argument.

     Finally, we are in the home stretch of our effort to define [insert].  We just need a few more definitions of non-recursive functions.  First, we need to give the final characterization of [insert]'s return type.  Inserting into a red-rooted tree gives a black-rooted tree where black depth has increased, and inserting into a black-rooted tree gives a tree where black depth has stayed the same and where the root is an arbitrary color. *)

  Definition insertResult c n :=
    match c with
      | Red => rbtree Black (S n)
      | Black => { c' : color & rbtree c' n }
    end.

  (** A simple clean-up procedure translates [insResult]s into [insertResult]s. *)

  Definition makeRbtree c n : insResult c n -> insertResult c n :=
    match c with
      | Red => fun r =>
        match r with
          | RedNode' _ _ _ a x b => BlackNode a x b
        end
      | Black => fun r => r
    end.

  (** We modify Coq's default choice of implicit arguments for [makeRbtree], so that we do not need to specify the [c] and [n] arguments explicitly in later calls. *)

  Implicit Arguments makeRbtree [c n].

  (** Finally, we define [insert] as a simple composition of [ins] and [makeRbtree]. *)

  Definition insert c n (t : rbtree c n) : insertResult c n :=
    makeRbtree (ins t).

  (** As we noted earlier, the type of [insert] guarantees that it outputs balanced trees whose depths have not increased too much.  We also want to know that [insert] operates correctly on trees interpreted as finite sets, so we finish this section with a proof of that fact. *)

  Section present.
    Variable z : nat.

    (** The variable [z] stands for an arbitrary key.  We will reason about [z]'s presence in particular trees.  As usual, outside the section the theorems we prove will quantify over all possible keys, giving us the facts we wanted.

       We start by proving the correctness of the balance operations.  It is useful to define a custom tactic [present_balance] that encapsulates the reasoning common to the two proofs.  We use the keyword %\index{Vernacular commands!Ltac}%[Ltac] to assign a name to a proof script.  This particular script just iterates between [crush] and identification of a tree that is being pattern-matched on and should be destructed. *)

    Ltac present_balance :=
      crush;
      repeat (match goal with
                | [ _ : context[match ?T with Leaf => _ | _ => _ end] |- _ ] =>
                  dep_destruct T
                | [ |- context[match ?T with Leaf => _ | _ => _ end] ] => dep_destruct T
              end; crush).

    (** The balance correctness theorems are simple first-order logic equivalences, where we use the function [projT2] to project the payload of a [sigT] value. *)

    Lemma present_balance1 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
      present z (projT2 (balance1 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
      destruct a; present_balance.
    Qed.

    Lemma present_balance2 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
      present z (projT2 (balance2 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
      destruct a; present_balance.
    Qed.

    (** To state the theorem for [ins], it is useful to define a new type-level function, since [ins] returns different result types based on the type indices passed to it.  Recall that [x] is the section variable standing for the key we are inserting. *)

    Definition present_insResult c n :=
      match c return (rbtree c n -> insResult c n -> Prop) with
        | Red => fun t r => rpresent z r <-> z = x \/ present z t
        | Black => fun t r => present z (projT2 r) <-> z = x \/ present z t
      end.

    (** Now the statement and proof of the [ins] correctness theorem are straightforward, if verbose.  We proceed by induction on the structure of a tree, followed by finding case analysis opportunities on expressions we see being analyzed in [if] or [match] expressions.  After that, we pattern-match to find opportunities to use the theorems we proved about balancing.  Finally, we identify two variables that are asserted by some hypothesis to be equal, and we use that hypothesis to replace one variable with the other everywhere. *)

    Theorem present_ins : forall c n (t : rbtree c n),
      present_insResult t (ins t).
      induction t; crush;
        repeat (match goal with
                  | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
                  | [ |- context[if ?E then _ else _] ] => destruct E
                  | [ _ : context[match ?C with Red => _ | Black => _ end]
                      |- _ ] => destruct C
                end; crush);
        try match goal with
              | [ _ : context[balance1 ?A ?B ?C] |- _ ] =>
                generalize (present_balance1 A B C)
            end;
        try match goal with
              | [ _ : context[balance2 ?A ?B ?C] |- _ ] =>
                generalize (present_balance2 A B C)
            end;
        try match goal with
              | [ |- context[balance1 ?A ?B ?C] ] =>
                generalize (present_balance1 A B C)
            end;
        try match goal with
              | [ |- context[balance2 ?A ?B ?C] ] =>
                generalize (present_balance2 A B C)
            end;
        crush;
          match goal with
            | [ z : nat, x : nat |- _ ] =>
              match goal with
                | [ H : z = x |- _ ] => rewrite H in *; clear H
              end
          end;
          tauto.
    Qed.

    (** The hard work is done.  The most readable way to state correctness of [insert] involves splitting the property into two color-specific theorems.  We write a tactic to encapsulate the reasoning steps that work to establish both facts. *)

    Ltac present_insert :=
      unfold insert; intros n t; inversion t;
        generalize (present_ins t); simpl;
          dep_destruct (ins t); tauto.

    Theorem present_insert_Red : forall n (t : rbtree Red n),
      present z (insert t)
      <-> (z = x \/ present z t).
      present_insert.
    Qed.

    Theorem present_insert_Black : forall n (t : rbtree Black n),
      present z (projT2 (insert t))
      <-> (z = x \/ present z t).
      present_insert.
    Qed.
  End present.
End insert.