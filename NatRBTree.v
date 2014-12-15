Require Import Arith.
Inductive Color : Set := R | B.

Inductive Tree: Type :=
  | E: Tree
  | T: Color -> Tree -> nat -> Tree -> Tree.

(*Member*)
Fixpoint member (x: nat) (t: Tree): bool :=
  match t with
    | E => false
    | T _ a y b => match nat_compare x y with
                     | Lt => member x a
                     | Eq => true
                     | Gt => member x b
                   end
  end.

Definition balance (t: Tree): Tree :=
  match t with
    | E => E
    | T B (T R (T R a x b) y c) z d => T R (T B a x b) y (T B c z d)
    | T B (T R a x (T R b y c)) z d => T R (T B a x b) y (T B c z d)
    | T B a x (T R (T R b y c) z d) => T R (T B a x b) y (T B c z d)
    | T B a x (T R b y (T R c z d)) => T R (T B a x b) y (T B c z d)
    | T color a x b => T color a x b             
  end.

Fixpoint ins (x: nat) (t: Tree): Tree :=
  match t with
      | E => T R E x E
      | T color a y b => match nat_compare x y with
                           | Lt => balance (T color (ins x a) y b)
                           | Eq => T color a y b
                           | Gt => balance (T color a y (ins x b))
                         end
  end.

Definition make_black (t: Tree): Tree :=
  match t with
    | E => E
    | T _ a y b => T B a y b
  end.

Definition insert (x: nat) (t: Tree): Tree :=
  make_black (ins x t).

Example t2 := insert 4 (insert 5 (insert 8 (insert 9 (insert 2 (insert 0 (insert 99 E)))))).


Definition left (t: Tree): Tree :=
  match t with
    | E => E
    | T _ a _ _ => a
  end.

Definition right (t: Tree): Tree :=
  match t with
    | E => E
    | T _ _ _ b => b
  end.

Definition color (t: Tree): option Color :=
  match t with
    | E => None
    | T c _ _ _ => Some c
  end.

Definition value (t: Tree): option nat :=
  match t with
    | E => None
    | T c a x b => Some x
  end.

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) := 
  match l with
  | nil      => cons v nil
  | cons h t => cons h (snoc t v)
  end.

Fixpoint traversal (t: Tree): list nat :=
  match t with
    | E => nil
    | T c E x E => cons x nil
    | T c a x E => snoc (traversal a) x
    | T c E x b => cons x (traversal b)
    | T C a x b => app (snoc (traversal a) x) (traversal b)
  end.

Fixpoint black_height (t: Tree): nat :=
  match t with
    | E => 0
    | T B a x b => min (1 + black_height a) (1 + black_height b)
    | T R a x b => min (black_height a) (black_height b)
  end.

Theorem balanced: forall t: Tree, black_height (left t) = black_height (right t).
Proof.
  intros. induction t.
  simpl. reflexivity.
  simpl. unfold left in IHt1. unfold right in IHt1. unfold black_height.
Abort.

Notation "a /- x -\ y" := (T R a x y) (at level 50, left associativity).
Notation "a //- x -\\ y" := (T B a x y) (at level 50, left associativity).
