Module RedBlackTree.

Inductive Color: Set := Red | Black.

Inductive Node {T: Type}: Type :=
  | make_node: Color -> T -> Node.

Definition GetColor {T: Type} (n: @Node T): Color :=
  match n with
  | make_node Red _ => Red
  | make_node Black _ => Black
  end.

Definition NatNode: Set := @Node nat.

Example redTwo: NatNode := make_node Red 2.
Example blackThree: NatNode := make_node Black 3.

Compute GetColor redTwo.
Compute GetColor blackThree.

Record Tree (T: Type): Type := make_tree {
  get_root: @Node T
}.

Example twoTree: Tree nat := make_tree nat redTwo.



