Require Import List Omega.
Set Implicit Arguments.

Inductive Tree : Set :=
| Leaf : Tree
| Node : Tree -> Tree -> Tree.

Definition incrl (d : nat) (ns : list nat) : list nat :=
  map (plus d) ns.

Fixpoint depths (t : Tree) : list nat :=
  match t with
    | Leaf => 0 :: nil
    | Node l r =>
      incrl 1 (depths l) ++ incrl 1 (depths r)
  end.

Definition ofs_depths (d : nat) (t : Tree) : list nat :=
  incrl d (depths t).

Inductive ofs_depths_spec (d : nat) : Tree -> list nat -> Prop :=
| ofs_depths_Leaf : ofs_depths_spec d Leaf (d :: nil)
| ofs_depths_Node :
  forall tl tr nsl nsr,
    ofs_depths_spec (S d) tl nsl ->
    ofs_depths_spec (S d) tr nsr ->
    ofs_depths_spec d (Node tl tr) (nsl ++ nsr).

Lemma ofs_depthsP :
  forall d t ns,
    ofs_depths d t = ns <-> ofs_depths_spec d t ns.
Proof.
split.
  revert d ns; induction t.
    intros d ns H; rewrite <-H.
    unfold ofs_depths, incrl; simpl.
    rewrite <- plus_n_O.
    constructor.
  intros d ns H; rewrite <-H.
  unfold ofs_depths, incrl; simpl.
  rewrite map_app.
  constructor; [apply IHt1|apply IHt2];
    unfold ofs_depths, incrl; rewrite map_map; apply map_ext; intro; omega.
revert d ns; induction t.
  intros d ns H; inversion H.
  unfold ofs_depths, incrl; simpl; rewrite <-plus_n_O; reflexivity.
intros d ns H; inversion H; subst.
rewrite <-(IHt1 (S d) nsl); auto.
rewrite <-(IHt2 (S d) nsr); auto.
unfold ofs_depths, incrl; simpl.
rewrite map_app.
f_equal; unfold incrl; rewrite map_map; apply map_ext; intro; omega.
Qed.

Inductive prefix_ofs_depths (d : nat) (t : Tree) : list nat -> Prop :=
| prefix_ofs_depths_app :
  forall nsl nsr,
    ofs_depths d t = nsl ->
    prefix_ofs_depths d t (nsl ++ nsr).
