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

Lemma ofs_depths_1 :
  forall d t,
    ofs_depths_spec d t (ofs_depths d t).
Proof.
  intros; destruct (ofs_depthsP d t (ofs_depths d t)); auto.
Qed.

Lemma ofs_depths_2 :
  forall d t ns,
    ofs_depths_spec d t ns -> ofs_depths d t = ns.
Proof.
  intros; destruct (ofs_depthsP d t ns); auto.
Qed.

Lemma ofs_depths_Node_E :
  forall d tl tr,
    ofs_depths d (Node tl tr) = ofs_depths (S d) tl ++ ofs_depths (S d) tr.
Proof.
  intros.
  apply ofs_depths_2.
  constructor; apply ofs_depths_1.
Qed.

Lemma ofs_depths_cons :
  forall d t,
    ofs_depths d t <> nil.
Proof.
  intros d t.
  revert d; induction t.
    unfold ofs_depths, incrl; simpl; congruence.
  intros d Heq.
  generalize (ofs_depths_1 d (Node t1 t2)).
  rewrite Heq; clear Heq; intro Hofs.
  inversion Hofs; subst.
  destruct (app_eq_nil _ _ H1).
  subst.
  apply ofs_depths_2 in H3.
  eapply IHt2; eauto.
Qed.

Lemma ofs_depths_le :
  forall d t n, In n (ofs_depths d t) -> d <= n.
Proof.
  intros d t; revert d; induction t.
    unfold ofs_depths, incrl; simpl.
    intros; omega.
  unfold ofs_depths, incrl; simpl.
  intros d n H.
  rewrite map_app in H.
  apply in_app_or in H.
  cut (d + 1 <= n); [omega|].
  destruct H.
    apply IHt1.
    unfold ofs_depths, incrl.
    clear t2 IHt1 IHt2.
    induction (depths t1).
      contradiction.
    unfold incrl in *.
    rewrite map_map in *.
    destruct H.
      left; omega.
    right; auto.

    apply IHt2.
    unfold ofs_depths, incrl.
    clear t1 IHt1 IHt2.
    induction (depths t2).
      contradiction.
    unfold incrl in *.
    rewrite map_map in *.
    destruct H.
      left; omega.
    right; auto.
Qed.

Lemma ofs_depths_lt :
  forall d tl tr n, In n (ofs_depths d (Node tl tr)) -> d < n.
Proof.
  intros.
  cut (S d <= n); [omega|].
  rewrite ofs_depths_Node_E in H.
  apply in_app_or in H.
  destruct H; eapply ofs_depths_le; eauto.
Qed.

Definition is_prefix (d : nat) (t : Tree) (ns : list nat) : Prop :=
  exists lsl, exists lsr, ns = lsl ++ lsr /\ ofs_depths d t = lsl.

Lemma is_prefix' :
  forall d t ns, is_prefix d t ns ->
    exists h, exists lsl, exists lsr, ns = h :: lsl ++ lsr /\ ofs_depths d t = h :: lsl.
Proof.
  intros d t ns [lsl [lsr [Happ Hofs]]].
  destruct lsl as [|h lsl].
    exfalso.
    clear ns lsr Happ.
    generalize (ofs_depths_1 d t).
    rewrite Hofs; clear Hofs.
    revert d; induction t.
      intros d Hi; inversion Hi.
    intros d Hi; inversion Hi.
    destruct (app_eq_nil _ _ H1) as [He _].
    rewrite He in *.
    eauto.
  exists h; exists lsl; exists lsr.
  auto.
Qed.

Lemma is_prefix_Node :
  forall d tl tr ns, is_prefix d (Node tl tr) ns ->
    is_prefix (S d) tl ns.
Proof.
  intros d tl tr ns [lsl [lsr [Happ Hofs]]].
  generalize (ofs_depths_1 d (Node tl tr)).
  rewrite Hofs; clear Hofs; intro Hofs.
  inversion Hofs; subst.
  exists nsl; exists (nsr ++ lsr).
  split.
    rewrite app_assoc; auto.
  apply ofs_depths_2; auto.
Qed.

Lemma prefix_unique :
  forall d t1 t2 ns, is_prefix d t1 ns -> is_prefix d t2 ns -> t1 = t2.
Proof.
  intros d t1; revert d; induction t1.
    intros d t2 ns Hpre1 Hpre2.
    destruct (is_prefix' Hpre1) as [n1 [lsl1 [lsr1 [Happ1 Hofs1]]]].
    destruct (is_prefix' Hpre2) as [n2 [lsl2 [lsr2 [Happ2 Hofs2]]]].
    destruct t2 as [|tl2 tr2]; auto.
    exfalso.
    unfold ofs_depths, incrl in Hofs1; simpl in Hofs1.
    injection Hofs1.
    assert (d < n2).
      apply ofs_depths_lt with tl2 tr2.
      rewrite Hofs2; left; auto.
    rewrite Happ1 in Happ2.
    injection Happ2.
    intros; omega.
  intros d t2 ns Hpre1 Hpre2.
  destruct (is_prefix' Hpre1) as [n1 [lsl1 [lsr1 [Happ1 Hofs1]]]].
  destruct (is_prefix' Hpre2) as [n2 [lsl2 [lsr2 [Happ2 Hofs2]]]].
  destruct t2 as [|tl2 tr2].
    exfalso.
    unfold ofs_depths, incrl in Hofs2; simpl in Hofs2.
    injection Hofs2.
    assert (d < n1).
      apply ofs_depths_lt with t1_1 t1_2.
      rewrite Hofs1; left; auto.
    rewrite Happ2 in Happ1.
    injection Happ1.
    intros; omega.
  assert (t1_1 = tl2).
    apply IHt1_1 with (S d) ns;
    eapply is_prefix_Node; eauto.
  subst t1_1.
  f_equal.
  generalize (ofs_depths_1 d (Node tl2 t1_2)).
  rewrite Hofs1; intro H.
  inversion H; subst.
  apply IHt1_2 with (S d) (nsr ++ lsr1).
    exists nsr; exists lsr1.
    split.
      auto.
    apply ofs_depths_2; auto.
  generalize (ofs_depths_1 d (Node tl2 tr2)).
  rewrite Hofs2; intro H'.
  inversion H'; subst.
  injection Happ2; intros _ ?.
  subst.
  rewrite app_comm_cons in Happ2.
  rewrite app_comm_cons in Happ2.
  rewrite <-H5 in Happ2.
  rewrite <-H2 in Happ2.
  rewrite <-app_assoc in Happ2.
  rewrite <-app_assoc in Happ2.
  rewrite <-(ofs_depths_2 H6) in Happ2.
  rewrite <-(ofs_depths_2 H3) in Happ2.
  apply app_inv_head in Happ2.
  rewrite Happ2.
  exists nsr0; exists lsr2.
    split; auto.
    apply ofs_depths_2; auto.
Qed.

Definition has_prefix (d : nat) (ns : list nat) : Prop :=
  exists t, is_prefix d t ns.

Lemma not_prefix_1 :
  forall d n ns, n < d -> ~ has_prefix d (n :: ns).
Proof.
  intros d n ns H [t Hpr].
  destruct (is_prefix' Hpr) as [n' [lsl [lsr [Happ Heq]]]].
  injection Happ.
  intros _ Heq'.
  subst n'.
  clear Happ lsr ns Hpr; revert Heq.
  unfold ofs_depths.
  generalize (depths t).
  intro lsl'.
  destruct lsl' as [|n' lsl'].
  unfold incrl; simpl; congruence.
  unfold incrl; simpl; intro Heq.
  injection Heq.
  intros; omega.
Qed.

Lemma not_prefix_2 :
  forall d n ns, d < n ->
    ~has_prefix (S d) (n :: ns) -> ~has_prefix d (n :: ns).
Proof.
  intros d n ns H Hnot [t [lsl [lsr [Happ Heq]]]].
  apply Hnot; clear Hnot.
  generalize (ofs_depths_1 d t).
  rewrite Heq; clear Heq; intro Hofs.
  inversion Hofs.
    destruct lsl as [|n' lsl]; [congruence|].
    simpl in Happ; injection Happ.
    injection H1; intros; subst.
    exfalso; omega.
  exists tl.
  exists nsl.
  exists (nsr ++ lsr).
  split.
    rewrite Happ, <-H3, app_assoc.
    reflexivity.
  apply ofs_depths_2; auto.
Qed.

Lemma not_prefix_3 :
  forall d n ns tl lsl lsr, d < n -> n :: ns = lsl ++ lsr ->
    ofs_depths (S d) tl = lsl -> ~has_prefix (S d) lsr -> ~has_prefix d (n :: ns).
Proof.
  intros d n ns tl lsl lsr H Hofs Hls Hnot [t [lsl' [lsr' [Happ Heq]]]].
  apply Hnot; clear Hnot.
  generalize (ofs_depths_1 d t).
  rewrite Heq; clear Heq; intro Hofs'.
  inversion Hofs'.
    destruct lsl' as [|n' lsl']; [congruence|].
    simpl in Happ; injection Happ.
    injection H1; intros; subst.
    exfalso; omega.
  assert (Heq : tl = tl0).
    apply prefix_unique with (S d) (n :: ns).
      rewrite Hofs.
      exists lsl; exists lsr; split; auto.
    rewrite Happ.
    rewrite <-H3.
    rewrite <-app_assoc.
    exists nsl; exists (nsr ++ lsr'); split; auto.
    apply ofs_depths_2; auto.
  subst tl0.
  rewrite (ofs_depths_2 H0) in Hls.
  subst nsl.
  rewrite Hofs in Happ.
  rewrite <-H3 in Happ.
  rewrite <-app_assoc in Happ.
  apply app_inv_head in Happ.
  rewrite Happ.
  exists tr; exists nsr; exists lsr'; split; auto.
  apply ofs_depths_2; auto.
Qed.
