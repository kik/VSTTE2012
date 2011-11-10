Require Import Ynot.
Local Open Scope hprop_scope.

Require Import List Arith Tree ImList.

Open Scope stsepi_scope.
Unset Automatic Introduction.

Definition build_rec (d : nat) (s : ImList.t nat) (ls : [list nat]) :
  STsep (ls ~~ ImList.rep s ls)
  (fun ot : option (Tree * [list nat]) => ls ~~
    match ot with
      | None =>
        Exists ls' :@ list nat,
        ImList.rep s ls' * [~has_prefix d ls]
      | Some (t, lsr) => lsr ~~
        Exists lsl :@ list nat,
        ImList.rep s lsr * [ofs_depths d t = lsl /\ ls = lsl ++ lsr]
    end).
Proof.
  Ltac t := sep idtac idtac.
  refine (Fix3 _ _ (fun build_rec d s ls =>
    ho <- ImList.head s ls;
    match ho with
      | None => {{Return None}}
      | Some h =>
        match lt_eq_lt_dec h d with
          | inleft (left _) => {{Return None}}
          | inleft (right _) =>
            ImList.pop s ls <@> (ls ~~ [ls = h :: tail ls]) ;;
            {{Return (Some (Leaf, ls ~~~ tail ls))}}
          | inright _ =>
            tlo <- build_rec (S d) s ls <@>
              (ls ~~ [ls = h :: tail ls]);
            match tlo with
              | None => {{Return None}}
              | Some (tl, ls') =>
                tro <- build_rec (S d) s ls' <@>
                  (ls ~~ ls' ~~ Exists lsl :@ list nat,
                    [ofs_depths (S d) tl = h :: lsl /\ ls = h :: lsl ++ ls']);
                match tro with
                  | None =>
                    {{Return None}}
                  | Some (tr, ls'') => {{Return (Some (Node tl tr, ls''))}}
                end
            end
        end
    end)).
  t.
  t.
  t.
  t.
  apply himp_pure'.
  apply not_prefix_1; auto.
  exfalso; omega.
  t.
  t.
  t.
  t.
  exfalso; omega.
  unfold ofs_depths, incrl; simpl; rewrite <-plus_n_O; t.
  t.
  t.
  t.
  apply himp_pure'.
  assert (Heq : ofs_depths (S d) tl = h :: tail (ofs_depths (S d) tl)).
  generalize (ofs_depths_cons (S d) tl).
  intros.
  destruct (ofs_depths (S d) tl) as [|h' lsl']; [congruence|].
  simpl in H; injection H; intros; subst; reflexivity.
  rewrite Heq.
  eauto.
  t.
  t.
  t.
  apply himp_pure'.
  rewrite app_comm_cons; rewrite <- H0.
  rewrite ofs_depths_Node_E.
  split; [reflexivity|].
  apply app_assoc.
  t.
  t.
  apply himp_pure'.
  eapply not_prefix_3; eauto.
  simpl; auto.
  t.
  t.
  apply himp_pure'.
  rewrite H1 in *.
  apply not_prefix_2; auto.
  t.
  t.
  apply himp_pure'.
  intros [t [lsl [lsr [Happ Heq]]]].
  apply eq_sym in Happ.
  apply app_eq_nil in Happ.
  destruct Happ.
  rewrite H in Heq.
  apply ofs_depths_cons in Heq.
  auto.
  Existential 1 := nil.
Qed.

Definition build (s : ImList.t nat) (ls : [list nat]) :
  STsep (ls ~~ ImList.rep s ls)
  (fun ot : option Tree => ls ~~
    match ot with
      | None =>
        Exists ls' :@ list nat,
          ImList.rep s ls' * [forall t, depths t <> ls]
      | Some t =>
        ImList.rep s nil * [depths t = ls]
    end).
Proof.
  intros.
  refine (to <- build_rec 0 s ls;
    match to with
      | None => {{Return None}}
      | Some (t, ls') =>
        ho <- ImList.head s ls' <@>
          (ls ~~ ls' ~~ Exists lsl :@ list nat, [ofs_depths 0 t = lsl /\ ls = lsl ++ ls']);
        match ho with
          | Some _ => {{Return None}}
          | None => {{Return (Some t)}}
        end
    end).
  t.
  t.
  t.
  t.
  t.
  t.
  apply himp_pure'.
  intros t' Heq.
  assert (depths t' = ofs_depths 0 t').
  rewrite <-(map_id (depths t')).
  unfold ofs_depths, incrl.
  apply map_ext; auto.
  rewrite H in Heq; clear H.
  assert (t = t').
  apply prefix_unique with 0 (ofs_depths 0 t').
    rewrite Heq.
    exists (ofs_depths 0 t); exists (n :: v1); auto.
  exists (ofs_depths 0 t'); exists nil.
  split; [rewrite app_nil_r|]; auto.
  subst.
  rewrite <-app_nil_r in Heq at 1.
  apply app_inv_head in Heq.
  congruence.
  t.
  t.
  apply himp_pure'.
  rewrite app_nil_r.
  unfold ofs_depths, incrl.
  rewrite <-(map_id (depths t)) at 1.
  apply map_ext; auto.
  t.
  t.
  apply himp_pure'.
  intros t Heq.
  apply H.
  exists t; exists x; exists nil.
  split.
    rewrite app_nil_r; auto.
  rewrite <- Heq.
  rewrite <-(map_id (depths t)).
  apply map_ext; auto.
Qed.
