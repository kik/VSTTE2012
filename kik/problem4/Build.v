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
        ImList.rep s ls' * [forall t lsl lsr, ls = lsl ++ lsr -> ofs_depths d t <> lsl]
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
            tlo <- build_rec (S d) s ls;
            match tlo with
              | None => {{Return None}}
              | Some (tl, ls') =>
                tro <- build_rec (S d) s ls' <@>
                  (ls ~~ ls' ~~ Exists lsl :@ list nat, [ofs_depths (S d) tl = lsl /\ ls = lsl ++ ls']);
                match tro with
                  | None => {{Return None}}
                  | Some (tr, ls'') => {{Return (Some (Node tl tr, ls''))}}
                end
            end
        end
    end)).
  t.
  t.
  t.
  t.
  admit.
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
  t.
  t.
  t.
  rewrite ofs_depths_Node_E.
  t.
  t.
  t.
  admit.
  t.
  t.
  admit.
  t.
  t.
  admit.
  Existential 1 := nil.
Qed.

Definition build (s : ImList.t nat) (ls : [list nat]) :
  STsep (ls ~~ ImList.rep s ls)
  (fun ot : option Tree => ls ~~
    match ot with
      | None => Exists ls' :@ list nat, ImList.rep s ls'
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
  t.
  t.
  apply himp_pure'.
  rewrite app_nil_r.
  unfold ofs_depths, incrl.
  rewrite <-(map_id (depths t)) at 1.
  apply map_ext; auto.
  t.
  t.
Qed.
