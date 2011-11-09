Require Import Ynot.
Local Open Scope hprop_scope.

Require Import Arith Tree ImList.

Open Scope stsepi_scope.
Unset Automatic Introduction.

Definition build_rec (d : nat) (s : ImList.t nat) (ls : [list nat]) :
  STsep (ls ~~ ImList.rep s ls)
  (fun ot : option Tree =>
    match ot with
      | None => Exists ls' :@ list nat, ImList.rep s ls'
      | Some t => Exists ls' :@ list nat, ImList.rep s ls' * [True (* TODO *)]
    end).
Proof.
  refine (Fix3 _ _ (fun build_rec d s ls =>
    ho <- ImList.head s ls;
    match ho with
      | None => {{Return None}}
      | Some h =>
        match nat_compare h d with
          | Lt => {{Return None}}
          | Eq => ImList.pop s ls ;; {{Return (Some Leaf)}}
          | Gt =>
            lo <- build_rec (S d) s ls;
            match lo with
              | None => {{Return None}}
              | Some l =>
                ro <- build_rec (S d) s ls;
                match ro with
                  | None => {{Return None}}
                  | Some r => {{Return (Some (Node l r))}}
                end
            end
        end
    end));

  try sep idtac idtac.
  sep idtac idtac.
Qed.
