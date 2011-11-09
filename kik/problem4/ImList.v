Require Import Ynot.
Require Import List.
Local Open Scope hprop_scope.
Set Implicit Arguments.

Module Type IMLIST.
  Parameter t : Set -> Set.
  Parameter rep : forall T, t T -> list T -> hprop.

  Parameter new : forall T,
    STsep __ (fun s : t T => rep s nil).
  Parameter free : forall T (s : t T),
    STsep (rep s nil) (fun _ : unit => __).

  Parameter push : forall T (s : t T) (x : T) (ls : [list T]),
    STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls)).
  Parameter head : forall T (s : t T) (ls : [list T]),
    STsep (ls ~~ rep s ls)
    (fun xo : option T => ls ~~ rep s ls *
      match xo with
        | None => [ls = nil]
        | Some x => Exists ls' :@ list T, [ls = x :: ls']
      end).
  Parameter pop : forall T (s : t T) (ls : [list T]),
    STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (tail ls)).
End IMLIST.

Module ImList : IMLIST.
  Section ImList.
    Variable T : Set.

    Record node : Set := Node {
      data : T;
      next : option ptr
    }.

    Fixpoint listRep (ls : list T) (hd : option ptr) {struct ls} : hprop :=
      match ls with
        | nil => [hd = None]
        | h :: t => match hd with
                      | None => [False]
                      | Some hd' => Exists p :@ option ptr, hd' --> Node h p * listRep t p
                    end
      end.

    Definition imlist := ptr.

    Definition rep q ls := (Exists po :@ option ptr, q --> po * listRep ls po)%hprop.

    Ltac simplr := try discriminate.

    Theorem listRep_None : forall ls,
      listRep ls None ==> [ls = nil].
      destruct ls; sep fail idtac.
    Qed.

    Theorem listRep_Some : forall ls hd,
      listRep ls (Some hd) ==> Exists h :@ T, Exists t :@ list T, Exists p :@ option ptr,
        [ls = h :: t] * hd --> Node h p * listRep t p.
      destruct ls; sep fail ltac:(try discriminate).
    Qed.

    Ltac simp_prem :=
      simpl_IfNull;
      simpl_prem ltac:(apply listRep_None || apply listRep_Some).

    Ltac t := unfold rep; sep simp_prem simplr.
    
    Open Scope stsepi_scope.

    Definition new : STsep __ (fun s => rep s nil).
      refine {{New (@None ptr)}}; t.
    Qed.

    Definition free : forall s, STsep (rep s nil) (fun _ : unit => __).
      intros; refine {{Free s}}; t.
    Qed.

    Definition push : forall s x ls, STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (x :: ls)).
      intros; refine (hd <- !s;
        nd <- New (Node x hd);
        {{s ::= Some nd}}
      );
      t.
    Qed.

    Definition head : forall s ls,
      STsep (ls ~~ rep s ls)
      (fun xo => ls ~~ rep s ls *
        match xo with
          | None => [ls = nil]
          | Some x => Exists ls' :@ list T, [ls = x :: ls']
        end).
    intros; refine (hd <- !s;
      IfNull hd Then
        {{Return None}}
      Else
        nd <- !hd;
        {{Return (Some (data nd))}}); t.
    Qed.

    Definition pop : forall s ls,
      STsep (ls ~~ rep s ls) (fun _ : unit => ls ~~ rep s (tail ls)).
      intros; refine (hd <- !s;

        IfNull hd Then
          {{Return tt}}
        Else
          nd <- !hd;
          Free hd;;
          {{s ::= next nd}}); t.
    Qed.
  End ImList.

  Definition t (_ : Set) := imlist.
End ImList.




