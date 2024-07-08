Require Import Lia.
Require Import BasicDefinitions Symmetries Tactics Checkmates.
Set Implicit Arguments.


Definition CheckmatePly001_Type1 N (P: Position N) (Hn: 3 <= N) :=
  Turn P = White /\ 1 <= BKx P <= N - 1 - BKx P /\ BKy P = 0 /\ WKy P = 2 /\ BKx P = WKx P /\ 1 <= WRy P /\
  (BKx P + 2 <= WRx P \/ WRx P + 2 <= BKx P).

Definition CheckmatePly001_Type2 N (P: Position N) (Hn: 3 <= N) :=
  Turn P = White /\ BKx P = 0 /\ BKy P = 0 /\ WKy P <= 1 /\ WKx P = 2 /\ 1 <= WRx P /\ 2 <= WRy P.

Ltac smart_destruct H :=
  match type of H with
  | _ /\ _ => 
    let L := fresh "L" in
    let R := fresh "R" in
    destruct H as [L R]; smart_destruct L; smart_destruct R
  | _ => idtac
  end.

Theorem CheckmatePly001_AllTypes N (P: Position N) (Hn: 3 <= N):
  IsNormalized P ->
  (WhiteWin P 1 <-> (CheckmatePly001_Type1 P Hn \/ CheckmatePly001_Type2 P Hn)).
Proof.
  assert (Black = 1) by (unfold Black; auto). assert (White = 0) by (unfold White; auto).
  intuition.
  + inversion H2; subst; clear H2. destruct H4 as [P' H5]. destruct H5. inversion H3; subst; clear H3.
    rewrite (@CheckmateAllTypes N P' Hn) in *.
    - destruct H4; [left | right].
      * destruct H2.
        ++ unfold LegalMoveWhiteKing in *. unfold OtherAfterMoveWhiteKing in *. unfold CheckmateType1 in *.
           unfold LegalPosition in *. unfold BlackKingAttacked in *. unfold MoveWhiteKing in *.
           destruct P, P'; simpl in *; intuition; subst; lia.
        ++ unfold CheckmateType1, CheckmatePly001_Type1 in *. unfold InsufficientMaterial in *. unfold LegalMoveWhiteRook in *.
           unfold LegalPosition in *. unfold OtherAfterMoveWhiteRook in *. unfold MoveWhiteRook in *. unfold BlackKingAttacked in *.
           destruct P, P'; simpl in *; intuition; subst; lia.
      * destruct H2.
        ++ unfold LegalMoveWhiteKing in *. unfold OtherAfterMoveWhiteKing in *. unfold CheckmateType2 in *.
           unfold LegalPosition in *. unfold BlackKingAttacked in *. unfold MoveWhiteKing in *.
           destruct P, P'; simpl in *; intuition; subst; lia.
        ++ unfold CheckmateType2, CheckmatePly001_Type2 in *. unfold InsufficientMaterial in *. unfold LegalMoveWhiteRook in *.
           unfold LegalPosition in *. unfold OtherAfterMoveWhiteRook in *. unfold MoveWhiteRook in *. unfold BlackKingAttacked in *.
           destruct P, P'; simpl in *; intuition; subst; lia.
    - unfold IsNormalized in *. destruct H2.
      * intuition.
        ++ unfold LegalMoveWhiteKing in *. unfold MoveWhiteKing, OtherAfterMoveWhiteKing in *. lia.
        ++ unfold LegalMoveWhiteKing in *. unfold MoveWhiteKing, OtherAfterMoveWhiteKing in *. lia.
        ++ unfold LegalMoveWhiteKing in *. unfold MoveWhiteKing, OtherAfterMoveWhiteKing in *. lia.
        ++ unfold LegalMoveWhiteKing in *. unfold MoveWhiteKing, OtherAfterMoveWhiteKing in *. lia.
        ++ unfold LegalMoveWhiteKing in *. unfold MoveWhiteKing, OtherAfterMoveWhiteKing in *. lia.
        ++ unfold LegalMoveWhiteKing in *. unfold MoveWhiteKing, OtherAfterMoveWhiteKing in *.
           unfold Checkmate, LegalPosition in *. unfold BlackKingAttacked in *.
Admitted.