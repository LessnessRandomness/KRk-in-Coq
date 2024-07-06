Require Import Lia.
Require Import BasicDefinitions Symmetries Tactics.
Set Implicit Arguments.

Definition StalemateType1 N (P: Position N) (Hn: 3 <= N) :=
  Turn P = Black /\
  BKx P = 0 /\ BKy P = 0 /\ WRx P = 1 /\ WRy P = 1 /\
  (WKx P = 2 /\ WKy P = 2 \/ WKx P = 2 /\ WKy P = 1 \/ WKx P = 2 /\ WKy P = 0).

Definition StalemateType2 N (P: Position N) (Hn: 3 <= N) :=
  Turn P = Black /\
  BKx P = 0 /\ BKy P = 0 /\
  WKx P = 2 /\ WKy P = 0 /\ 2 <= WRx P /\ WRy P = 1.




Theorem StalemateAllTypes N (P: Position N) (Hn: 3 <= N):
  IsNormalized P ->
  (Stalemate P <-> (StalemateType1 P Hn \/ StalemateType2 P Hn)).
Proof.
  assert (Black = 1) by (unfold Black; auto). assert (White = 0) by (unfold White; auto). split; intros.
  + unfold Stalemate, LegalPosition in *. intuition. clear H7 H6.
    assert (BKx P = 0 \/ 1 <= BKx P) by lia. assert (BKy P = 0 \/ 1 <= BKy P) by lia. intuition.
    - assert (WKx P = 2 /\ (WKy P = 0 \/ WKy P = 1 \/ WKy P = 2) \/ 3 <= WKx P).
      { unfold NotKingNextToKing, IsNormalized in *. lia. }
      intuition.
      * assert (WRy P = 0 /\ 3 <= WRx P \/ WRy P = 1 /\ 1 <= WRx P \/ 2 <= WRy P /\ 1 <= WRx P).
        { unfold BlackKingAttacked, Between, NotOnSameSquare in *. lia. }
        intuition.
        ++ exfalso. BK_move H8 N P 0 1.
        ++ unfold StalemateType1, StalemateType2. lia.
        ++ exfalso. BK_move H8 N P 0 1.
      * assert (WRy P = 1 /\ (WRx P = 1 \/ 3 <= WRx P) \/ 2 <= WRy P /\ 1 <= WRx P).
        { unfold BlackKingAttacked, Between, NotOnSameSquare in *. lia. }
        intuition.
        ++ unfold StalemateType1. lia.
        ++ exfalso. BK_move H8 N P 0 1.
        ++ exfalso. BK_move H8 N P 0 1.
      * assert (WRy P = 1 /\ (WRx P = 1 \/ 2 <= WRx P) \/ WRy P = 2 /\ (WRx P = 1 \/ 3 <= WRx P) \/ 3 <= WRy P /\ 1 <= WRx P).
        { unfold BlackKingAttacked, NotOnSameSquare in *. lia. }
        intuition.
        ++ unfold StalemateType1. lia.
        ++ exfalso. BK_move H8 N P 1 0.
        ++ exfalso. BK_move H8 N P 0 1.
        ++ exfalso. BK_move H8 N P 0 1.
        ++ exfalso. BK_move H8 N P 0 1.
      * assert ((WRx P = 1 \/ WRx P = 2) /\ (WRy P = 1 \/ 2 <= WRy P) \/ 3 <= WRx P).
        { unfold BlackKingAttacked, Between, NotOnSameSquare in *. lia. }
        intuition.
        ++ exfalso. BK_move H8 N P 1 1.
        ++ exfalso. BK_move H8 N P 0 1.
        ++ exfalso. BK_move H8 N P 1 0.
        ++ exfalso. BK_move H8 N P 1 0.
        ++ exfalso. BK_move H8 N P 1 0.
    - unfold IsNormalized in H1; intuition'.
    - exfalso. unfold IsNormalized in *. destruct H1 as [H1 [H10 _]].
      assert (WKx P + 3 <= BKx P \/ WKx P + 2 = BKx P \/ WKx P + 1 = BKx P \/ WKx P = BKx P \/ BKx P + 1 = WKx P \/ BKx P + 2 = WKx P \/ BKx P + 3 <= WKx P) by lia.
      assert (WKy P = 0 \/ WKy P = 1 \/ WKy P = 2 \/ 3 <= WKy P) by lia.
      assert (WRx P + 2 <= BKx P \/ WRx P + 1 = BKx P \/ WRx P = BKx P \/ BKx P + 1 = WRx P \/ BKx P + 2 <= WRx P) by lia.
      assert (WRy P = 0 \/ WRy P = 1 \/ 2 <= WRy P) by lia.
      intuition'; BK_moves H8 N P.
    - exfalso. unfold IsNormalized in *. destruct H1 as [H1 [H10 _]].
      assert (WKx P + 3 <= BKx P \/ WKx P + 2 = BKx P \/ WKx P + 1 = BKx P \/ WKx P = BKx P \/ BKx P + 1 = WKx P \/ BKx P + 2 = WKx P \/ BKx P + 3 <= WKx P) by lia.
      assert (WKy P + 3 <= BKy P \/ WKy P + 2 = BKy P \/ WKy P + 1 = BKy P \/ WKy P = BKy P \/ BKy P + 1 = WKy P \/ BKy P + 2 = WKy P \/ BKy P + 3 <= WKy P) by lia.
      assert (WRx P + 2 <= BKx P \/ WRx P + 1 = BKx P \/ WRx P = BKx P \/ BKx P + 1 = WRx P \/ BKx P + 2 <= WRx P) by lia.
      assert (WRy P + 2 <= BKy P \/ WRy P + 1 = BKy P \/ WRy P = BKy P \/ BKy P + 1 = WRy P \/ BKy P + 2 <= WRy P) by lia.
      intuition'; BK_moves H8 N P.
  + unfold Stalemate. intuition.
    - unfold StalemateType1, LegalPosition, NotOnSameSquare, NotKingNextToKing in *. lia.
    - unfold StalemateType1, BlackKingAttacked in *. lia.
    - unfold StalemateType1 in *. lia.
    - unfold LegalBlackMove, LegalPosition, OtherAfterMoveBlackKing, StalemateType1 in *.
      intuition; destruct P, P'; simpl in *; subst;
      unfold NotOnSameSquare, BlackKingAttacked, Between, NotKingNextToKing, MoveBlackKing in *; simpl in *; lia.
    - unfold StalemateType2, LegalPosition, NotOnSameSquare, NotKingNextToKing in *. lia.
    - unfold StalemateType2, BlackKingAttacked in *. lia.
    - unfold StalemateType2 in *. lia.
    - unfold LegalBlackMove, LegalPosition, OtherAfterMoveBlackKing, StalemateType2 in *.
      intuition; destruct P, P'; simpl in *; subst;
      unfold NotOnSameSquare, BlackKingAttacked, NotKingNextToKing, MoveBlackKing in *; simpl in *; lia.
Qed.

