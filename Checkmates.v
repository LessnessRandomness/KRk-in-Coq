Require Import Lia.
Require Import BasicDefinitions Symmetries Tactics.
Set Implicit Arguments.

Definition CheckmateType1 N (P: Position N) (Hn: 3 <= N) :=
  Turn P = Black /\ 1 <= BKx P <= N - 1 - BKx P /\ BKy P = 0 /\ WKy P = 2 /\ BKx P = WKx P /\ WRy P = 0 /\
  (BKx P + 2 <= WRx P \/ WRx P + 2 <= BKx P).

Definition CheckmateType2 N (P: Position N) (Hn: 3 <= N) :=
  Turn P = Black /\ BKx P = 0 /\ BKy P = 0 /\ WKy P <= 1 /\ WKx P = 2 /\ WRx P = 0 /\ 2 <= WRy P.

Theorem CheckmateAllTypes N (P: Position N) (Hn: 3 <= N):
  IsNormalized P ->
  (Checkmate P <-> (CheckmateType1 P Hn \/ CheckmateType2 P Hn)).
Proof.
  assert (Black = 1) by (unfold Black; auto). assert (White = 0) by (unfold White; auto).
  split; intros.
  + unfold Checkmate, LegalPosition in *.
    assert (BKx P = 0 \/ 1 <= BKx P) by lia. assert (BKy P = 0 \/ 1 <= BKy P) by lia. intuition.
    - unfold IsNormalized in *.
      assert (WKx P = 0 \/ WKx P = 1 \/ WKx P = 2 \/ 3 <= WKx P) by lia.
      assert (WKy P = 0 \/ WKy P = 1 \/ WKy P = 2 \/ 3 <= WKy P) by lia.
      assert (WRx P = 0 \/ WRx P = 1 \/ 2 <= WRx P) by lia.
      assert (WRy P = 0 \/ WRy P = 1 \/ 2 <= WRy P) by lia.
      intuition'; try (BK_moves H10 N P).
      * unfold CheckmateType2; lia.
      * unfold CheckmateType2; lia.
    - unfold IsNormalized in *. lia.
    - unfold IsNormalized in *.
      assert (WKy P = 0 \/ WKy P = 1 \/ WKy P = 2 \/ 3 <= WKy P) by lia.
      assert (WKx P + 3 <= BKx P \/ WKx P + 2 = BKx P \/ WKx P + 1 = BKx P \/ WKx P = BKx P \/ BKx P + 1 = WKx P \/ BKx P + 2 = WKx P \/ BKx P + 3 <= WKx P) by lia.
      assert (WRy P = 0 \/ WRy P = 1 \/ 2 <= WRy P) by lia.
      assert (WRx P + 2 <= BKx P \/ WRx P + 1 = BKx P \/ WRx P = BKx P \/ BKx P + 1 = WRx P \/ BKx P + 2 <= WRx P) by lia.
      intuition'; try (BK_moves H10 N P).
      * unfold CheckmateType1. lia.
      * unfold CheckmateType1. lia.
    - unfold IsNormalized in *.
      assert (WKx P + 3 <= BKx P \/ WKx P + 2 = BKx P \/ WKx P + 1 = BKx P \/ WKx P = BKx P \/ BKx P + 1 = WKx P \/ BKx P + 2 = WKx P \/ BKx P + 3 <= WKx P) by lia.
      assert (WKy P + 3 <= BKy P \/ WKy P + 2 = BKy P \/ WKy P + 1 = BKy P \/ WKy P = BKy P \/ BKy P + 1 = WKy P \/ BKy P + 2 = WKy P \/ BKy P + 3 <= WKy P) by lia.
      assert (WRx P + 2 <= BKx P \/ WRx P + 1 = BKx P \/ WRx P = BKx P \/ BKx P + 1 = WRx P \/ BKx P + 2 <= WRx P) by lia.
      assert (WRy P + 2 <= BKy P \/ WRy P + 1 = BKy P \/ WRy P = BKy P \/ BKy P + 1 = WRy P \/ BKy P + 2 <= WRy P) by lia.
      intuition'; try (BK_moves H10 N P).
  + unfold Checkmate. intuition.
    - unfold IsNormalized, CheckmateType1, LegalPosition, NotOnSameSquare, NotKingNextToKing in *. lia.
    - unfold CheckmateType1, BlackKingAttacked in *. lia.
    - unfold CheckmateType1 in *. lia.
    - unfold LegalBlackMove, LegalPosition, OtherAfterMoveBlackKing, CheckmateType1 in *.
      intuition; destruct P, P'; simpl in *; subst;
      unfold NotOnSameSquare, BlackKingAttacked, NotKingNextToKing, MoveBlackKing in *; simpl in *; lia.
    - unfold CheckmateType2, LegalPosition, NotOnSameSquare, NotKingNextToKing in *. lia.
    - unfold CheckmateType2, BlackKingAttacked in *. lia.
    - unfold CheckmateType2 in *. lia.
    - unfold LegalBlackMove, LegalPosition, OtherAfterMoveBlackKing, CheckmateType2 in *.
      intuition; destruct P, P'; simpl in *; subst;
      unfold NotOnSameSquare, BlackKingAttacked, NotKingNextToKing, MoveBlackKing in *; simpl in *; lia.
Qed.
