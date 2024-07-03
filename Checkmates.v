Require Import Lia.
Require Import BasicDefinitions Symmetries Tactics.
Set Implicit Arguments.

Definition CheckmateType1 Nx Ny (P: Position Nx Ny) (Hx: 3 <= Nx) (Hy: 3 <= Ny) :=
  Turn P = Black /\
  ((BKx P = 0 /\ WKx P = 2 /\ BKy P = WKy P /\ WRx P = 0 /\ (BKy P + 2 <= WRy P \/ WRy P + 2 <= BKy P)) \/
   (BKy P = 0 /\ WKy P = 2 /\ BKx P = WKx P /\ WRy P = 0 /\ (BKx P + 2 <= WRx P \/ WRx P + 2 <= BKx P))).

Definition CheckmateType2 Nx Ny (P: Position Nx Ny) (Hx: 3 <= Nx) (Hy: 3 <= Ny) :=
  Turn P = Black /\ BKx P = 0 /\ BKy P = 0 /\
  (WKx P = 1 /\ WKy P = 2 /\ WRy P = 0 /\ 2 <= WRx P \/
   WKy P = 1 /\ WKx P = 2 /\ WRx P = 0 /\ 2 <= WRy P).

Theorem CheckmateAllTypes Nx Ny (P: Position Nx Ny) (Hx: 3 <= Nx) (Hy: 3 <= Ny):
  (BKx P <= Nx - 1 - BKx P /\ BKy P <= Ny - 1 - BKy P) ->
  (Mate P <-> (CheckmateType1 P Hx Hy \/ CheckmateType2 P Hx Hy)).
Proof.
  assert (Black = 1) by (unfold Black; auto). assert (White = 0) by (unfold White; auto).
  split; intros.
  + unfold Mate in *. unfold LegalPosition in *. intuition. 
    assert (BKx P = 0 \/ 1 <= BKx P) by lia. assert (BKy P = 0 \/ 1 <= BKy P) by lia. intuition.
    - assert (WKx P = 0 \/ WKx P = 1 \/ WKx P = 2 \/ 3 <= WKx P) by lia.
      assert (WKy P = 0 \/ WKy P = 1 \/ WKy P = 2 \/ 3 <= WKy P) by lia.
      assert (WRx P = 0 \/ WRx P = 1 \/ 2 <= WRx P) by lia.
      assert (WRy P = 0 \/ WRy P = 1 \/ 2 <= WRy P) by lia.
      intuition'; try (BK_moves H9 Nx Ny P).
      * left. unfold CheckmateType1. lia.
      * left. unfold CheckmateType1. lia.
      * right. unfold CheckmateType2. lia.
      * right. unfold CheckmateType2. lia.
    - assert (WKx P = 0 \/ WKx P = 1 \/ WKx P = 2 \/ 3 <= WKx P) by lia.
      assert (WKy P + 3 <= BKy P \/ WKy P + 2 = BKy P \/ WKy P + 1 = BKy P \/ WKy P = BKy P \/ BKy P + 1 = WKy P \/ BKy P + 2 = WKy P \/ BKy P + 3 <= WKy P) by lia.
      assert (WRx P = 0 \/ WRx P = 1 \/ 2 <= WRx P) by lia.
      assert (WRy P + 2 <= BKy P \/ WRy P + 1 = BKy P \/ WRy P = BKy P \/ BKy P + 1 = WRy P \/ BKy P + 2 <= WRy P) by lia.
      intuition'; try (BK_moves H9 Nx Ny P).
      * left. unfold CheckmateType1. lia.
      * left. unfold CheckmateType1. lia.
    - assert (WKy P = 0 \/ WKy P = 1 \/ WKy P = 2 \/ 3 <= WKy P) by lia.
      assert (WKx P + 3 <= BKx P \/ WKx P + 2 = BKx P \/ WKx P + 1 = BKx P \/ WKx P = BKx P \/ BKx P + 1 = WKx P \/ BKx P + 2 = WKx P \/ BKx P + 3 <= WKx P) by lia.
      assert (WRy P = 0 \/ WRy P = 1 \/ 2 <= WRy P) by lia.
      assert (WRx P + 2 <= BKx P \/ WRx P + 1 = BKx P \/ WRx P = BKx P \/ BKx P + 1 = WRx P \/ BKx P + 2 <= WRx P) by lia.
      intuition'; try (BK_moves H9 Nx Ny P).
      * left. unfold CheckmateType1. lia.
      * left. unfold CheckmateType1. lia.
    - assert (WKx P + 3 <= BKx P \/ WKx P + 2 = BKx P \/ WKx P + 1 = BKx P \/ WKx P = BKx P \/ BKx P + 1 = WKx P \/ BKx P + 2 = WKx P \/ BKx P + 3 <= WKx P) by lia.
      assert (WKy P + 3 <= BKy P \/ WKy P + 2 = BKy P \/ WKy P + 1 = BKy P \/ WKy P = BKy P \/ BKy P + 1 = WKy P \/ BKy P + 2 = WKy P \/ BKy P + 3 <= WKy P) by lia.
      assert (WRx P + 2 <= BKx P \/ WRx P + 1 = BKx P \/ WRx P = BKx P \/ BKx P + 1 = WRx P \/ BKx P + 2 <= WRx P) by lia.
      assert (WRy P + 2 <= BKy P \/ WRy P + 1 = BKy P \/ WRy P = BKy P \/ BKy P + 1 = WRy P \/ BKy P + 2 <= WRy P) by lia.
      intuition'; try (BK_moves H9 Nx Ny P).
  + unfold Mate. intuition.
    - unfold CheckmateType1, LegalPosition, NotOnSameSquare, NotKingNextToKing in *. lia.
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