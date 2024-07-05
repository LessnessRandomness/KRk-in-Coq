Require Import Lia.
Require Import BasicDefinitions.
Set Implicit Arguments.

Ltac intuition' := intuition;
                   try (unfold NotKingNextToKing in *; simpl in *; lia);
                   try (unfold NotOnSameSquare in *; simpl in *; lia);
                   try (unfold BlackKingAttacked, Between in *; simpl in *; lia);
                   try (unfold MoveBlackKing in *; simpl in *; lia);
                   try (unfold OtherAfterMoveBlackKing in *; simpl in *; lia).

Ltac BK_move H N P x y :=
  try (
  assert (WKx P < N /\ WRx P < N /\ x < N /\ WKy P < N /\ WRy P < N /\ y < N) as DC
    by (abstract (destruct P; simpl in *; lia));
  refine (H (@Build_Position _ (WKx P) (WKy P) (WRx P) (WRy P) x y DC White) _);
  unfold LegalBlackMove, LegalPosition in *; intuition').

Ltac BK_moves H N P :=
  try (exfalso;
       try (BK_move H N P (BKx P + 1) (BKy P + 1); fail);
       try (BK_move H N P (BKx P + 1) (BKy P); fail);
       try (BK_move H N P (BKx P + 1) (BKy P - 1); fail);
       try (BK_move H N P (BKx P) (BKy P - 1); fail);
       try (BK_move H N P (BKx P - 1) (BKy P - 1); fail);
       try (BK_move H N P (BKx P - 1) (BKy P); fail);
       try (BK_move H N P (BKx P - 1) (BKy P + 1); fail);
       try (BK_move H N P (BKx P) (BKy P + 1); fail);
  fail).