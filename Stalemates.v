Require Import Lia.
Require Import BasicDefinitions Symmetries Tactics.
Set Implicit Arguments.

Definition StalemateType1 Nx Ny (P: Position Nx Ny) (Hx: 3 <= Nx) (Hy: 3 <= Ny) :=
  Turn P = Black /\
  BKx P = 0 /\ BKy P = 0 /\ WRx P = 1 /\ WRy P = 1 /\
  (WKx P = 0 /\ WKy P = 2 \/ WKx P = 1 /\ WKy P = 2 \/ WKx P = 2 /\ WKy P = 2 \/
   WKx P = 2 /\ WKy P = 1 \/ WKx P = 2 /\ WKy P = 0).

Definition StalemateType2 Nx Ny (P: Position Nx Ny) (Hx: 3 <= Nx) (Hy: 3 <= Ny) :=
  Turn P = Black /\
  BKx P = 0 /\ BKy P = 0 /\
  (WKx P = 0 /\ WKy P = 2 /\ WRx P = 1 /\ 2 <= WRy P \/
   WKx P = 2 /\ WKy P = 0 /\ 2 <= WRx P /\ WRy P = 1).

Theorem StalemateAllTypes Nx Ny (P: Position Nx Ny) (Hx: 3 <= Nx) (Hy: 3 <= Ny):
  (BKx P <= Nx - 1 - BKx P /\ BKy P <= Ny - 1 - BKy P) ->
  (Stalemate P <-> (StalemateType1 P Hx Hy \/ StalemateType2 P Hx Hy)).
Proof.
  assert (Black = 1) by (unfold Black; auto). assert (White = 0) by (unfold White; auto).
  split; intros.
  + unfold Stalemate, LegalPosition in *; intuition. clear H8.
    assert (BKx P = 0 \/ 1 <= BKx P) by lia. assert (BKy P = 0 \/ 1 <= BKy P) by lia. intuition.
    - assert (WKx P = 0 \/ WKx P = 1 \/ WKx P = 2 \/ 3 <= WKx P) by lia.
      assert (WKy P = 0 \/ WKy P = 1 \/ WKy P = 2 \/ 3 <= WKy P) by lia.
      assert (WRx P = 0 \/ WRx P = 1 \/ 2 <= WRx P) by lia.
      assert (WRy P = 0 \/ WRy P = 1 \/ 2 <= WRy P) by lia.
      intuition'; try (BK_moves H9 Nx Ny P).
      * left. unfold StalemateType1. lia.
      * right. unfold StalemateType2. lia.
      * left. unfold StalemateType1. lia.
      * right. unfold StalemateType2. lia.
      * left. unfold StalemateType1. lia.
      * assert (WRy P = 2 \/ 3 <= WRy P) by lia. intuition'. BK_moves H9 Nx Ny P.
      * left. unfold StalemateType1. lia.
      * assert (WRx P = 2 \/ 3 <= WRx P) by lia. intuition'. BK_moves H9 Nx Ny P.
      * left. unfold StalemateType1. lia.
    - assert (WKx P = 0 \/ WKx P = 1 \/ WKx P = 2 \/ 3 <= WKx P) by lia.
      assert (WKy P + 3 <= BKy P \/ WKy P + 2 = BKy P \/ WKy P + 1 = BKy P \/ WKy P = BKy P \/ BKy P + 1 = WKy P \/ BKy P + 2 = WKy P \/ BKy P + 3 <= WKy P) by lia.
      assert (WRx P = 0 \/ WRx P = 1 \/ 2 <= WRx P) by lia.
      assert (WRy P + 2 <= BKy P \/ WRy P + 1 = BKy P \/ WRy P = BKy P \/ BKy P + 1 = WRy P \/ BKy P + 2 <= WRy P) by lia.
      intuition'; try (BK_moves H9 Nx Ny P).
    - assert (WKy P = 0 \/ WKy P = 1 \/ WKy P = 2 \/ 3 <= WKy P) by lia.
      assert (WKx P + 3 <= BKx P \/ WKx P + 2 = BKx P \/ WKx P + 1 = BKx P \/ WKx P = BKx P \/ BKx P + 1 = WKx P \/ BKx P + 2 = WKx P \/ BKx P + 3 <= WKx P) by lia.
      assert (WRy P = 0 \/ WRy P = 1 \/ 2 <= WRy P) by lia.
      assert (WRx P + 2 <= BKx P \/ WRx P + 1 = BKx P \/ WRx P = BKx P \/ BKx P + 1 = WRx P \/ BKx P + 2 <= WRx P) by lia.
      intuition'; try (BK_moves H9 Nx Ny P).
    - assert (WKx P + 3 <= BKx P \/ WKx P + 2 = BKx P \/ WKx P + 1 = BKx P \/ WKx P = BKx P \/ BKx P + 1 = WKx P \/ BKx P + 2 = WKx P \/ BKx P + 3 <= WKx P) by lia.
      assert (WKy P + 3 <= BKy P \/ WKy P + 2 = BKy P \/ WKy P + 1 = BKy P \/ WKy P = BKy P \/ BKy P + 1 = WKy P \/ BKy P + 2 = WKy P \/ BKy P + 3 <= WKy P) by lia.
      assert (WRx P + 2 <= BKx P \/ WRx P + 1 = BKx P \/ WRx P = BKx P \/ BKx P + 1 = WRx P \/ BKx P + 2 <= WRx P) by lia.
      assert (WRy P + 2 <= BKy P \/ WRy P + 1 = BKy P \/ WRy P = BKy P \/ BKy P + 1 = WRy P \/ BKy P + 2 <= WRy P) by lia.
      intuition'; try (BK_moves H9 Nx Ny P).
  + unfold Stalemate. intuition.
    - unfold StalemateType1, LegalPosition, NotOnSameSquare, NotKingNextToKing in *. lia.
    - unfold StalemateType1, BlackKingAttacked in *. lia.
    - unfold StalemateType1 in *. lia.
    - unfold LegalBlackMove, LegalPosition, OtherAfterMoveBlackKing, StalemateType1 in *.
      intuition; destruct P, P'; simpl in *; subst;
      unfold NotOnSameSquare, BlackKingAttacked, NotKingNextToKing, MoveBlackKing in *; simpl in *; lia.
    - unfold StalemateType2, LegalPosition, NotOnSameSquare, NotKingNextToKing in *. lia.
    - unfold StalemateType2, BlackKingAttacked in *. lia.
    - unfold StalemateType2 in *. lia.
    - unfold LegalBlackMove, LegalPosition, OtherAfterMoveBlackKing, StalemateType2 in *.
      intuition; destruct P, P'; simpl in *; subst;
      unfold NotOnSameSquare, BlackKingAttacked, NotKingNextToKing, MoveBlackKing in *; simpl in *; lia.
Qed.

(* Refactor parts related to symmetries into Symmetries.v *)
(* Also, is this theorem actually necessary? *)
(* Theorem StalemateThm' Nx Ny (P: Position Nx Ny) (Hx: 3 <= Nx) (Hy: 3 <= Ny):
  (exists P', RectangularSymmetric P P' /\ (StalemateType1 P' Hx Hy \/ StalemateType2 P' Hx Hy)) <->
  Stalemate P.
Proof.
  intuition.
  + destruct H as [P' H]. intuition.
    - unfold RectangularSymmetric in *. intuition.
      * unfold SamePosition in *; intuition. rewrite (StalemateAllTypes P Hx Hy).
        ++ left; destruct P, P'; simpl in *; subst. auto.
        ++ unfold StalemateType1 in *. lia.
      * rewrite StalemateAfterMirrorX. unfold SamePosition in *. rewrite (StalemateAllTypes (MirrorX P) Hx Hy).
        ++ left; destruct P, P'; simpl in *; unfold StalemateType1 in *; simpl in *; intuition; subst; lia.
        ++ unfold StalemateType1, MirrorX in *. destruct P, P'; simpl in *; intuition; subst; lia.
      * rewrite StalemateAfterMirrorY. unfold SamePosition in *. rewrite (StalemateAllTypes (MirrorY P) Hx Hy).
        ++ left; destruct P, P'; simpl in *; unfold StalemateType1 in *; simpl in *; intuition; subst; lia.
        ++ unfold StalemateType1, MirrorY in *. destruct P, P'; simpl in *; intuition; subst; lia.
      * rewrite StalemateAfterMirrorX, StalemateAfterMirrorY. unfold SamePosition in *. rewrite (StalemateAllTypes _ Hx Hy).
        ++ left; destruct P, P'; simpl in *; unfold StalemateType1 in *; simpl in *; intuition; subst; lia.
        ++ unfold StalemateType1, MirrorY, MirrorX in *. destruct P, P'; simpl in *; intuition; subst; lia.
    - unfold RectangularSymmetric in *. intuition.
      * unfold SamePosition in *; intuition. rewrite (StalemateAllTypes P Hx Hy).
        ++ right; destruct P, P'; simpl in *; subst. auto.
        ++ unfold StalemateType2 in *. lia.
      * rewrite StalemateAfterMirrorX. unfold SamePosition in *. rewrite (StalemateAllTypes (MirrorX P) Hx Hy).
        ++ right; destruct P, P'; simpl in *; unfold StalemateType2 in *; simpl in *; intuition; subst; lia.
        ++ unfold StalemateType2, MirrorX in *. destruct P, P'; simpl in *; intuition; subst; lia.
      * rewrite StalemateAfterMirrorY. unfold SamePosition in *. rewrite (StalemateAllTypes (MirrorY P) Hx Hy).
        ++ right; destruct P, P'; simpl in *; unfold StalemateType2 in *; simpl in *; intuition; subst; lia.
        ++ unfold StalemateType2, MirrorY in *. destruct P, P'; simpl in *; intuition; subst; lia.
      * rewrite StalemateAfterMirrorX, StalemateAfterMirrorY. unfold SamePosition in *. rewrite (StalemateAllTypes _ Hx Hy).
        ++ right; destruct P, P'; simpl in *; unfold StalemateType2 in *; simpl in *; intuition; subst; lia.
        ++ unfold StalemateType2, MirrorY, MirrorX in *. destruct P, P'; simpl in *; intuition; subst; lia.
  + assert (BKx P <= Nx - 1 - BKx P \/ ~ (BKx P <= Nx - 1 - BKx P)) by lia.
    assert (BKy P <= Ny - 1 - BKy P \/ ~ (BKy P <= Ny - 1 - BKy P)) by lia.
    intuition.
    - exists P. rewrite (StalemateAllTypes P Hx Hy) in H; auto. split; auto.
      unfold RectangularSymmetric. left. unfold SamePosition. tauto.
    - exists (MirrorY P). rewrite (StalemateAfterMirrorY P) in H. split.
      * unfold RectangularSymmetric. right; right; left. unfold SamePosition, MirrorY. destruct P; simpl in *. lia.
      * apply StalemateAllTypes; auto. unfold MirrorY; simpl in *. lia.
    - exists (MirrorX P). rewrite (StalemateAfterMirrorX P) in H. split.
      * unfold RectangularSymmetric. right; left. unfold SamePosition, MirrorX. destruct P; simpl in *. lia.
      * apply StalemateAllTypes; auto. unfold MirrorX; simpl in *. lia.
    - exists (MirrorY (MirrorX P)). rewrite (StalemateAfterMirrorX P), (StalemateAfterMirrorY _) in H. split.
      * unfold RectangularSymmetric. right; right; right. unfold SamePosition, MirrorY, MirrorX. destruct P; simpl in *. clear H. intuition; lia.
      * apply StalemateAllTypes; auto. unfold MirrorX, MirrorY; simpl in *. lia.
Qed. *)

Definition StalemateThm2 Nx Ny (P: Position Nx Ny) (Hx: 3 <= Nx) (Hy: 3 <= Ny):
  Stalemate P <-> (StalemateType1 (Normalize P) Hx Hy \/ StalemateType2 (Normalize P) Hx Hy).
Proof.
  intuition; unfold Normalize in *; repeat destruct Compare_dec.le_lt_dec.
  + apply StalemateAllTypes; auto.
  + rewrite StalemateAfterMirrorY in H. apply StalemateAllTypes; auto. unfold MirrorY; simpl. lia.
  + apply StalemateAllTypes.
    - unfold MirrorX; simpl. lia.
    - rewrite <- StalemateAfterMirrorX; auto.
  + rewrite StalemateAfterMirrorX, StalemateAfterMirrorY in H. apply StalemateAllTypes; auto. unfold MirrorY, MirrorX; simpl. lia.
  + rewrite (StalemateAllTypes P Hx Hy); auto.
  + rewrite StalemateAfterMirrorY. rewrite (StalemateAllTypes _ Hx Hy); auto. unfold MirrorY; simpl. lia.
  + rewrite StalemateAfterMirrorX. rewrite (StalemateAllTypes _ Hx Hy); auto. unfold MirrorX; simpl. lia.
  + rewrite StalemateAfterMirrorX, StalemateAfterMirrorY. rewrite (StalemateAllTypes _ Hx Hy); auto. unfold MirrorX, MirrorY; simpl. lia.
  + rewrite (StalemateAllTypes P Hx Hy); auto.
  + rewrite StalemateAfterMirrorY. rewrite (StalemateAllTypes _ Hx Hy); auto. unfold MirrorY; simpl. lia.
  + rewrite StalemateAfterMirrorX. rewrite (StalemateAllTypes _ Hx Hy); auto. unfold MirrorX; simpl. lia.
  + rewrite StalemateAfterMirrorX, StalemateAfterMirrorY. rewrite (StalemateAllTypes _ Hx Hy); auto. unfold MirrorX, MirrorY; simpl. lia.
Qed.

