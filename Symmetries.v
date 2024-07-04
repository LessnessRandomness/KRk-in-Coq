Require Import Lia.
Require Import BasicDefinitions.
Set Implicit Arguments.

Definition MirrorX N (P: Position N): Position N.
Proof.
  refine (@Build_Position N (N - 1 - WKx P) (WKy P) (N - 1 - WRx P) (WRy P) (N - 1 - BKx P) (BKy P) _ (Turn P)).
  destruct P; simpl in *. abstract lia.
Defined.

Definition MirrorY N (P: Position N): Position N.
Proof.
  refine (@Build_Position N (WKx P) (N - 1 - WKy P) (WRx P) (N - 1 - WRy P) (BKx P) (N - 1 - BKy P) _ (Turn P)).
  destruct P; simpl in *. abstract lia.
Defined.

Definition SwapXY N (P: Position N): Position N.
Proof.
  refine (@Build_Position N (WKy P) (WKx P) (WRy P) (WRx P) (BKy P) (BKx P) _ (Turn P)).
  destruct P; simpl in *. abstract intuition.
Defined.

Definition Symmetric N (P1 P2: Position N) :=
  SamePosition P1 P2 \/ SamePosition P1 (MirrorX P2) \/ SamePosition P1 (MirrorY P2) \/ SamePosition P1 (MirrorY (MirrorX P2)) \/
  SamePosition P1 (SwapXY P2) \/ SamePosition P1 (SwapXY (MirrorX P2)) \/
  SamePosition P1 (SwapXY (MirrorY P2)) \/ SamePosition P1 (SwapXY (MirrorY (MirrorX P2))).

(* MirrorX *)

Theorem LegalPositionAfterMirrorX N (P: Position N):
  LegalPosition P <-> LegalPosition (MirrorX P).
Proof.
  unfold LegalPosition, MirrorX; simpl in *. intuition.
  + clear H H1 H2. unfold NotOnSameSquare in *; destruct P; simpl in *. lia.
  + clear H0 H1 H2. unfold NotKingNextToKing in *; destruct P; simpl in *. lia.
  + subst. apply H2; auto. clear H H0 H1 H2. unfold BlackKingAttacked, Between in *; destruct P; simpl in *. lia.
  + clear H H1 H2. unfold NotOnSameSquare in *; simpl in *. lia.
  + clear H2 H1 H0. unfold NotKingNextToKing in *; simpl in *. lia.
  + apply H2; auto. subst. clear H H0 H1 H2. unfold BlackKingAttacked, Between in *; destruct P; simpl in *. lia.
Qed.

Theorem CheckmateAfterMirrorX N (P: Position N):
  Checkmate P <-> Checkmate (MirrorX P).
Proof.
  unfold Checkmate; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + clear H0 H3. unfold BlackKingAttacked, Between, MirrorX in *; destruct P; simpl in *. lia.
  + apply (H3 (MirrorX P')). clear H H3 H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. clear H0 H3. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. clear H0 H3. lia.
    - apply LegalPositionAfterMirrorX; auto.
    - rewrite <- LegalPositionAfterMirrorX; auto.
  + apply LegalPositionAfterMirrorX; auto.
  + clear H0 H3. unfold BlackKingAttacked, Between, MirrorX in *; destruct P; simpl in *. clear H1. lia.
  + apply (H3 (MirrorX P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6 H0 H3. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6 H0 H3. unfold OtherAfterMoveBlackKing in *; simpl in *. destruct P, P'; simpl in *.
      intuition; subst; auto.
    - rewrite <- LegalPositionAfterMirrorX; auto.
    - rewrite <- LegalPositionAfterMirrorX; auto.
Qed.

Theorem StalemateAfterMirrorX N (P: Position N):
  Stalemate P <-> Stalemate (MirrorX P).
Proof.
  unfold Stalemate; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + clear H0 H1 H3. apply H; clear H. unfold BlackKingAttacked, Between in *; simpl in *.
    destruct P; simpl in *. lia.
  + apply (H3 (MirrorX P')). clear H H0 H1 H3. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H0 H1 H2 H3 H5. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H H0 H2 H3 H5. unfold OtherAfterMoveBlackKing in *; destruct P, P'; simpl in *. lia.
    - apply LegalPositionAfterMirrorX; auto.
    - rewrite <- LegalPositionAfterMirrorX; auto.
  + apply LegalPositionAfterMirrorX; auto.
  + clear H0 H1 H3. apply H; clear H. unfold BlackKingAttacked, Between in *; destruct P; simpl in *. lia.
  + apply (H3 (MirrorX P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H0 H1 H2 H3 H4 H6. unfold MoveBlackKing in *; destruct P, P'; simpl in *. lia.
    - clear H H0 H1 H3 H4 H6. unfold OtherAfterMoveBlackKing in *; destruct P, P'; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorX; auto.
    - rewrite <- LegalPositionAfterMirrorX; auto.
Qed.

Theorem InsufficientMaterialAfterMirrorX N (P: Position N):
  InsufficientMaterial P <-> InsufficientMaterial (MirrorX P).
Proof.
  unfold InsufficientMaterial; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + rewrite LegalPositionAfterMirrorX. auto.
  + clear H H0 H3. destruct P; simpl in *. lia.
Qed.

Theorem WhiteMoveAndMirrorX N (P P': Position N):
  LegalWhiteMove P P' <-> LegalWhiteMove (MirrorX P) (MirrorX P').
Proof.
  unfold LegalWhiteMove, LegalMoveWhiteKing, LegalMoveWhiteRook; simpl. intuition.
  + left. intuition.
    - clear H3 H5 H0 H1 H2. unfold MoveWhiteKing in *; destruct P, P'; simpl in *. lia.
    - clear H3 H5 H H1 H2. unfold OtherAfterMoveWhiteKing in *; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorX. auto.
    - rewrite <- LegalPositionAfterMirrorX. auto.
  + right. intuition.
    - clear H0 H3 H5 H1 H2. unfold MoveWhiteRook, Between in *; simpl in *.
      destruct P, P'; simpl in *. destruct H; [left | right]; intuition; subst; lia.
    - clear H H3 H5 H1 H2. unfold OtherAfterMoveWhiteRook in *; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorX. auto.
    - rewrite <- LegalPositionAfterMirrorX. auto.
  + left. intuition.
    - clear H0 H3 H5 H1 H2. unfold MoveWhiteKing in *; destruct P, P'; simpl in *. lia.
    - clear H H3 H5 H1 H2. unfold OtherAfterMoveWhiteKing in *; destruct P, P'; simpl in *. lia.
    - rewrite LegalPositionAfterMirrorX; auto.
    - rewrite LegalPositionAfterMirrorX; auto.
  + right. intuition.
    - clear H0 H3 H5 H1 H2. unfold MoveWhiteRook, Between in *; simpl in *.
      destruct P, P'; simpl in *. destruct H; [left | right]; intuition; subst; lia.
    - clear H H3 H5 H1 H2. unfold OtherAfterMoveWhiteRook in *; destruct P, P'; simpl in *. lia.
    - rewrite LegalPositionAfterMirrorX; auto.
    - rewrite LegalPositionAfterMirrorX; auto.
Qed.

Theorem BlackMoveAndMirrorX N (P P': Position N):
  LegalBlackMove P P' <-> LegalBlackMove (MirrorX P) (MirrorX P').
Proof.
  unfold LegalBlackMove; simpl. intuition.
  + clear H H3 H5 H1 H2. unfold MoveBlackKing in *; destruct P, P'; simpl in *. lia.
  + clear H0 H3 H5 H1 H2. unfold OtherAfterMoveBlackKing in *; simpl in *. lia.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + clear H H3 H5 H1 H2. unfold MoveBlackKing in *; destruct P, P'; simpl in *. lia.
  + clear H0 H3 H5 H1 H2. unfold OtherAfterMoveBlackKing in *; destruct P, P'; simpl in *. lia.
  + rewrite LegalPositionAfterMirrorX; auto.
  + rewrite LegalPositionAfterMirrorX; auto.
Qed.

(* MirrorY *)

Theorem LegalPositionAfterMirrorY N (P: Position N):
  LegalPosition P <-> LegalPosition (MirrorY P).
Proof.
  unfold LegalPosition, MirrorY; simpl in *. intuition.
  + clear H H1 H2. unfold NotOnSameSquare in *; destruct P; simpl in *. lia.
  + clear H0 H1 H2. unfold NotKingNextToKing in *; destruct P; simpl in *. lia.
  + subst. apply H2; auto. clear H H0 H1 H2. unfold BlackKingAttacked, Between in *; destruct P; simpl in *. lia.
  + clear H H1 H2. unfold NotOnSameSquare in *; simpl in *. lia.
  + clear H2 H1 H0. unfold NotKingNextToKing in *; simpl in *. lia.
  + apply H2; auto. subst. clear H H0 H1 H2. unfold BlackKingAttacked, Between in *; destruct P; simpl in *. lia.
Qed.

Theorem CheckmateAfterMirrorY N (P: Position N):
  Checkmate P <-> Checkmate (MirrorY P).
Proof.
  unfold Checkmate; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + clear H0 H3. unfold BlackKingAttacked, Between, MirrorY in *; destruct P; simpl in *. lia.
  + apply (H3 (MirrorY P')). clear H H3 H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. clear H0 H3. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. clear H0 H3. lia.
    - apply LegalPositionAfterMirrorY; auto.
    - rewrite <- LegalPositionAfterMirrorY; auto.
  + apply LegalPositionAfterMirrorY; auto.
  + clear H0 H3. unfold BlackKingAttacked, Between, MirrorY in *; destruct P; simpl in *. clear H1. lia.
  + apply (H3 (MirrorY P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6 H0 H3. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6 H0 H3. unfold OtherAfterMoveBlackKing in *; simpl in *. destruct P, P'; simpl in *.
      intuition; subst; auto.
    - rewrite <- LegalPositionAfterMirrorY; auto.
    - rewrite <- LegalPositionAfterMirrorY; auto.
Qed.

Theorem StalemateAfterMirrorY N (P: Position N):
  Stalemate P <-> Stalemate (MirrorY P).
Proof.
  unfold Stalemate; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + clear H0 H1 H3. apply H; clear H. unfold BlackKingAttacked, Between in *; simpl in *.
    destruct P; simpl in *. lia.
  + apply (H3 (MirrorY P')). clear H H0 H1 H3. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H0 H1 H2 H3 H5. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H H0 H2 H3 H5. unfold OtherAfterMoveBlackKing in *; destruct P, P'; simpl in *. lia.
    - apply LegalPositionAfterMirrorY; auto.
    - rewrite <- LegalPositionAfterMirrorY; auto.
  + apply LegalPositionAfterMirrorY; auto.
  + clear H0 H1 H3. apply H; clear H. unfold BlackKingAttacked, Between in *; destruct P; simpl in *. lia.
  + apply (H3 (MirrorY P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H0 H1 H2 H3 H4 H6. unfold MoveBlackKing in *; destruct P, P'; simpl in *. lia.
    - clear H H0 H1 H3 H4 H6. unfold OtherAfterMoveBlackKing in *; destruct P, P'; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorY; auto.
    - rewrite <- LegalPositionAfterMirrorY; auto.
Qed.

Theorem InsufficientMaterialAfterMirrorY N (P: Position N):
  InsufficientMaterial P <-> InsufficientMaterial (MirrorY P).
Proof.
  unfold InsufficientMaterial; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + rewrite LegalPositionAfterMirrorY. auto.
  + clear H H0 H1. destruct P; simpl in *. lia.
Qed.

Theorem WhiteMoveAndMirrorY N (P P': Position N):
  LegalWhiteMove P P' <-> LegalWhiteMove (MirrorY P) (MirrorY P').
Proof.
  unfold LegalWhiteMove, LegalMoveWhiteKing, LegalMoveWhiteRook; simpl. intuition.
  + left. intuition.
    - clear H3 H5 H0 H1 H2. unfold MoveWhiteKing in *; destruct P, P'; simpl in *. lia.
    - clear H3 H5 H H1 H2. unfold OtherAfterMoveWhiteKing in *; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorY. auto.
    - rewrite <- LegalPositionAfterMirrorY. auto.
  + right. intuition.
    - clear H0 H3 H5 H1 H2. unfold MoveWhiteRook, Between in *; simpl in *.
      destruct P, P'; simpl in *. destruct H; [left | right]; intuition; subst; lia.
    - clear H H3 H5 H1 H2. unfold OtherAfterMoveWhiteRook in *; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorY. auto.
    - rewrite <- LegalPositionAfterMirrorY. auto.
  + left. intuition.
    - clear H0 H3 H5 H1 H2. unfold MoveWhiteKing in *; destruct P, P'; simpl in *. lia.
    - clear H H3 H5 H1 H2. unfold OtherAfterMoveWhiteKing in *; destruct P, P'; simpl in *. lia.
    - rewrite LegalPositionAfterMirrorY; auto.
    - rewrite LegalPositionAfterMirrorY; auto.
  + right. intuition.
    - clear H0 H3 H5 H1 H2. unfold MoveWhiteRook, Between in *; simpl in *.
      destruct P, P'; simpl in *. destruct H; [left | right]; intuition; subst; lia.
    - clear H H3 H5 H1 H2. unfold OtherAfterMoveWhiteRook in *; destruct P, P'; simpl in *. lia.
    - rewrite LegalPositionAfterMirrorY; auto.
    - rewrite LegalPositionAfterMirrorY; auto.
Qed.

Theorem BlackMoveAndMirrorY N (P P': Position N):
  LegalBlackMove P P' <-> LegalBlackMove (MirrorY P) (MirrorY P').
Proof.
  unfold LegalBlackMove; simpl. intuition.
  + clear H H3 H5 H1 H2. unfold MoveBlackKing in *; destruct P, P'; simpl in *. lia.
  + clear H0 H3 H5 H1 H2. unfold OtherAfterMoveBlackKing in *; simpl in *. lia.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + clear H H3 H5 H1 H2. unfold MoveBlackKing in *; destruct P, P'; simpl in *. lia.
  + clear H0 H3 H5 H1 H2. unfold OtherAfterMoveBlackKing in *; destruct P, P'; simpl in *. lia.
  + rewrite LegalPositionAfterMirrorY; auto.
  + rewrite LegalPositionAfterMirrorY; auto.
Qed.

(* SwapXY *)

Theorem LegalPositionAfterSwapXY N (P: Position N):
  LegalPosition P <-> LegalPosition (SwapXY P).
Proof.
  unfold LegalPosition, SwapXY; simpl. intuition.
  + clear H H2 H1. unfold NotOnSameSquare in *; simpl in *. tauto.
  + clear H0 H2 H1. unfold NotKingNextToKing in *; simpl in *. tauto.
  + subst. apply H2; auto. clear H H0 H1 H2 H5. unfold BlackKingAttacked in *; simpl in *. tauto.
  + clear H H2 H1. unfold NotOnSameSquare in *; simpl in *. tauto.
  + clear H1 H2 H0. unfold NotKingNextToKing in *; simpl in *. tauto.
  + apply H2; auto. clear H0 H H1 H2 H5. unfold BlackKingAttacked, Between in *; simpl in *. tauto.
Qed.

Theorem CheckmateAfterSwapXY N (P: Position N):
  Checkmate P <-> Checkmate (SwapXY P).
Proof.
  unfold Checkmate; simpl; intuition.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + clear H0 H1 H3. unfold BlackKingAttacked in *; simpl in *. tauto.
  + apply (H3 (SwapXY P')). clear H H1 H3 H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H0 H2 H3 H5. unfold MoveBlackKing in *; simpl in *. tauto.
    - clear H0 H2 H H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
    - apply LegalPositionAfterSwapXY; auto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
  + apply LegalPositionAfterSwapXY; auto.
  + clear H0 H1 H3. unfold BlackKingAttacked in *; simpl in *. tauto.
  + apply (H3 (SwapXY P')). clear H3 H H1 H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H0 H1 H2 H3 H5. unfold MoveBlackKing in *; simpl in *. tauto.
    - clear H0 H2 H H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
Qed.

Theorem StalemateAfterSwapXY N (P: Position N):
  Stalemate P <-> Stalemate (SwapXY P).
Proof.
  unfold Stalemate; simpl; intuition.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + clear H0 H1 H3. apply H; clear H. unfold BlackKingAttacked in *; simpl in *. tauto.
  + apply (H3 (SwapXY P')). clear H H1 H3 H0.
    unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H0 H2 H3 H5. unfold MoveBlackKing in *; simpl in *. tauto.
    - clear H H0 H2 H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
    - apply LegalPositionAfterSwapXY; auto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
  + apply LegalPositionAfterSwapXY; auto.
  + clear H0 H1 H3. unfold BlackKingAttacked, Between in *; simpl in *. tauto.
  + apply (H3 (SwapXY P')). clear H3 H H0 H1. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H0 H2 H3 H5. unfold MoveBlackKing in *; simpl in *. tauto.
    - clear H H0 H2 H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
Qed.

Theorem InsufficientMaterialAfterSwapXY N (P: Position N):
  InsufficientMaterial P <-> InsufficientMaterial (SwapXY P).
Proof.
  unfold InsufficientMaterial; simpl; intuition.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + rewrite LegalPositionAfterSwapXY. auto.
Qed.

Theorem WhiteMoveAndSwapXY N (P P': Position N):
  LegalWhiteMove P P' <-> LegalWhiteMove (SwapXY P) (SwapXY P').
Proof.
  unfold LegalWhiteMove, LegalMoveWhiteKing, LegalMoveWhiteRook; simpl. intuition.
  + left. intuition.
    - clear H3 H5 H0 H1 H2. unfold MoveWhiteKing in *; simpl in *. tauto.
    - clear H3 H5 H H1 H2. unfold OtherAfterMoveWhiteKing in *; simpl in *. tauto.
    - rewrite <- LegalPositionAfterSwapXY. auto.
    - rewrite <- LegalPositionAfterSwapXY. auto.
  + right. intuition.
    - clear H0 H3 H5 H1 H2. unfold MoveWhiteRook, Between in *; simpl in *. tauto.
    - clear H H3 H5 H1 H2. unfold OtherAfterMoveWhiteRook in *; simpl in *. tauto.
    - rewrite <- LegalPositionAfterSwapXY. auto.
    - rewrite <- LegalPositionAfterSwapXY. auto.
  + left. intuition.
    - clear H0 H3 H5 H1 H2. unfold MoveWhiteKing in *; simpl in *. tauto.
    - clear H H3 H5 H1 H2. unfold OtherAfterMoveWhiteKing in *; simpl in *. tauto.
    - rewrite LegalPositionAfterSwapXY; auto.
    - rewrite LegalPositionAfterSwapXY; auto.
  + right. intuition.
    - clear H0 H3 H5 H1 H2. unfold MoveWhiteRook, Between in *; simpl in *. tauto.
    - clear H H3 H5 H1 H2. unfold OtherAfterMoveWhiteRook in *; simpl in *. tauto.
    - rewrite LegalPositionAfterSwapXY; auto.
    - rewrite LegalPositionAfterSwapXY; auto.
Qed.

Theorem BlackMoveAndSwapXY N (P P': Position N):
  LegalBlackMove P P' <-> LegalBlackMove (SwapXY P) (SwapXY P').
Proof.
  unfold LegalBlackMove; simpl. intuition.
  + clear H H3 H5 H1 H2. unfold MoveBlackKing in *; simpl in *. tauto.
  + clear H0 H3 H5 H1 H2. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + clear H H3 H5 H1 H2. unfold MoveBlackKing in *; simpl in *. tauto.
  + clear H0 H3 H5 H1 H2. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
  + rewrite LegalPositionAfterSwapXY; auto.
  + rewrite LegalPositionAfterSwapXY; auto.
Qed.

(******************)

Definition IsNormalized N (P: Position N) :=
  BKx P <= N - 1 - BKx P /\ BKy P <= N - 1 - BKy P /\
  (BKy P < BKx P \/ BKy P = BKx P /\ (WKy P < WKx P \/ WKy P = WKx P /\ WRy P <= WRx P)).
