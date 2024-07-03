Require Import Lia.
Require Import BasicDefinitions.
Set Implicit Arguments.

Definition MirrorX Nx Ny (P: Position Nx Ny): Position Nx Ny.
Proof.
  refine (@Build_Position Nx Ny (Nx - 1 - WKx P) (WKy P) (Nx - 1 - WRx P) (WRy P) (Nx - 1 - BKx P) (BKy P) _ (Turn P)).
  destruct P; simpl in *. abstract lia.
Defined.

Definition MirrorY Nx Ny (P: Position Nx Ny): Position Nx Ny.
Proof.
  refine (@Build_Position Nx Ny (WKx P) (Ny - 1 - WKy P) (WRx P) (Ny - 1 - WRy P) (BKx P) (Ny - 1 - BKy P) _ (Turn P)).
  destruct P; simpl in *. abstract lia.
Defined.

Definition RectangularSymmetric Nx Ny (P1 P2: Position Nx Ny) :=
  SamePosition P1 P2 \/ SamePosition P1 (MirrorX P2) \/ SamePosition P1 (MirrorY P2) \/ SamePosition P1 (MirrorY (MirrorX P2)).

Definition SwapXY Nx Ny (P: Position Nx Ny): Position Ny Nx.
Proof.
  refine (@Build_Position Ny Nx (WKy P) (WKx P) (WRy P) (WRx P) (BKy P) (BKx P) _ (Turn P)).
  destruct P; simpl in *. abstract tauto.
Defined.

Definition SquareSymmetric N (P1 P2: Position N N) :=
  SamePosition P1 P2 \/ SamePosition P1 (MirrorX P2) \/ SamePosition P1 (MirrorY P2) \/ SamePosition P1 (MirrorY (MirrorX P2)) \/
  SamePosition P1 (SwapXY P2) \/ SamePosition P1 (SwapXY (MirrorX P2)) \/
  SamePosition P1 (SwapXY (MirrorY P2)) \/ SamePosition P1 (SwapXY (MirrorY (MirrorX P2))).

(* MirrorX *)

Theorem LegalPositionAfterMirrorX Nx Ny (P: Position Nx Ny):
  LegalPosition P <-> LegalPosition (MirrorX P).
Proof.
  unfold LegalPosition, MirrorX; simpl. destruct P; simpl in *. intuition.
  + clear H H2. unfold NotOnSameSquare in *; simpl in *. lia.
  + clear H0 H2. unfold NotKingNextToKing in *; simpl in *. lia.
  + subst. apply H2; auto. clear H H0 H2. unfold BlackKingAttacked in *; simpl in *. lia.
  + clear H H2. unfold NotOnSameSquare in *; simpl in *. lia.
  + clear H2 H0. unfold NotKingNextToKing in *; simpl in *. lia.
  + apply H2; auto. subst. clear H0 H H2. unfold BlackKingAttacked in *; simpl in *. lia.
Qed.

Theorem MateAfterMirrorX Nx Ny (P: Position Nx Ny):
  Mate P <-> Mate (MirrorX P).
Proof.
  unfold Mate; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + clear H0 H3. unfold BlackKingAttacked, MirrorX in *; destruct P; simpl in *. lia.
  + apply (H3 (MirrorX P')). clear H H3 H0.
    unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - apply LegalPositionAfterMirrorX; auto.
    - rewrite <- LegalPositionAfterMirrorX; auto.
  + apply LegalPositionAfterMirrorX; auto.
  + clear H0 H3. unfold BlackKingAttacked, MirrorX in *; destruct P; simpl in *. lia.
  + apply (H3 (MirrorX P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorX; auto.
    - rewrite <- LegalPositionAfterMirrorX; auto.
Qed.

Theorem StalemateAfterMirrorX Nx Ny (P: Position Nx Ny):
  Stalemate P <-> Stalemate (MirrorX P).
Proof.
  unfold Stalemate; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + clear H0 H3. apply H; clear H. unfold BlackKingAttacked in *; simpl in *.
    destruct P; simpl in *. lia.
  + apply (H3 (MirrorX P')). clear H H3 H0.
    unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - apply LegalPositionAfterMirrorX; auto.
    - rewrite <- LegalPositionAfterMirrorX; auto.
  + apply LegalPositionAfterMirrorX; auto.
  + clear H0 H3. unfold BlackKingAttacked in *; simpl in *. destruct P; simpl in *. lia.
  + apply (H3 (MirrorX P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorX; auto.
    - rewrite <- LegalPositionAfterMirrorX; auto.
Qed.

Theorem InsufficientMaterialAfterMirrorX Nx Ny (P: Position Nx Ny):
  InsufficientMaterial P <-> InsufficientMaterial (MirrorX P).
Proof.
  unfold InsufficientMaterial; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + rewrite LegalPositionAfterMirrorX. auto.
  + destruct P; simpl in *. clear H0. lia.
Qed.

Theorem WhiteMoveAndMirrorX Nx Ny (P P': Position Nx Ny):
  LegalWhiteMove P P' <-> LegalWhiteMove (MirrorX P) (MirrorX P').
Proof.
  unfold LegalWhiteMove; simpl. unfold LegalMoveWhiteKing, LegalMoveWhiteRook; simpl. intuition.
  + left. intuition.
    - clear H3 H5 H0. unfold MoveWhiteKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H3 H5 H. unfold OtherAfterMoveWhiteKing in *; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorX. auto.
    - rewrite <- LegalPositionAfterMirrorX. auto.
  + right. intuition.
    - clear H0 H3 H5. unfold MoveWhiteRook, Between in *; simpl in *.
      destruct P, P'; simpl in *. intuition; subst; try lia.
    - clear H H3 H5. unfold OtherAfterMoveWhiteRook in *; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorX. auto.
    - rewrite <- LegalPositionAfterMirrorX. auto.
  + left. intuition.
    - clear H0 H3 H5. unfold MoveWhiteKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H H3 H5. unfold OtherAfterMoveWhiteKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - rewrite LegalPositionAfterMirrorX; auto.
    - rewrite LegalPositionAfterMirrorX; auto.
  + right. intuition.
    - clear H0 H3 H5. unfold MoveWhiteRook, Between in *; simpl in *.
      destruct P, P'; simpl in *. intuition; subst; try lia.
    - clear H H3 H5. unfold OtherAfterMoveWhiteRook in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - rewrite LegalPositionAfterMirrorX; auto.
    - rewrite LegalPositionAfterMirrorX; auto.
Qed.

Theorem BlackMoveAndMirrorX Nx Ny (P P': Position Nx Ny):
  LegalBlackMove P P' <-> LegalBlackMove (MirrorX P) (MirrorX P').
Proof.
  unfold LegalBlackMove; simpl. intuition.
  + clear H H3 H5. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
  + clear H0 H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. lia.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + rewrite <- LegalPositionAfterMirrorX. auto.
  + clear H H3 H5. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
  + clear H0 H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
  + rewrite LegalPositionAfterMirrorX; auto.
  + rewrite LegalPositionAfterMirrorX; auto.
Qed.

(* MirrorY *)

Theorem LegalPositionAfterMirrorY Nx Ny (P: Position Nx Ny):
  LegalPosition P <-> LegalPosition (MirrorY P).
Proof.
  unfold LegalPosition, MirrorY; simpl. destruct P; simpl in *. intuition.
  + clear H H2. unfold NotOnSameSquare in *; simpl in *. lia.
  + clear H0 H2. unfold NotKingNextToKing in *; simpl in *. lia.
  + subst. apply H2; auto. clear H H0 H2. unfold BlackKingAttacked in *; simpl in *. lia.
  + clear H H2. unfold NotOnSameSquare in *; simpl in *. lia.
  + clear H2 H0. unfold NotKingNextToKing in *; simpl in *. lia.
  + apply H2; auto. subst. clear H0 H H2. unfold BlackKingAttacked in *; simpl in *. lia.
Qed.

Theorem MateAfterMirrorY Nx Ny (P: Position Nx Ny):
  Mate P <-> Mate (MirrorY P).
Proof.
  unfold Mate; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + clear H0 H3. unfold BlackKingAttacked, MirrorY in *; destruct P; simpl in *. lia.
  + apply (H3 (MirrorY P')). clear H H3 H0.
    unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - apply LegalPositionAfterMirrorY; auto.
    - rewrite <- LegalPositionAfterMirrorY; auto.
  + apply LegalPositionAfterMirrorY; auto.
  + clear H0 H3. unfold BlackKingAttacked, MirrorY in *; destruct P; simpl in *. lia.
  + apply (H3 (MirrorY P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorY; auto.
    - rewrite <- LegalPositionAfterMirrorY; auto.
Qed.

Theorem StalemateAfterMirrorY Nx Ny (P: Position Nx Ny):
  Stalemate P <-> Stalemate (MirrorY P).
Proof.
  unfold Stalemate; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + clear H0 H3. apply H; clear H. unfold BlackKingAttacked in *; simpl in *.
    destruct P; simpl in *. lia.
  + apply (H3 (MirrorY P')). clear H H3 H0.
    unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - apply LegalPositionAfterMirrorY; auto.
    - rewrite <- LegalPositionAfterMirrorY; auto.
  + apply LegalPositionAfterMirrorY; auto.
  + clear H0 H3. unfold BlackKingAttacked in *; simpl in *. destruct P; simpl in *. lia.
  + apply (H3 (MirrorY P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorY; auto.
    - rewrite <- LegalPositionAfterMirrorY; auto.
Qed.

Theorem InsufficientMaterialAfterMirrorY Nx Ny (P: Position Nx Ny):
  InsufficientMaterial P <-> InsufficientMaterial (MirrorY P).
Proof.
  unfold InsufficientMaterial; simpl; intuition.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + rewrite LegalPositionAfterMirrorY. auto.
  + destruct P; simpl in *. clear H0. lia.
Qed.

Theorem WhiteMoveAndMirrorY Nx Ny (P P': Position Nx Ny):
  LegalWhiteMove P P' <-> LegalWhiteMove (MirrorY P) (MirrorY P').
Proof.
  unfold LegalWhiteMove; simpl. unfold LegalMoveWhiteKing, LegalMoveWhiteRook; simpl. intuition.
  + left. intuition.
    - clear H3 H5 H0. unfold MoveWhiteKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H3 H5 H. unfold OtherAfterMoveWhiteKing in *; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorY. auto.
    - rewrite <- LegalPositionAfterMirrorY. auto.
  + right. intuition.
    - clear H0 H3 H5. unfold MoveWhiteRook, Between in *; simpl in *.
      destruct P, P'; simpl in *. intuition; subst; try lia.
    - clear H H3 H5. unfold OtherAfterMoveWhiteRook in *; simpl in *. lia.
    - rewrite <- LegalPositionAfterMirrorY. auto.
    - rewrite <- LegalPositionAfterMirrorY. auto.
  + left. intuition.
    - clear H0 H3 H5. unfold MoveWhiteKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - clear H H3 H5. unfold OtherAfterMoveWhiteKing in *; simpl in *. destruct P, P'; simpl in *. lia.
    - rewrite LegalPositionAfterMirrorY; auto.
    - rewrite LegalPositionAfterMirrorY; auto.
  + right. intuition.
    - clear H0 H3 H5. unfold MoveWhiteRook, Between in *; simpl in *.
      destruct P, P'; simpl in *. intuition; subst; try lia.
    - clear H H3 H5. unfold OtherAfterMoveWhiteRook in *; simpl in *.
      destruct P, P'; simpl in *. lia.
    - rewrite LegalPositionAfterMirrorY; auto.
    - rewrite LegalPositionAfterMirrorY; auto.
Qed.

Theorem BlackMoveAndMirrorY Nx Ny (P P': Position Nx Ny):
  LegalBlackMove P P' <-> LegalBlackMove (MirrorY P) (MirrorY P').
Proof.
  unfold LegalBlackMove; simpl. intuition.
  + clear H H3 H5. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
  + clear H0 H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. lia.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + rewrite <- LegalPositionAfterMirrorY. auto.
  + clear H H3 H5. unfold MoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
  + clear H0 H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. destruct P, P'; simpl in *. lia.
  + rewrite LegalPositionAfterMirrorY; auto.
  + rewrite LegalPositionAfterMirrorY; auto.
Qed.

(* SwapXY *)

Theorem LegalPositionAfterSwapXY Nx Ny (P: Position Nx Ny):
  LegalPosition P <-> LegalPosition (SwapXY P).
Proof.
  unfold LegalPosition, SwapXY; simpl. intuition.
  + clear H H2. unfold NotOnSameSquare in *; simpl in *. tauto.
  + clear H0 H2. unfold NotKingNextToKing in *; simpl in *. tauto.
  + subst. apply H2; auto. clear H H0 H2. unfold BlackKingAttacked in *; simpl in *. tauto.
  + clear H H2. unfold NotOnSameSquare in *; simpl in *. tauto.
  + clear H2 H0. unfold NotKingNextToKing in *; simpl in *. tauto.
  + apply H2; auto. subst. clear H0 H H2. unfold BlackKingAttacked in *; simpl in *. tauto.
Qed.

Theorem MateAfterSwapXY Nx Ny (P: Position Nx Ny):
  Mate P <-> Mate (SwapXY P).
Proof.
  unfold Mate; simpl; intuition.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + clear H0 H3. unfold BlackKingAttacked in *; simpl in *. tauto.
  + apply (H3 (SwapXY P')). clear H H3 H0.
    unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. tauto.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
    - apply LegalPositionAfterSwapXY; auto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
  + apply LegalPositionAfterSwapXY; auto.
  + clear H0 H3. unfold BlackKingAttacked in *; simpl in *. tauto.
  + apply (H3 (SwapXY P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. tauto.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
Qed.

Theorem StalemateAfterSwapXY Nx Ny (P: Position Nx Ny):
  Stalemate P <-> Stalemate (SwapXY P).
Proof.
  unfold Stalemate; simpl; intuition.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + clear H0 H3. apply H; clear H. unfold BlackKingAttacked in *; simpl in *. tauto.
  + apply (H3 (SwapXY P')). clear H H3 H0.
    unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. tauto.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
    - apply LegalPositionAfterSwapXY; auto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
  + apply LegalPositionAfterSwapXY; auto.
  + clear H0 H3. unfold BlackKingAttacked in *; simpl in *. tauto.
  + apply (H3 (SwapXY P')). clear H3 H H0. unfold LegalBlackMove in *; simpl in *. intuition.
    - clear H1 H2 H4 H6. unfold MoveBlackKing in *; simpl in *. tauto.
    - clear H1 H H4 H6. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
    - rewrite <- LegalPositionAfterSwapXY; auto.
Qed.

Theorem InsufficientMaterialAfterSwapXY Nx Ny (P: Position Nx Ny):
  InsufficientMaterial P <-> InsufficientMaterial (SwapXY P).
Proof.
  unfold InsufficientMaterial; simpl; intuition.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + rewrite LegalPositionAfterSwapXY. auto.
Qed.

Theorem WhiteMoveAndSwapXY Nx Ny (P P': Position Nx Ny):
  LegalWhiteMove P P' <-> LegalWhiteMove (SwapXY P) (SwapXY P').
Proof.
  unfold LegalWhiteMove; simpl. unfold LegalMoveWhiteKing, LegalMoveWhiteRook; simpl. intuition.
  + left. intuition.
    - clear H3 H5 H0. unfold MoveWhiteKing in *; simpl in *. tauto.
    - clear H3 H5 H. unfold OtherAfterMoveWhiteKing in *; simpl in *. tauto.
    - rewrite <- LegalPositionAfterSwapXY. auto.
    - rewrite <- LegalPositionAfterSwapXY. auto.
  + right. intuition.
    - clear H0 H3 H5. unfold MoveWhiteRook, Between in *; simpl in *. tauto.
    - clear H H3 H5. unfold OtherAfterMoveWhiteRook in *; simpl in *. tauto.
    - rewrite <- LegalPositionAfterSwapXY. auto.
    - rewrite <- LegalPositionAfterSwapXY. auto.
  + left. intuition.
    - clear H0 H3 H5. unfold MoveWhiteKing in *; simpl in *. tauto.
    - clear H H3 H5. unfold OtherAfterMoveWhiteKing in *; simpl in *. tauto.
    - rewrite LegalPositionAfterSwapXY; auto.
    - rewrite LegalPositionAfterSwapXY; auto.
  + right. intuition.
    - clear H0 H3 H5. unfold MoveWhiteRook, Between in *; simpl in *. tauto.
    - clear H H3 H5. unfold OtherAfterMoveWhiteRook in *; simpl in *. tauto.
    - rewrite LegalPositionAfterSwapXY; auto.
    - rewrite LegalPositionAfterSwapXY; auto.
Qed.

Theorem BlackMoveAndSwapXY Nx Ny (P P': Position Nx Ny):
  LegalBlackMove P P' <-> LegalBlackMove (SwapXY P) (SwapXY P').
Proof.
  unfold LegalBlackMove; simpl. intuition.
  + clear H H3 H5. unfold MoveBlackKing in *; simpl in *. tauto.
  + clear H0 H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + rewrite <- LegalPositionAfterSwapXY. auto.
  + clear H H3 H5. unfold MoveBlackKing in *; simpl in *. tauto.
  + clear H0 H3 H5. unfold OtherAfterMoveBlackKing in *; simpl in *. tauto.
  + rewrite LegalPositionAfterSwapXY; auto.
  + rewrite LegalPositionAfterSwapXY; auto.
Qed.

(******************)

Definition Normalize Nx Ny (P: Position Nx Ny): Position Nx Ny :=
  if Compare_dec.le_lt_dec (BKx P) (Nx - 1 - BKx P)
  then if Compare_dec.le_lt_dec (BKy P) (Ny - 1 - BKy P)
       then P
       else MirrorY P
  else if Compare_dec.le_lt_dec (BKy P) (Ny - 1 - BKy P)
       then MirrorX P
       else MirrorY (MirrorX P).

Definition NormalizeThm Nx Ny (P: Position Nx Ny):
  let P' := Normalize P in
  BKx P' <= Nx - 1 - BKx P' /\ BKy P' <= Ny - 1 - BKy P'.
Proof.
  unfold Normalize. unfold MirrorX, MirrorY. destruct P; simpl in *.
  repeat destruct Compare_dec.le_lt_dec; simpl in *; lia.
Qed.