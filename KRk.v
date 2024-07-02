Require Import Lia.
Set Implicit Arguments.

Definition White := 0.
Definition Black := 1.

Structure Position (Nx Ny: nat) := {
  WKx: nat;
  WKy: nat;
  WRx: nat;
  WRy: nat;
  BKx: nat;
  BKy: nat;
  DimensionCheck: WKx < Nx /\ WRx < Nx /\ BKx < Nx /\ WKy < Ny /\ WRy < Ny /\ BKy < Ny;
  Turn: nat;
}.

Definition SamePosition Nx Ny (P1 P2: Position Nx Ny) :=
  WKx P1 = WKx P2 /\ WKy P1 = WKy P2 /\
  WRx P1 = WRx P2 /\ WRy P1 = WRy P2 /\
  BKx P1 = BKx P2 /\ BKy P1 = BKy P2.

Definition NotOnSameSquare Nx Ny (P: Position Nx Ny) :=
  (WKx P <> WRx P \/ WKy P <> WRy P) /\ (Turn P = Black -> (WRx P <> BKx P \/ WRy P <> BKy P)).

Definition NotKingNextToKing Nx Ny (P: Position Nx Ny) :=
  WKx P > BKx P + 1 \/ BKx P > WKx P + 1 \/ WKy P > BKy P + 1 \/ BKy P > WKy P + 1.

Definition BlackKingAttacked Nx Ny (P: Position Nx Ny) :=
  (WRx P = BKx P /\ (WKx P <> WRx P \/ WKx P = WRx P /\ (WKy P <= BKy P /\ WKy P <= WRy P \/ BKy P <= WKy P /\ WRy P <= WKy P)) \/
   WRy P = BKy P /\ (WKy P <> WRy P \/ WKy P = WRy P /\ (WKx P <= BKx P /\ WKx P <= WRx P \/ BKx P <= WKx P /\ WRx P <= WKx P))) /\
   (WRx P <> BKx P \/ WRy P <> BKy P).


Definition LegalPosition Nx Ny (P: Position Nx Ny) :=
  NotOnSameSquare P /\
  NotKingNextToKing P /\
  Turn P <= 1 /\
  ~ (BlackKingAttacked P /\ Turn P = White).

Definition MoveWhiteKing Nx Ny (P1 P2: Position Nx Ny) :=
  WKx P1 <= WKx P2 + 1 /\ WKx P2 <= WKx P1 + 1 /\
  WKy P1 <= WKy P2 + 1 /\ WKy P2 <= WKy P1 + 1 /\
  (WKx P1 <> WKx P2 \/ WKy P1 <> WKy P2).

Definition OtherAfterMoveWhiteKing Nx Ny (P1 P2: Position Nx Ny) :=
  BKx P2 = BKx P1 /\ BKy P2 = BKy P1 /\
  WRx P2 = WRx P1 /\ WRy P2 = WRy P1.

Definition LegalMoveWhiteKing Nx Ny (P1 P2: Position Nx Ny) :=
  MoveWhiteKing P1 P2 /\
  OtherAfterMoveWhiteKing P1 P2 /\
  Turn P1 = White /\
  Turn P2 = Black /\
  LegalPosition P1 /\
  LegalPosition P2.

Definition Between x1 x2 x :=
  x1 < x < x2 \/ x2 < x < x1.

Definition MoveWhiteRook Nx Ny (P1 P2: Position Nx Ny) :=
  (WRx P1 = WRx P2 /\ WRy P1 <> WRy P2 /\
   (WKx P1 <> WRx P1 \/ ~ Between (WRy P1) (WRy P2) (WKy P1)) /\
   (BKx P1 <> WRx P1 \/ ~ Between (WRy P1) (WRy P2) (BKy P1)))
  \/
  (WRy P1 = WRy P2 /\ WRx P1 <> WRx P2 /\
   (WKy P1 <> WRy P1 \/ ~ Between (WRx P1) (WRx P2) (WKx P1)) /\
   (BKy P1 <> WRy P1 \/ ~ Between (WRx P1) (WRx P2) (BKx P1))).

Definition OtherAfterMoveWhiteRook Nx Ny (P1 P2: Position Nx Ny) :=
  WKx P2 = WKx P1 /\ WKy P2 = WKy P1 /\
  BKx P2 = BKx P1 /\ BKy P2 = BKy P1.

Definition LegalMoveWhiteRook Nx Ny (P1 P2: Position Nx Ny) :=
  MoveWhiteRook P1 P2 /\
  OtherAfterMoveWhiteRook P1 P2 /\
  Turn P1 = White /\
  Turn P2 = Black /\
  LegalPosition P1 /\
  LegalPosition P2.

Definition LegalWhiteMove Nx Ny (P1 P2: Position Nx Ny) :=
  LegalMoveWhiteKing P1 P2 \/ LegalMoveWhiteRook P1 P2.

Definition MoveBlackKing Nx Ny (P1 P2: Position Nx Ny) :=
  BKx P1 <= BKx P2 + 1 /\ BKx P2 <= BKx P1 + 1 /\
  BKy P1 <= BKy P2 + 1 /\ BKy P2 <= BKy P1 + 1 /\
  (BKx P1 <> BKx P2 \/ BKy P1 <> BKy P2).

Definition OtherAfterMoveBlackKing Nx Ny (P1 P2: Position Nx Ny) :=
  WKx P2 = WKx P1 /\ WKy P2 = WKy P1 /\
  WRx P2 = WRx P1 /\ WRy P2 = WRy P1.

Definition LegalBlackMove Nx Ny (P1 P2: Position Nx Ny) :=
  MoveBlackKing P1 P2 /\
  OtherAfterMoveBlackKing P1 P2 /\
  Turn P1 = Black /\
  Turn P2 = White /\
  LegalPosition P1 /\
  LegalPosition P2.

Definition Mate Nx Ny (P: Position Nx Ny) :=
  LegalPosition P /\ BlackKingAttacked P /\ Turn P = Black /\ forall P': Position Nx Ny, ~ LegalBlackMove P P'.

Definition Stalemate Nx Ny (P: Position Nx Ny) :=
  LegalPosition P /\ ~ BlackKingAttacked P /\ Turn P = Black /\ forall P': Position Nx Ny, ~ LegalBlackMove P P'.

Definition InsufficientMaterial Nx Ny (P: Position Nx Ny) :=
  LegalPosition P /\ Turn P = White /\ BKx P = WRx P /\ BKy P = WRy P.

(* Symmetries *)

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

(*****************)

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

Ltac intuition' := intuition;
                   try (unfold NotKingNextToKing in *; simpl in *; lia);
                   try (unfold NotOnSameSquare in *; simpl in *; lia);
                   try (unfold BlackKingAttacked in *; simpl in *; lia);
                   try (unfold MoveBlackKing in *; simpl in *; lia);
                   try (unfold OtherAfterMoveBlackKing in *; simpl in *; lia).

Ltac BK_move H Nx Ny P x y :=
  try (
  assert (WKx P < Nx /\ WRx P < Nx /\ x < Nx /\ WKy P < Ny /\ WRy P < Ny /\ y < Ny) as DC
    by (abstract (destruct P; simpl in *; lia));
  refine (H (@Build_Position _ _ (WKx P) (WKy P) (WRx P) (WRy P) x y DC White) _);
  unfold LegalBlackMove, LegalPosition in *; intuition').

Ltac BK_moves H Nx Ny P :=
  try (exfalso;
  try (BK_move H Nx Ny P (BKx P + 1) (BKy P + 1); fail);
  try (BK_move H Nx Ny P (BKx P + 1) (BKy P); fail);
  try (BK_move H Nx Ny P (BKx P + 1) (BKy P - 1); fail);
  try (BK_move H Nx Ny P (BKx P) (BKy P - 1); fail);
  try (BK_move H Nx Ny P (BKx P - 1) (BKy P - 1); fail);
  try (BK_move H Nx Ny P (BKx P - 1) (BKy P); fail);
  try (BK_move H Nx Ny P (BKx P - 1) (BKy P + 1); fail);
  try (BK_move H Nx Ny P (BKx P) (BKy P + 1); fail);
  fail).

Theorem StalemateAllTypes Nx Ny (P: Position Nx Ny) (Hx: 3 <= Nx) (Hy: 3 <= Ny):
  (BKx P <= Nx - 1 - BKx P /\ BKy P <= Ny - 1 - BKy P) ->
  (Stalemate P <-> (StalemateType1 P Hx Hy \/ StalemateType2 P Hx Hy)).
Proof.
  assert (Black = 1) by (unfold Black; auto). assert (White = 0) by (unfold White; auto).
  split; intros.
  + unfold Stalemate, LegalPosition in *; intuition. clear H8.
    assert (BKx P = 0 \/ 1 <= BKx P) by lia. assert (BKy P = 0 \/ 1 <= BKy P) by lia. intuition.
    - assert (WKy P = 2 /\ (WKx P = 0 \/ WKx P = 1 \/ WKx P = 2) \/ WKy P = 1 /\ WKx P = 2 \/ WKy P = 0 /\ WKx P = 2 \/ 3 <= WKx P \/ 3 <= WKy P).
      { unfold NotKingNextToKing in *; lia. }
      intuition.
      * assert (WRx P = 0 /\ 3 <= WRy P \/ WRx P = 1 /\ (WRy P = 1 \/ 2 <= WRy P) \/ 2 <= WRx P /\ 1 <= WRy P).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
        ++ left. unfold StalemateType1. lia.
        ++ right. unfold StalemateType2. lia.
      * assert (WRx P = 1 /\ (WRy P = 1 \/ 3 <= WRy P) \/ 2 <= WRx P /\ 1 <= WRx P).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
        left. unfold StalemateType1. lia.
      * assert (WRx P = 1 /\ (WRy P = 1 \/ 2 <= WRy P) \/ (WRx P = 2 /\ (WRy P = 1 \/ 3 <= WRy P)) \/ 3 <= WRx P /\ 1 <= WRy P).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
        left. unfold StalemateType1. lia.
      * assert (WRx P = 1 /\ (WRy P = 1 \/ 2 <= WRy P) \/ WRx P = 2 /\ 2 <= WRy P \/ 3 <= WRx P /\ 1 <= WRy P).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
        left. unfold StalemateType1. lia.
      * assert (WRy P = 1 /\ (WRx P = 1 \/ 2 <= WRx P) \/ WRy P = 0 /\ 3 <= WRx P \/ 2 <= WRy P /\ 1 <= WRx P).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
        ++ left. unfold StalemateType1. lia.
        ++ right. unfold StalemateType2. lia.
      * assert (WRy P = 1 /\ (WRx P = 1 \/ 2 <= WRx P) \/ WRy P = 0 /\ WKx P + 1 <= WRx P \/ 2 <= WRy P /\ 1 <= WRx P).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
      * assert (WRx P = 1 /\ (WRy P = 1 \/ 2 <= WRy P) \/ WRx P = 0 /\ WKy P + 1 <= WRy P \/ 2 <= WRx P /\ 1 <= WRy P).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
    - assert ((WKx P = 0 \/ WKx P = 1) /\ (WKy P + 3 <= BKy P \/ WKy P + 2 = BKy P \/ BKy P + 2 = WKy P \/ BKy P + 3 <= WKy P) \/
              WKx P = 2 /\ (WKy P + 3 <= BKy P \/ WKy P + 2 = BKy P \/ WKy P + 1 = BKy P \/ WKy P = BKy P \/ BKy P + 1 = WKy P \/ BKy P + 2 = WKy P \/ BKy P + 3 <= WKy P) \/
              3 <= WKx P).
      { unfold NotKingNextToKing in *; lia. }
      intuition.
      * assert (WRx P = 0 /\ WRy P < WKy P \/ 1 <= WRx P /\ (WRy P < BKy P \/ BKy P < WRy P)).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
      * assert (WRx P = 0 /\ WRy P < WKy P \/ WRx P = 1 /\ (WRy P + 1 <= BKy P \/ BKy P + 1 = WRy P \/ BKy P + 2 <= WRy P) \/
                2 <= WRx P /\ WRy P <> BKy P).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
      * assert (WRx P = 0 /\ WRy P > WKy P \/ WRx P = 1 /\ (BKy P + 1 <= WRy P \/ WRy P + 1 = BKy P \/ WRy P + 2 <= BKy P) \/
                2 <= WRx P /\ WRy P <> BKy P).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
      * assert (WRx P = 0 /\ WRy P > WKy P \/ 1 <= WRx P /\ (BKy P < WRy P \/ WRy P < BKy P)).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
      * assert (WRx P = 0 /\ WRy P < WKy P \/ 1 <= WRx P /\ (BKy P < WRy P \/ WRy P < BKy P)).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
      * assert (WRx P = 1 /\ (WRy P < WKy P \/ WRy P + 1 = BKy P \/ BKy P + 1 = WRy P \/ BKy P + 2 <= WRy P) \/ 2 <= WRx P /\ (WRy P < BKy P \/ BKy P < WRy P)).
        { unfold BlackKingAttacked, NotOnSameSquare in *; lia. }
        intuition; try (BK_moves H9 Nx Ny P).
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
    - admit.
    - admit.
  + unfold Stalemate. intuition.
    - unfold StalemateType1, LegalPosition, NotOnSameSquare, NotKingNextToKing in *. lia.
    - unfold StalemateType1, BlackKingAttacked in *. lia.
    - unfold StalemateType1 in *. lia.
    - unfold LegalBlackMove, LegalPosition in *. intuition. unfold OtherAfterMoveBlackKing in *.
      intuition. unfold StalemateType1 in *. intuition.
      * destruct P, P'. simpl in *. subst. unfold NotOnSameSquare in *; simpl in *.
        unfold BlackKingAttacked in *; simpl in *. unfold NotKingNextToKing in *; simpl in *.
        unfold MoveBlackKing in *; simpl in *. lia.
      * destruct P, P'. simpl in *. subst. unfold NotOnSameSquare in *; simpl in *.
        unfold BlackKingAttacked in *; simpl in *. unfold NotKingNextToKing in *; simpl in *.
        unfold MoveBlackKing in *; simpl in *. lia.
      * destruct P, P'. simpl in *. subst. unfold NotOnSameSquare in *; simpl in *.
        unfold BlackKingAttacked in *; simpl in *. unfold NotKingNextToKing in *; simpl in *.
        unfold MoveBlackKing in *; simpl in *. lia.
      * destruct P, P'. simpl in *. subst. unfold NotOnSameSquare in *; simpl in *.
        unfold BlackKingAttacked in *; simpl in *. unfold NotKingNextToKing in *; simpl in *.
        unfold MoveBlackKing in *; simpl in *. lia.
      * destruct P, P'. simpl in *. subst. unfold NotOnSameSquare in *; simpl in *.
        unfold BlackKingAttacked in *; simpl in *. unfold NotKingNextToKing in *; simpl in *.
        unfold MoveBlackKing in *; simpl in *. lia.
    - unfold StalemateType2, LegalPosition, NotOnSameSquare, NotKingNextToKing in *. lia.
    - unfold StalemateType2, BlackKingAttacked in *. lia.
    - unfold StalemateType2 in *. lia.
    - unfold LegalBlackMove, LegalPosition in *. intuition. unfold OtherAfterMoveBlackKing in *.
      intuition. unfold StalemateType2 in *. intuition.
      * destruct P, P'. simpl in *. subst. unfold NotOnSameSquare in *; simpl in *.
        unfold BlackKingAttacked in *; simpl in *. unfold NotKingNextToKing in *; simpl in *.
        unfold MoveBlackKing in *; simpl in *. lia.
      * destruct P, P'. simpl in *. subst. unfold NotOnSameSquare in *; simpl in *.
        unfold BlackKingAttacked in *; simpl in *. unfold NotKingNextToKing in *; simpl in *.
        unfold MoveBlackKing in *; simpl in *. lia.
Admitted.


