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

Definition NotOnSameSquare Nx Ny (P: Position Nx Ny) :=
  WKx P <> WRx P \/ WKy P <> WRy P.

Definition NotKingNextToKing Nx Ny (P: Position Nx Ny) :=
  WKx P > BKx P + 1 \/ BKx P > WKx P + 1 \/ WKy P > BKy P + 1 \/ BKy P > WKy P + 1.

Definition BlackKingAttacked Nx Ny (P: Position Nx Ny) :=
  WRx P = BKx P /\ (WKx P <> WRx P \/ WKx P = WRx P /\ (WKy P <= BKy P /\ WKy P <= WRy P \/ BKy P <= WKy P /\ WRy P <= WKy P)) \/
  WRy P = BKy P /\ (WKy P <> WRy P \/ WKy P = WRy P /\ (WKx P <= BKx P /\ WKx P <= WRx P \/ BKx P <= WKx P /\ WRx P <= WKx P)).

Definition LegalPosition Nx Ny (P: Position Nx Ny) :=
  NotOnSameSquare P /\
  NotKingNextToKing P /\
  Turn P <= 1 /\
  ~ (BlackKingAttacked P /\ Turn P = White).

Definition MoveWhiteKing Nx Ny (P1 P2: Position Nx Ny) :=
  WKx P1 - 1 <= WKx P2 <= WKx P1 + 1 /\
  WKy P1 - 1 <= WKy P2 <= WKy P1 + 1 /\
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
  BKx P2 - BKx P1 <= 1 /\ BKx P1 - BKx P2 <= 1 /\
  BKy P2 - BKy P1 <= 1 /\ BKy P1 - BKy P2 <= 1 /\
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

Definition Symmetric Nx Ny (P1 P2: Position Nx Ny) :=
  P1 = P2 \/ P2 = MirrorX P1 \/ P2 = MirrorY P1 \/ P2 = MirrorY (MirrorX P1).

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
  + 
Admitted.