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
  BKx P1 = BKx P2 /\ BKy P1 = BKy P2 /\
  Turn P1 = Turn P2.

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

Definition Draw Nx Ny (P: Position Nx Ny) := InsufficientMaterial P \/ Stalemate P.


Inductive BlackLoss Nx Ny: Position Nx Ny -> nat -> Prop :=
  | black_lost: forall P, Mate P -> BlackLoss P 0
  | black_lost_S: forall P n, (forall P', LegalBlackMove P P' -> exists m, WhiteWin P' m /\ m <= n) ->
                  (exists P', LegalBlackMove P P' /\ WhiteWin P' n) -> BlackLoss P (S n)
with
WhiteWin Nx Ny: Position Nx Ny -> nat -> Prop :=
  | white_win: forall P n, (exists P', LegalWhiteMove P P' /\ BlackLoss P' n) -> WhiteWin P (S n).