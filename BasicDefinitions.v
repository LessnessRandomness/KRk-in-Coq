Set Implicit Arguments.

Definition White := 0.
Definition Black := 1.

Structure Position N := {
  WKx: nat;
  WKy: nat;
  WRx: nat;
  WRy: nat;
  BKx: nat;
  BKy: nat;
  DimensionCheck: WKx < N /\ WRx < N /\ BKx < N /\ WKy < N /\ WRy < N /\ BKy < N;
  Turn: nat;
}.

Definition SamePosition N (P1 P2: Position N) :=
  WKx P1 = WKx P2 /\ WKy P1 = WKy P2 /\
  WRx P1 = WRx P2 /\ WRy P1 = WRy P2 /\
  BKx P1 = BKx P2 /\ BKy P1 = BKy P2 /\
  Turn P1 = Turn P2.

Definition NotOnSameSquare N (P: Position N) :=
  (WKx P <> WRx P \/ WKy P <> WRy P) /\ (Turn P = Black -> (WRx P <> BKx P \/ WRy P <> BKy P)).

Definition NotKingNextToKing N (P: Position N) :=
  WKx P > BKx P + 1 \/ BKx P > WKx P + 1 \/ WKy P > BKy P + 1 \/ BKy P > WKy P + 1.

Definition Between x1 x2 x :=
  x1 < x < x2 \/ x2 < x < x1.

Definition BlackKingAttacked N (P: Position N) :=
  WRx P = BKx P /\ BKy P <> WRy P /\ (~ Between (WRy P) (BKy P) (WKy P) \/ WRx P <> WKx P) \/
  WRy P = BKy P /\ BKx P <> WRx P /\ (~ Between (WRx P) (BKx P) (WKx P) \/ WRy P <> WKy P).

Definition LegalPosition N (P: Position N) :=
  NotOnSameSquare P /\
  NotKingNextToKing P /\
  Turn P <= 1 /\
  ~ (BlackKingAttacked P /\ Turn P = White).

Definition MoveWhiteKing N (P1 P2: Position N) :=
  WKx P1 <= WKx P2 + 1 /\ WKx P2 <= WKx P1 + 1 /\
  WKy P1 <= WKy P2 + 1 /\ WKy P2 <= WKy P1 + 1 /\
  (WKx P1 <> WKx P2 \/ WKy P1 <> WKy P2).

Definition OtherAfterMoveWhiteKing N (P1 P2: Position N) :=
  BKx P2 = BKx P1 /\ BKy P2 = BKy P1 /\ WRx P2 = WRx P1 /\ WRy P2 = WRy P1.

Definition LegalMoveWhiteKing N (P1 P2: Position N) :=
  MoveWhiteKing P1 P2 /\
  OtherAfterMoveWhiteKing P1 P2 /\
  Turn P1 = White /\
  Turn P2 = Black /\
  LegalPosition P1 /\
  LegalPosition P2.

Definition MoveWhiteRook N (P1 P2: Position N) :=
  (WRx P1 = WRx P2 /\ WRy P1 <> WRy P2 /\
   (WKx P1 <> WRx P1 \/ ~ Between (WRy P1) (WRy P2) (WKy P1)) /\
   (BKx P1 <> WRx P1 \/ ~ Between (WRy P1) (WRy P2) (BKy P1)))
  \/
  (WRy P1 = WRy P2 /\ WRx P1 <> WRx P2 /\
   (WKy P1 <> WRy P1 \/ ~ Between (WRx P1) (WRx P2) (WKx P1)) /\
   (BKy P1 <> WRy P1 \/ ~ Between (WRx P1) (WRx P2) (BKx P1))).

Definition OtherAfterMoveWhiteRook N (P1 P2: Position N) :=
  WKx P2 = WKx P1 /\ WKy P2 = WKy P1 /\ BKx P2 = BKx P1 /\ BKy P2 = BKy P1.

Definition LegalMoveWhiteRook N (P1 P2: Position N) :=
  MoveWhiteRook P1 P2 /\
  OtherAfterMoveWhiteRook P1 P2 /\
  Turn P1 = White /\
  Turn P2 = Black /\
  LegalPosition P1 /\
  LegalPosition P2.

Definition LegalWhiteMove N (P1 P2: Position N) :=
  LegalMoveWhiteKing P1 P2 \/ LegalMoveWhiteRook P1 P2.

Definition MoveBlackKing N (P1 P2: Position N) :=
  BKx P1 <= BKx P2 + 1 /\ BKx P2 <= BKx P1 + 1 /\
  BKy P1 <= BKy P2 + 1 /\ BKy P2 <= BKy P1 + 1 /\
  (BKx P1 <> BKx P2 \/ BKy P1 <> BKy P2).

Definition OtherAfterMoveBlackKing N (P1 P2: Position N) :=
  WKx P2 = WKx P1 /\ WKy P2 = WKy P1 /\ WRx P2 = WRx P1 /\ WRy P2 = WRy P1.

Definition LegalBlackMove N (P1 P2: Position N) :=
  MoveBlackKing P1 P2 /\
  OtherAfterMoveBlackKing P1 P2 /\
  Turn P1 = Black /\
  Turn P2 = White /\
  LegalPosition P1 /\
  LegalPosition P2.

Definition Checkmate N (P: Position N) :=
  LegalPosition P /\ BlackKingAttacked P /\ Turn P = Black /\ forall P': Position N, ~ LegalBlackMove P P'.

Definition Stalemate N (P: Position N) :=
  LegalPosition P /\ ~ BlackKingAttacked P /\ Turn P = Black /\ forall P': Position N, ~ LegalBlackMove P P'.

Definition InsufficientMaterial N (P: Position N) :=
  LegalPosition P /\ Turn P = White /\ BKx P = WRx P /\ BKy P = WRy P.

Definition Draw N (P: Position N) := InsufficientMaterial P \/ Stalemate P.

Inductive BlackLoss N: Position N -> nat -> Prop :=
  | black_lost: forall P, Checkmate P -> BlackLoss P 0
  | black_lost_S: forall P n, (forall P', LegalBlackMove P P' -> exists m, WhiteWin P' m /\ m <= n) ->
                  (exists P', LegalBlackMove P P' /\ WhiteWin P' n) -> BlackLoss P (S n)
with
WhiteWin N: Position N -> nat -> Prop :=
  | white_win: forall P n, (exists P', LegalWhiteMove P P' /\ BlackLoss P' n) -> (~ InsufficientMaterial P) -> WhiteWin P (S n).
