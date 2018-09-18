module ThreeManChess.Engine.BasicTypes

data NatRange : Nat -> Nat -> Type where
     MkNatRange : (x : Nat) -> LTE n x -> LTE x m -> NatRange n m

data Rank = MostOuter | SecondOuter | MiddleOuter | MiddleInner | SecondInner | MostInner

data Color = White | Gray | Black

next : Color -> Color
next White = Gray
next Gray = Black
next Black = White

prev : Color -> Color
prev a = next $ next a

proofofNextBeingCyclic : (x : Color) -> x = (next (next (next x)))
proofofNextBeingCyclic White = Refl
proofofNextBeingCyclic Gray = Refl
proofofNextBeingCyclic Black = Refl

data SegmentHalf = FirstHalf | SecondHalf

otherSegmHalf : SegmentHalf -> SegmentHalf
otherSegmHalf FirstHalf = SecondHalf
otherSegmHalf SecondHalf = FirstHalf

SegmentQuarter : Type
SegmentQuarter = (SegmentHalf, SegmentHalf)

SegmentEight : Type
SegmentEight = (SegmentHalf, SegmentHalf, SegmentHalf)

File : Type
File = (Color, SegmentEight)

segmFile : Pos.File -> SegmentEight
segmFile (c, x) = x
colorSegm : Pos.File -> Color
colorSegm (c, x) = c

Pos : Type
Pos = (Pos.Rank, Pos.File)

opposite : Pos.File -> Pos.File
opposite (c, (h, q, e)) = ((case h of FirstHalf => next
                                      SecondHalf => prev) c,
                           (otherSegmHalf h, q, e))

minus : File -> File
minus (c, (FirstHalf, FirstHalf, FirstHalf)) =
      (prev c, (SecondHalf, SecondHalf, SecondHalf))
minus (c, (x, y, SecondHalf)) = (c, (x, y, FirstHalf))
minus (c, (x, SecondHalf, FirstHalf)) = (c, (x, FirstHalf, SecondHalf))
minus (c, (SecondHalf, FirstHalf, FirstHalf)) =
      (c, (FirstHalf, SecondHalf, SecondHalf))
mirror : SegmentEight -> SegmentEight
mirror (x, y, z) = (otherSegmHalf x, otherSegmHalf y, otherSegmHalf z)
plus : Pos.File -> Pos.File
plus (c, (SecondHalf, SecondHalf, SecondHalf)) =
      (next c, (FirstHalf, FirstHalf, FirstHalf))
plus (c, (x, y, FirstHalf)) = (c, (x, y, SecondHalf))
plus (c, (x, FirstHalf, SecondHalf)) = (c, (x, SecondHalf, FirstHalf))
plus (c, (FirstHalf, SecondHalf, SecondHalf)) =
      (c, (SecondHalf, FirstHalf, FirstHalf))
provePlusToMinusSegmFile : (x : Pos.File) ->
                           (segmFile (minus (colorSegm x,mirror (segmFile x)))) =
                                     mirror (segmFile (plus x))
provePlusToMinusSegmFile (_, (FirstHalf, FirstHalf, FirstHalf)) = Refl
provePlusToMinusSegmFile (_, (FirstHalf, FirstHalf, SecondHalf)) = Refl
provePlusToMinusSegmFile (_, (FirstHalf, SecondHalf, FirstHalf)) = Refl
provePlusToMinusSegmFile (_, (FirstHalf, SecondHalf, SecondHalf)) = Refl
provePlusToMinusSegmFile (_, (SecondHalf, FirstHalf, FirstHalf)) = Refl
provePlusToMinusSegmFile (_, (SecondHalf, FirstHalf, SecondHalf)) = Refl
provePlusToMinusSegmFile (_, (SecondHalf, SecondHalf, FirstHalf)) = Refl
provePlusToMinusSegmFile (_, (SecondHalf, SecondHalf, SecondHalf)) = Refl
provePlusMinusReduce : (x : Pos.File) -> x = (minus (plus x))
provePlusMinusReduce (_, (FirstHalf, FirstHalf, FirstHalf)) = Refl
provePlusMinusReduce (_, (FirstHalf, FirstHalf, SecondHalf)) = Refl
provePlusMinusReduce (_, (FirstHalf, SecondHalf, FirstHalf)) = Refl
provePlusMinusReduce (_, (FirstHalf, SecondHalf, SecondHalf)) = Refl
provePlusMinusReduce (_, (SecondHalf, FirstHalf, FirstHalf)) = Refl
provePlusMinusReduce (_, (SecondHalf, FirstHalf, SecondHalf)) = Refl
provePlusMinusReduce (_, (SecondHalf, SecondHalf, FirstHalf)) = Refl
provePlusMinusReduce (c, (SecondHalf, SecondHalf, SecondHalf)) = rewrite proofofNextBeingCyclic c in Refl
proveMinusPlusReduce : (x : Pos.File) -> x = (plus (minus x))
proveMinusPlusReduce (c, (FirstHalf, FirstHalf, FirstHalf)) = rewrite proofofNextBeingCyclic c in Refl
proveMinusPlusReduce (_, (FirstHalf, FirstHalf, SecondHalf)) = Refl
proveMinusPlusReduce (_, (FirstHalf, SecondHalf, FirstHalf)) = Refl
proveMinusPlusReduce (_, (FirstHalf, SecondHalf, SecondHalf)) = Refl
proveMinusPlusReduce (_, (SecondHalf, FirstHalf, FirstHalf)) = Refl
proveMinusPlusReduce (_, (SecondHalf, FirstHalf, SecondHalf)) = Refl
proveMinusPlusReduce (_, (SecondHalf, SecondHalf, FirstHalf)) = Refl
proveMinusPlusReduce (_, (SecondHalf, SecondHalf, SecondHalf)) = Refl

inw : Rank -> Rank
inw MostOuter = SecondOuter
inw SecondOuter = MiddleOuter
inw MiddleOuter = MiddleInner
inw MiddleInner = SecondInner
inw SecondInner = MostInner
inw MostInner = MostInner
out : (x : Rank) -> Not (x = MostOuter) -> Rank
out MostInner _ = SecondInner
out SecondInner _ = MiddleInner
out MiddleInner _ = MiddleOuter
out MiddleOuter _ = SecondOuter
out SecondOuter _ = MostOuter
proveInwOutReduce : (x : Rank) -> Not (x = MostInner) -> x = (out (inw x) p)
proveInwOutReduce MostOuter _ = ?inwoutmostouter
proveInwOutReduce SecondOuter _ = ?inwoutsecondouter
proveInwOutReduce MiddleOuter _ = ?inwoutmiddleouter
proveInwOutReduce MiddleInner _ = ?inwoutmiddleinner
proveInwOutReduce SecondInner _ = ?inwoutsecondinner
proveOutInwReduce : (x : Rank) -> (p : Not (x = MostOuter)) -> x = (inw (out x p))
proveOutInwReduce SecondOuter _ = ?outinwsecondouter
proveOutInwReduce MiddleOuter _ = ?outinwmiddleouter
proveOutInwReduce MiddleInner _ = ?outinwmiddleinner
proveOutInwReduce SecondInner _ = ?outinwsecondinner
proveOutInwReduce MostOuter _ = ?outinwmostouter

kfm : SegmentEight
kfm = (SecondHalf, FirstHalf, FirstHalf)

data FilewiseDirection = Pluswards | Minuswards
data RankwiseDirection = Inwards | Outwards
-- type DiagonalDirection = (RankwiseDirection, FilewiseDirection)
DiagonalDirection : RankwiseDirection => Type
DiagonalDirection rd = (rd, FilewiseDirection)