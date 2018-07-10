module ThreeManChess.Engine.Pos

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

minus : Pos.File -> Pos.File
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
