--import Mathlib (cannot do this due to name clashes)
import Rubik.Orientation

namespace Orientation

/- A corner piece consists of three stickers, each defined by pairwise adjacent orientations. Equivalent corner pieces will be identified later. -/
structure CornerPiece where
  fst : Orientation
  snd : Orientation
  thd : Orientation
  isAdjacent₃ : IsAdjacent₃ fst snd thd

/-- Constructs the finset containing the corner's orientations. -/
def toFinset (e : CornerPiece) : Finset Orientation :=
  ⟨{e.fst, e.snd, e.thd}, by
    obtain ⟨h₁, h₂, h₃⟩ := e.isAdjacent₃.ne
    simpa using ⟨⟨h₁, h₃.symm⟩, h₂⟩⟩

#check Finset
#check Multiset
#check Multiset.Nodup
#check IsAdjacent₃.ne
