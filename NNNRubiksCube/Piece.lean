--import Mathlib (cannot do this due to name clashes)
import Mathlib.Data.ZMod.Defs
import NNNRubiksCube.Equiv
import NNNRubiksCube.Orientation

namespace Orientation

/-- A corner piece is an ordered triple of pairwise adjacent orientations, oriented as the standard
basis. -/
structure CornerPiece where
  fst : Orientation
  snd : Orientation
  thd : Orientation
  isAdjacent₃ : IsAdjacent₃ fst snd thd

namespace CornerPiece

/-- Constructs the finset containing the corner's orientations. -/
def toFinset (e : CornerPiece) : Finset Orientation :=
  ⟨{e.fst, e.snd, e.thd}, by
    have ⟨h₁, h₂, h₃⟩ := e.isAdjacent₃.ne
    simp [h₁, h₂, h₃.symm]⟩

/-- Permutes the colors in a corner cyclically. -/
def cyclic (c : CornerPiece) : CornerPiece :=
  ⟨_, _, _, c.isAdjacent₃.cyclic⟩

/-- Returns the unique corner piece sharing a corner, with the
orientation of the given axis. -/
def withAxis (c : CornerPiece) (a : Axis) : CornerPiece :=
  if c.fst.axis = a then c
  else if c.snd.axis = a then c.cyclic
  else c.cyclic.cyclic

/-- The "value" of a corner piece is the number of **counterclockwise**
rotations needed to orient a specific face towards its corresponding axis. -/
def value (c : CornerPiece) (a : Axis) : ZMod 3 :=
  if c.fst.axis = a then 0 else if c.thd.axis = a then 1 else 2

instance : Setoid CornerPiece where
  r c₁ c₂ := c₁.toFinset = c₂.toFinset
  iseqv := by
    constructor
    · intro x
      rfl
    · exact Eq.symm
    · exact Eq.trans

end CornerPiece

/-- Identifies corner pieces in a corner. -/
def Corner : Type := Quotient CornerPiece.instSetoid

#check Quotient

/-- An edge piece is an ordered pair of adjacent orientations along with an index. -/
structure EdgePiece (n : {m : ℕ // m ≥ 3}) where
  fst : Orientation
  snd : Orientation
  isAdjacent : IsAdjacent fst snd
  index : Fin (n.val - 2)

namespace EdgePiece

/-- Constructs the finset containing the edge's orientations. -/
def toFinset {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) : Finset Orientation :=
  ⟨{e.fst, e.snd}, by
    have h : e.fst ≠ e.snd := e.isAdjacent.ne
    simp [h]⟩

/-- Constructs the other edge piece sharing an edge and index. -/
def flip {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) : EdgePiece n :=
  ⟨_, _, e.isAdjacent.symm, e.index⟩

instance (n : {m : ℕ // m ≥ 3}): Setoid (EdgePiece n) where
  r e₁ e₂ := e₁.toFinset = e₂.toFinset
  iseqv := by
    constructor
    · intro x
      rfl
    · exact Eq.symm
    · exact Eq.trans

end EdgePiece

/-- Identifies edge pieces in an edge. -/
def Edge (n: {m : ℕ // m ≥ 3}) : Type := Quotient (EdgePiece.instSetoid n)

/-- The edges of concentric squares of centre pieces. Note that such
concentric squares contain edges only when the side length of the square
is atleast 3 (which requires n atleast 5).

These pieces are defined by the side length of the square it belongs to,
their color, as well an index.
TODO: How do we exactly index? -/
structure CentreSquareEdge (n : {m : ℕ // m ≥ 5}) where
  k : Fin (n - 4) -- side length - 3
  h₂ : k.val % 2 = n % 2 -- parity condition
  face : Orientation
  index : Fin (4 * (k.val + 1))

/-- The corners of concentric squares of centre pieces. Note that such
concentric squares contain corners only when the sidelength of the square
is atleast 2 (which requires n atleast 4).

These pieces are define by the side length of the square it belongs to,
their color, as well as an index ranging from 0 to 3. -/
structure CentreSquareCorner (n : {m : ℕ // m ≥ 4}) where
  k : Fin (n - 3) -- side length - 2
  h₂ : k.val % 2 = n % 2
  face : Orientation
  index : Fin 4

end Orientation
