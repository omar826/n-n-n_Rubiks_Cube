--import Mathlib (cannot do this due to name clashes)
import Mathlib.Data.ZMod.Defs
import Rubik.Equiv
import Rubik.Orientation

namespace Orientation

/-- A corner piece is an ordered triple of pairwise adjacent orientations, oriented as the standard
basis.

Since we identify colors and orientations, there's two possible ways to think of this type:

- The position of a corner piece within a Rubik's cube, specified by its face, followed by its
  relative orientation with respect to it. For instance, `CornerPiece.mk U B L` is the upper piece
  in the upper-back-left corner.
- A corner piece with a particular color, within a particular corner. For instance,
  `CornerPiece.mk U B L` is the white piece of the white-blue-orange edge.

The type `PRubik` contains a `Perm CornerPiece` field, which assigns to each corner piece position
in the cube a particular sticker. -/
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

#check Finset
#check Multiset
#check Multiset.Nodup
#check IsAdjacent₃.ne

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

/-- An edge piece is an ordered pair of adjacent orientations.

Since we identify colors and orientations, there's two possible ways to think of this structure:

- The position of an edge piece within a Rubik's cube, specified by its face, followed by its
  relative orientation with respect to it. For instance, `EdgePiece.mk U B` is the upper piece in
  the upper-back edge.
- An edge piece with a particular color, within a particular edge. For instance,
  `EdgePiece.mk U B` is the white piece of the white-blue edge.

The type `PRubik` contains a `Perm EdgePiece` field, which assigns to each edge piece position in
the cube a particular sticker. -/
structure EdgePiece where
  n : ℕ
  h : n ≥ 3
  fst : Orientation
  snd : Orientation
  isAdjacent : IsAdjacent fst snd
  index : Fin (n - 2)

namespace EdgePiece

/-- Constructs the finset containing the edge's orientations. -/
def toFinset (e : EdgePiece) : Finset Orientation :=
  ⟨{e.fst, e.snd}, by
    have h : e.fst ≠ e.snd := e.isAdjacent.ne
    simp [h]⟩

/-- Constructs the other edge piece sharing an edge and index. -/
def flip (e : EdgePiece) : EdgePiece :=
  ⟨e.n, e.h, _, _, e.isAdjacent.symm, e.index⟩

instance : Setoid EdgePiece where
  r e₁ e₂ := e₁.toFinset = e₂.toFinset
  iseqv := by
    constructor
    · intro x
      rfl
    · exact Eq.symm
    · exact Eq.trans

end EdgePiece

/-- Identifies edge pieces in an edge. -/
def Edge : Type := Quotient EdgePiece.instSetoid

/-- The edges of concentric squares of centre pieces. Note that such
concentric squares contain edges only when the side length of the square
is atleast 3.

These pieces are defined by the side length of the square it belongs to,
their color, as well an index.
TODO: How do we exactly index? -/
structure CentreSquareEdge (n : ℕ) where
  h : n ≥ 5
  k : Fin (n - 4) -- side length - 2
  h₂ : k % 2 = n % 2
  face : Orientation
  index : Fin (4 * (k - 2))

/-- The corners of concentric squares of centre pieces. Note that such
concentric squares contain corners only when the sidelength of the square
is atleast 2.

These pieces are define by the side length of the square it belongs to,
their color, as well as an index ranging from 0 to 3. -/
structure CentreSquareCorner (n : ℕ) where
  h : n ≥ 4
  k : Fin (n - 3) -- side length - 2
  h₂ : k % 2 = n % 2
  face : Orientation
  index : Fin 4

end Orientation
