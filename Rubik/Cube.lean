-- import Mathlib (cannot do this due to name clashes)
import Rubik.Piece

open Orientation Equiv

/-- Permutations of pieces in an odd Rubik's cube. -/
structure AllOddRubik (n : ℕ) where
  h : n % 2 = 1 ∧ n ≥ 3
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Perm EdgePiece
  /-- Returns the centre square edge at a given location -/
  centreSquareEdgeEquiv : Perm (CentreSquareEdge n)
  /-- Returns the centre square corner at a given location -/
  centreSquareCornerEquiv : Perm (CentreSquareCorner n)
  /-- Pieces in the same edge get mapped to pieces in the same edge. -/
  edge_flip (e : EdgePiece) : edgePieceEquiv e.flip = (edgePieceEquiv e).flip
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic
  /-- Pieces in the same centre square get mapped to pieces in the
  same centre square -/
  centre_square_corner_square (e : CentreSquareEdge n) :
  (centreSquareEdgeEquiv e).k = e.k
  centre_square_edge_square (c : CentreSquareCorner n) :
  (centreSquareCornerEquiv c).k = c.k
