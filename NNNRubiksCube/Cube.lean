-- import Mathlib (cannot do this due to name clashes)
import NNNRubiksCube.Piece

open Orientation Equiv

/-- Permutations of pieces in an big Rubik's cube (n ≥ 5). -/
structure BigRubik (n : {m : ℕ // m ≥ 5}) where
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Perm (EdgePiece ⟨n.val, by omega⟩)
  /-- Returns the centre square edge at a given location -/
  centreSquareEdgeEquiv : Perm (CentreSquareEdge ⟨n.val, by omega⟩)
  /-- Returns the centre square corner at a given location -/
  centreSquareCornerEquiv : Perm (CentreSquareCorner ⟨n.val, by omega⟩)
  /-- Pieces in the same edge get mapped to pieces in the same edge. -/
  edge_flip (e : (EdgePiece ⟨n.val, by omega⟩)) : edgePieceEquiv e.flip = (edgePieceEquiv e).flip
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic
  /-- Pieces in the same centre square get mapped to pieces in the same centre square -/
  centre_square_corner_square (e : CentreSquareEdge ⟨n.val, by omega⟩) : (centreSquareEdgeEquiv e).k = e.k
  centre_square_edge_square (c : CentreSquareCorner ⟨n.val, by omega⟩) : (centreSquareCornerEquiv c).k = c.k

/-- Permutations of pieces in 4×4×4 Rubik's cube. -/
structure FourRubik where
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Perm (EdgePiece ⟨4, by decide⟩)
  /-- Returns the centre square corner at a given location -/
  centreSquareCornerEquiv : Perm (CentreSquareCorner ⟨4, by decide⟩)
  /-- Pieces in the same edge get mapped to pieces in the same edge. -/
  edge_flip (e : (EdgePiece ⟨4, by decide⟩)) : edgePieceEquiv e.flip = (edgePieceEquiv e).flip
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic
  /-- Pieces in the same centre square get mapped to pieces in the same centre square -/
  centre_square_edge_square (c : CentreSquareCorner ⟨4, by decide⟩) :(centreSquareCornerEquiv c).k = c.k

/-- Permutations of pieces in 3×3×3 Rubik's cube. -/
structure ThreeRubik where
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Perm (EdgePiece ⟨3, by decide⟩)
  /-- Pieces in the same edge get mapped to pieces in the same edge. -/
  edge_flip (e : (EdgePiece ⟨3, by decide⟩)) : edgePieceEquiv e.flip = (edgePieceEquiv e).flip
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic

/-- Permutations of pieces in 2×2×2 Rubik's cube. -/
structure TwoRubik where
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic
