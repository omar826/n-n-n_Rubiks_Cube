-- import Mathlib (cannot do this due to name clashes)
import NNNRubiksCube.Piece

open Orientation Equiv

/-- Permutations of pieces in 4×4×4 Rubik's cube. -/
structure FourIllegalRubik where
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
  centre_square_corner_square (c : CentreSquareCorner ⟨4, by decide⟩) :(centreSquareCornerEquiv c).k = c.k

namespace FourIllegalRubik

/-- The solved 4×4×4 Rubik's cube. -/
instance : One FourIllegalRubik where
  one := ⟨1, 1, 1, by simp, by simp, by simp⟩

instance : Inhabited FourIllegalRubik where
  default := 1

/-- The product of two 4×4×4 Rubik's cubes is the 4×4×4 Rubik's cube where the first's scramble is
performed before the second's. -/
instance : Mul FourIllegalRubik :=
  ⟨fun cube₁ cube₂ ↦ by
    refine ⟨cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv,
      cube₁.edgePieceEquiv * cube₂.edgePieceEquiv,
      cube₁.centreSquareCornerEquiv * cube₂.centreSquareCornerEquiv,
      fun e ↦ ?_, fun c ↦ ?_, fun csc ↦ ?_⟩
    · simp [cube₁.edge_flip, cube₂.edge_flip]
    · simp [cube₁.corner_cyclic, cube₂.corner_cyclic]
    · simp [cube₁.centre_square_corner_square, cube₂.centre_square_corner_square]⟩

end FourIllegalRubik
