/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.RelEffCartierDiv
import Nyll.SchemeTheory.Affine.FiniteSchemeAlgebra
import Nyll.SchemeTheory.Affine.WeilRestriction.ProjectiveUnitDimension
import Nyll.SchemeTheory.Affine.WeilRestriction.ProjectiveUnitGeometric
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The affine scalar-unit quotient of an actual modulus

The algebra is the global sections of the whole divisor subscheme. Its
dimension is proved to be the finite flat degree of that divisor. For
positive degree, a basis of this actual algebra constructs the smooth,
geometrically connected affine group scheme representing its fppf scalar
quotient, with relative dimension `degree - 1`.

The exact-sequence identification with the kernel of a generalized Jacobian
still requires the construction and classification of that Jacobian.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open SchemeTheory.Affine

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}

/-- Global sections of the entire finite modulus, with its actual base-field action. -/
abbrev modulusAlgebra (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) :
    CommAlgCat.{u} K :=
  FiniteScheme.coordinateAlgebra
    (D.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K))))

/-- The weighted divisor degree is the dimension of the actual modulus algebra. -/
theorem finrank_modulusAlgebra
    (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) :
    Module.finrank K (modulusAlgebra D) = d := by
  have : IsFinite (D.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K)))) :=
    D.isFinite
  have : Flat (D.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K)))) := D.flat
  exact (FiniteScheme.finrank_coordinateAlgebra
    (D.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K))))).trans
      (D.finrank_eq (IsLocalRing.closedPoint K))

/-- A basis is supplied by finiteness of the actual divisor morphism and the
proved rank formula, without an extra freeness or dimension hypothesis. -/
def modulusBasis (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) :
    Basis (Fin d) K (modulusAlgebra D) := by
  let : IsFinite (D.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K)))) :=
    D.isFinite
  exact Module.finBasisOfFinrankEq K (modulusAlgebra D) (finrank_modulusAlgebra D)

/-- The same actual algebra basis in positive-rank projective coordinates. -/
def positiveModulusBasis
    (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d) :
    Basis (Fin (d - 1 + 1)) K (modulusAlgebra D) :=
  (modulusBasis D).reindex (finCongr (Nat.sub_add_cancel (Nat.succ_le_of_lt hd)).symm)

/-- The actual group scheme of modulus units modulo scalars. -/
def modulusUnitQuotient
    (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d) :
    CommGrp (Over (Spec (CommRingCat.of K))) :=
  ScalarQuotientSchemePresheaf.scalarQuotientCommGroupScheme (positiveModulusBasis D hd)

/-- The group scheme represents the actual fppf sheafification of tensor
units of the modulus algebra modulo scalar units on all test schemes. -/
def modulusUnitQuotientRepresentable
    (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d) :
    ((ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (modulusUnitQuotient D hd).X :=
  ScalarQuotientSchemePresheaf.scalarQuotientRepresentable (positiveModulusBasis D hd)

/-- The constructed group has an affine carrier. -/
theorem isAffine_modulusUnitQuotient
    (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d) :
    IsAffine (modulusUnitQuotient D hd).X.left := by
  change IsAffine (ProjectiveUnitOpen.carrier (positiveModulusBasis D hd))
  infer_instance

/-- Its relative dimension is the full divisor degree minus one. -/
theorem smoothOfRelativeDimension_modulusUnitQuotient
    (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d) :
    SmoothOfRelativeDimension (d - 1) (modulusUnitQuotient D hd).X.hom :=
  ScalarQuotientSchemePresheaf.smoothOfRelativeDimension_scalarQuotientCommGroupScheme
    (positiveModulusBasis D hd)

/-- The quotient constructed from the full modulus is geometrically connected. -/
theorem geometricallyConnected_modulusUnitQuotient
    (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d) :
    GeometricallyConnected (modulusUnitQuotient D hd).X.hom :=
  ScalarQuotientSchemePresheaf.geometricallyConnected_scalarQuotientCommGroupScheme
    (positiveModulusBasis D hd)

end AlgebraicGeometry.GeneralizedJacobian
