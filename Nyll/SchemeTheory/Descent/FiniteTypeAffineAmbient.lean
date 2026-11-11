/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.ChowDatum
public import Nyll.SchemeTheory.ProjectiveSpace.FinitePresentation

/-!
# A finite-presentation ambient scheme for an affine finite-type scheme

The existing affine chart in Chow's construction already gives the
required closed immersion. Its target is a standard affine open of
projective space, hence is separated and of finite presentation over the
original base ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs.ChowDatum_nonempty.AlgebraicGeometry.ChowLemma

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual affine finite-type scheme over an arbitrary ring embeds as
a closed subscheme of an affine scheme of finite presentation over that ring. -/
theorem exists_affine_finitePresentation_ambient
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)),
      IsAffine Y ∧ IsClosedImmersion i ∧ LocallyOfFinitePresentation g ∧ i ≫ g = f := by
  let U : X.Opens := ⊤
  have hU : IsAffineOpen U := isAffineOpen_top X
  let n := chartN f U hU
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  let V := Proj.basicOpen 𝒜 (MvPolynomial.X (0 : Fin (n + 1)))
  have hdeg : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R) ∈
      𝒜 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R _)
  have : IsAffine V.toScheme := Proj.isAffineOpen_basicOpen 𝒜 _ hdeg one_pos
  let j : U.toScheme ⟶ V.toScheme := chartJD f U hU
  have : IsClosedImmersion j := chartJD_closed f U hU
  let i : X ⟶ V.toScheme := X.topIso.inv ≫ j
  let g : V.toScheme ⟶ Spec (CommRingCat.of R) := V.ι ≫ ProjSpace.π R n
  refine ⟨V.toScheme, i, g, inferInstance, inferInstance, inferInstance, ?_⟩
  change (X.topIso.inv ≫ chartJD f U hU) ≫ (V.ι ≫ ProjSpace.π R n) = f
  rw [Category.assoc, ← Category.assoc (chartJD f U hU), chartJD_ι,
    chartJ_over, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]

end AlgebraicGeometry
