/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.UnitNormPolynomial
import Nyll.SchemeTheory.ProjectiveSpace.Smooth
import Nyll.SchemeTheory.Modules.Frames.ProjectivePresentationFromFrames

/-!
# The projective norm open of a finite free algebra

For an algebra of positive rank, the homogeneous norm defines an affine
open in projective space. This open is smooth over the base. The affine
unit open maps to it, and that map is invariant under multiplication by
units of the test algebra.

These constructions supply the carrier and the invariant map for the
scalar quotient. The fppf quotient universal property, including points
with a nontrivial scalar line bundle, is a separate assertion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Module HomogeneousLocalization
open AlgebraicCurves.Geometry.Sheaves.Proofs.ProjectivePresentation.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

namespace SchemeTheory.Affine.ProjectiveUnitOpen

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The determinant belongs to the positive homogeneous component given
by the rank, without reducedness or field hypotheses. -/
theorem norm_mem : UnitNormPolynomial.normPolynomial b ∈ 𝒜 (n + 1) := by
  apply (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
  simpa only [Fintype.card_fin] using UnitNormPolynomial.normPolynomial_homogeneous b

/-- The degree-zero part of the localization by the homogeneous norm. -/
abbrev CoordinateRing := Away 𝒜 (UnitNormPolynomial.normPolynomial b)

instance coordinateRingAlgebra : Algebra R (CoordinateRing b) :=
  ((HomogeneousLocalization.fromZeroRingHom 𝒜 _).comp
    (ProjSpace.grad0Equiv R n).toRingHom).toAlgebra

/-- The affine projective open on which the homogeneous norm is invertible. -/
abbrev carrier : Scheme := Spec (CommRingCat.of (CoordinateRing b))

/-- The inclusion of the norm open into the projectivized underlying module. -/
def projectiveι : carrier b ⟶ Proj 𝒜 :=
  Proj.awayι 𝒜 (UnitNormPolynomial.normPolynomial b) (norm_mem b) (Nat.succ_pos n)

instance : IsOpenImmersion (projectiveι b) := by
  dsimp [projectiveι]
  infer_instance

/-- The structure morphism of the projective norm open. -/
def toBase : carrier b ⟶ Spec (CommRingCat.of R) :=
  projectiveι b ≫ ProjSpace.π R n

/-- The structure map is induced by the coefficient algebra structure on
the degree-zero localization. -/
theorem toBase_eq : toBase b =
    Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing b))) := by
  unfold toBase projectiveι ProjSpace.π
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The actual projective norm open is smooth over the coefficient ring. -/
theorem smooth_toBase : Smooth (toBase b) := by
  have : Smooth (ProjSpace.π R n) := ProjSpace.smooth_π R n
  dsimp [toBase]
  infer_instance

/-- The map from units to their projective class, induced by the inclusion
of degree-zero fractions into the full norm localization. -/
def quotientMap : UnitNormPolynomial.unitOpen b ⟶ carrier b :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (CoordinateRing b) (UnitNormPolynomial.CoordinateRing b)))

/-- The projective-class map is a morphism over the coefficient spectrum. -/
theorem quotientMap_toBase :
    quotientMap b ≫ toBase b = UnitNormPolynomial.unitOpenToBase b := by
  rw [toBase_eq]
  unfold quotientMap UnitNormPolynomial.unitOpenToBase
  rw [← Spec.map_comp]
  congr 1

variable {S : Type u} [CommRing S] [Algebra R S]

/-- Multiplication by a scalar unit in the finite free algebra after base change. -/
def scalarMul (r : Sˣ) (a : (S ⊗[R] A)ˣ) : (S ⊗[R] A)ˣ :=
  Units.map (algebraMap S (S ⊗[R] A)).toMonoidHom r * a

/-- Coordinates transform linearly under scalar multiplication. -/
theorem coordinates_scalarMul (r : Sˣ) (a : (S ⊗[R] A)ˣ) :
    UnitNormPolynomial.coordinates b (scalarMul r a : S ⊗[R] A) =
      fun i => (r : S) * UnitNormPolynomial.coordinates b (a : S ⊗[R] A) i := by
  funext i
  change (Algebra.TensorProduct.basis S b).repr
      (algebraMap S (S ⊗[R] A) (r : S) * (a : S ⊗[R] A)) i = _
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rfl

/-- Evaluation of a homogeneous polynomial at the coordinates of a scalar
multiple acquires precisely the scalar to its homogeneous degree. -/
theorem aeval_scalarMul (r : Sˣ) (a : (S ⊗[R] A)ˣ)
    {p : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval
        (UnitNormPolynomial.coordinates b (scalarMul r a : S ⊗[R] A)) p =
      (r : S) ^ d * MvPolynomial.aeval
        (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) p := by
  rw [coordinates_scalarMul]
  exact LinSys.eval₂_mul_of_isHomogeneous (algebraMap R S)
      (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) (r : S) hp

/-- The ring map of the projective norm open associated to an actual unit. -/
def projectivePoint (a : (S ⊗[R] A)ˣ) : CoordinateRing b →+* S :=
  (UnitNormPolynomial.unitToHom b a).toRingHom.comp
    (algebraMap (CoordinateRing b) (UnitNormPolynomial.CoordinateRing b))

/-- The numerator-denominator identity for evaluation of a homogeneous
fraction at a unit; both polynomials have the same degree. -/
theorem projectivePoint_fraction (a : (S ⊗[R] A)ˣ) (z : CoordinateRing b) :
    MvPolynomial.aeval (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) z.den *
        projectivePoint b a z =
      MvPolynomial.aeval (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) z.num := by
  have h := congrArg (UnitNormPolynomial.unitToHom b a) z.den_smul_val
  rw [Algebra.smul_def, map_mul, UnitNormPolynomial.unitToHom_algebraMap,
    UnitNormPolynomial.unitToHom_algebraMap] at h
  exact h

/-- Every denominator of a homogeneous norm fraction evaluates to a unit. -/
theorem isUnit_aeval_den (a : (S ⊗[R] A)ˣ) (z : CoordinateRing b) :
    IsUnit (MvPolynomial.aeval
      (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) z.den) := by
  rw [← UnitNormPolynomial.unitToHom_algebraMap b a z.den]
  exact (IsLocalization.map_units (UnitNormPolynomial.CoordinateRing b)
    (⟨z.den, z.den_mem⟩ : Submonoid.powers (UnitNormPolynomial.normPolynomial b))).map
      (UnitNormPolynomial.unitToHom b a)

/-- The projective-class map really is invariant under scalar units over
every test algebra, including nonreduced ones. -/
theorem projectivePoint_scalarMul (r : Sˣ) (a : (S ⊗[R] A)ˣ) :
    projectivePoint b (scalarMul r a) = projectivePoint b a := by
  apply RingHom.ext
  intro z
  apply (isUnit_aeval_den b a z).mul_left_cancel
  apply (r.isUnit.pow z.deg).mul_left_cancel
  have h := projectivePoint_fraction b (scalarMul r a) z
  rw [aeval_scalarMul b r a ((MvPolynomial.mem_homogeneousSubmodule _ _).mp z.den_mem_deg),
    aeval_scalarMul b r a ((MvPolynomial.mem_homogeneousSubmodule _ _).mp z.num_mem_deg),
    mul_assoc] at h
  rw [projectivePoint_fraction]
  exact h

end SchemeTheory.Affine.ProjectiveUnitOpen
