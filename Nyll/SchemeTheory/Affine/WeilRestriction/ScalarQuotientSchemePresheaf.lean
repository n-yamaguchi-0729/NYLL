/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientPresheaf
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# The scalar quotient presheaf on all schemes

The actual scalar quotient of tensor-algebra units is evaluated on global
sections of every scheme over the coefficient spectrum. The affine
Gamma--Spec adjunction sends its invariant projective point to a morphism
to the projective norm open. This construction is natural on all test
schemes, including nonaffine test schemes.

The universe lift only prepares this genuine group presheaf for ordinary
sheafification on the big site. Local bijectivity and sheaf representation
are proved separately.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Module
open scoped TensorProduct

universe u

namespace SchemeTheory.Affine.ScalarQuotientPresheaf

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A S T : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
  [Algebra R A] [Algebra R S] [Algebra R T]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The concrete norm-open homomorphism commutes with change of test algebra. -/
theorem unitToHom_unitMap (g : S →ₐ[R] T) (a : (S ⊗[R] A)ˣ) :
    UnitNormPolynomial.unitToHom b (unitMap g a) =
      g.comp (UnitNormPolynomial.unitToHom b a) := by
  apply (UnitNormPolynomial.homEquivUnits b).injective
  rw [UnitNormPolynomial.homEquivUnits_comp]
  change UnitNormPolynomial.homToUnit b
      (UnitNormPolynomial.unitToHom b (unitMap g a)) =
    unitMap g (UnitNormPolynomial.homToUnit b (UnitNormPolynomial.unitToHom b a))
  rw [UnitNormPolynomial.homToUnit_unitToHom, UnitNormPolynomial.homToUnit_unitToHom]

/-- The projective point of a unit is natural in the coefficient algebra. -/
theorem projectivePointAlgHom_unitMap (g : S →ₐ[R] T) (a : (S ⊗[R] A)ˣ) :
    projectivePointAlgHom b (unitMap g a) = g.comp (projectivePointAlgHom b a) := by
  apply AlgHom.ext
  intro x
  change UnitNormPolynomial.unitToHom b (unitMap g a)
      (algebraMap (ProjectiveUnitOpen.CoordinateRing b)
        (UnitNormPolynomial.CoordinateRing b) x) =
    g (UnitNormPolynomial.unitToHom b a
      (algebraMap (ProjectiveUnitOpen.CoordinateRing b)
        (UnitNormPolynomial.CoordinateRing b) x))
  rw [unitToHom_unitMap]
  rfl

/-- The actual scalar quotient maps naturally to the projective norm open. -/
theorem quotientPoint_quotientMap (g : S →ₐ[R] T)
    (q : ScalarQuotient (R := R) (A := A) (S := S)) :
    quotientPoint b (quotientMap g q) = g.comp (quotientPoint b q) := by
  refine QuotientGroup.induction_on q fun a => ?_
  exact projectivePointAlgHom_unitMap b g a

end SchemeTheory.Affine.ScalarQuotientPresheaf

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

/-- Global sections with their coefficient algebra structure supplied by
the relative Gamma functor, for an arbitrary test scheme. -/
abbrev sectionsAlgebra (T : Over (Spec (CommRingCat.of R))) : CommAlgCat.{u} R :=
  ((AlgebraicGeometry.algΓ (CommRingCat.of R)).obj T).unop

variable {R}

/-- Pullback of global sections as a coefficient-algebra homomorphism. -/
abbrev sectionsMap {T T' : Over (Spec (CommRingCat.of R))} (f : T ⟶ T') :
    sectionsAlgebra R T' →ₐ[R] sectionsAlgebra R T :=
  ((AlgebraicGeometry.algΓ (CommRingCat.of R)).map f).unop.hom

/-- The relative Gamma--Spec adjunction, expressed directly in algebra maps. -/
def affinePointEquiv (B : CommAlgCat.{u} R) (T : Over (Spec (CommRingCat.of R))) :
    (B →ₐ[R] sectionsAlgebra R T) ≃
      (T ⟶ (AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op B)) where
  toFun f := (AlgebraicGeometry.algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv
    T (op B) (CommAlgCat.ofHom f).op
  invFun f :=
    (((AlgebraicGeometry.algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv
      T (op B)).symm f).unop.hom
  left_inv f := congrArg
    (fun g : (AlgebraicGeometry.algΓ (CommRingCat.of R)).obj T ⟶ op B => g.unop.hom)
    (((AlgebraicGeometry.algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv
      T (op B)).symm_apply_apply (CommAlgCat.ofHom f).op)
  right_inv f :=
    ((AlgebraicGeometry.algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv
      T (op B)).apply_symm_apply f

/-- Source naturality, without unfolding the Gamma functor. -/
theorem affinePointEquiv_comp (B : CommAlgCat.{u} R)
    {T T' : Over (Spec (CommRingCat.of R))}
    (g : T' ⟶ T) (f : B →ₐ[R] sectionsAlgebra R T) :
    affinePointEquiv B T' ((sectionsMap g).comp f) = g ≫ affinePointEquiv B T f :=
  (AlgebraicGeometry.algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv_naturality_left
    g (CommAlgCat.ofHom f).op

/-- Target naturality, directly in the homomorphism of coordinate algebras. -/
theorem affinePointEquiv_postcomp {B B' : CommAlgCat.{u} R}
    (T : Over (Spec (CommRingCat.of R)))
    (f : B' →ₐ[R] sectionsAlgebra R T) (g : B →ₐ[R] B') :
    affinePointEquiv B T (f.comp g) = affinePointEquiv B' T f ≫
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op :=
  (AlgebraicGeometry.algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv_naturality_right
    (CommAlgCat.ofHom f).op (CommAlgCat.ofHom g).op

/-- The coordinate-algebra map of a composite with a source morphism. -/
theorem affinePointEquiv_symm_comp (B : CommAlgCat.{u} R)
    {T T' : Over (Spec (CommRingCat.of R))} (g : T' ⟶ T)
    (f : T ⟶ (AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op B)) :
    (affinePointEquiv B T').symm (g ≫ f) =
      (sectionsMap g).comp ((affinePointEquiv B T).symm f) :=
  congrArg
    (fun k : (AlgebraicGeometry.algΓ (CommRingCat.of R)).obj T' ⟶ op B => k.unop.hom)
    ((AlgebraicGeometry.algΓAlgSpecAdjunction
      (CommRingCat.of R)).homEquiv_naturality_left_symm g f)

/-- A factorization through an affine target chart induces the corresponding
factorization of coordinate-algebra maps. -/
theorem affinePointEquiv_symm_postcomp {B B' : CommAlgCat.{u} R}
    {T : Over (Spec (CommRingCat.of R))}
    (f : T ⟶ (AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op B'))
    (g : B →ₐ[R] B') :
    (affinePointEquiv B T).symm
        (f ≫ (AlgebraicGeometry.algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op) =
      ((affinePointEquiv B' T).symm f).comp g :=
  congrArg
    (fun k : (AlgebraicGeometry.algΓ (CommRingCat.of R)).obj T ⟶ op B => k.unop.hom)
    ((AlgebraicGeometry.algΓAlgSpecAdjunction
      (CommRingCat.of R)).homEquiv_naturality_right_symm f (CommAlgCat.ofHom g).op)

variable (R) (A : Type u) [CommRing A] [Algebra R A]

/-- Tensor-algebra units modulo actual scalar units on every test scheme. -/
def groupPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u} :=
  (AlgebraicGeometry.algΓ (CommRingCat.of R)).op ⋙
    (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙
    ScalarQuotientPresheaf.quotientFunctor R A

/-- The same group presheaf in the value universe used for the big site. -/
def liftedGroupPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
  groupPresheaf R A ⋙ CommGrpCat.uliftFunctor.{u + 1, u}

theorem groupPresheaf_map_apply {T T' : Over (Spec (CommRingCat.of R))}
    (f : T' ⟶ T)
    (q : ScalarQuotientPresheaf.ScalarQuotient
      (R := R) (A := A) (S := sectionsAlgebra R T)) :
    (groupPresheaf R A).map f.op q =
      ScalarQuotientPresheaf.quotientMap (sectionsMap f) q := rfl

theorem liftedGroupPresheaf_map_down {T T' : Over (Spec (CommRingCat.of R))}
    (f : T' ⟶ T) (q : (liftedGroupPresheaf R A).obj (op T)) :
    ((liftedGroupPresheaf R A).map f.op q).down =
      ScalarQuotientPresheaf.quotientMap (sectionsMap f) q.down := rfl

variable {R A} {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The actual affine projective norm open as an object over the base. -/
def representingObject : Over (Spec (CommRingCat.of R)) :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).obj
    (op (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)))

theorem representingObject_left :
    (representingObject b).left = ProjectiveUnitOpen.carrier b := rfl

theorem representingObject_hom :
    (representingObject b).hom = ProjectiveUnitOpen.toBase b :=
  (ProjectiveUnitOpen.toBase_eq b).symm

/-- The coordinate-algebra map of an actual scheme-valued projective point. -/
abbrev pointAlgHom {T : Over (Spec (CommRingCat.of R))}
    (f : T ⟶ representingObject b) :
    ProjectiveUnitOpen.CoordinateRing b →ₐ[R] sectionsAlgebra R T :=
  (affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) T).symm f

theorem pointAlgHom_comp {T T' : Over (Spec (CommRingCat.of R))}
    (g : T' ⟶ T) (f : T ⟶ representingObject b) :
    pointAlgHom b (g ≫ f) = (sectionsMap g).comp (pointAlgHom b f) :=
  affinePointEquiv_symm_comp (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) g f

/-- The algebraic invariant point, interpreted as a morphism of test schemes. -/
def comparisonSmall : groupPresheaf R A ⋙ forget CommGrpCat.{u} ⟶
    yoneda.obj (representingObject b) where
  app T := TypeCat.ofHom (fun q =>
    affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) T.unop
      (ScalarQuotientPresheaf.quotientPoint b q))
  naturality {T T'} f := by
    apply ConcreteCategory.hom_ext
    intro q
    change affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) T'.unop
        (ScalarQuotientPresheaf.quotientPoint b
          (ScalarQuotientPresheaf.quotientMap (sectionsMap f.unop) q)) =
      f.unop ≫ affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) T.unop
        (ScalarQuotientPresheaf.quotientPoint b q)
    exact (congrArg
      (affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) T'.unop)
      (ScalarQuotientPresheaf.quotientPoint_quotientMap b (sectionsMap f.unop) q)).trans
      (affinePointEquiv_comp
        (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) f.unop
        (ScalarQuotientPresheaf.quotientPoint b q))

/-- The natural comparison in the universe required for sheafification on
the big relative site. Its target is the actual represented norm open. -/
def comparison : liftedGroupPresheaf R A ⋙ forget CommGrpCat.{u + 1} ⟶
    uliftYoneda.{u + 1}.obj (representingObject b) :=
  Functor.whiskerRight (comparisonSmall b) CategoryTheory.uliftFunctor.{u + 1, u}

theorem comparison_app_down (T : Over (Spec (CommRingCat.of R)))
    (q : (liftedGroupPresheaf R A).obj (op T)) :
    ((comparison b).app (op T) q).down =
      affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) T
        (ScalarQuotientPresheaf.quotientPoint b q.down) := rfl

theorem pointAlgHom_comparison_app (T : Over (Spec (CommRingCat.of R)))
    (q : (liftedGroupPresheaf R A).obj (op T)) :
    pointAlgHom b (((comparison b).app (op T) q).down) =
      ScalarQuotientPresheaf.quotientPoint b q.down :=
  (affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) T).symm_apply_apply
    (ScalarQuotientPresheaf.quotientPoint b q.down)

/-- Equality of a comparison point with a scheme morphism can be checked
by the actual coordinate-algebra map. -/
theorem comparison_app_eq_iff (T : Over (Spec (CommRingCat.of R)))
    (q : (liftedGroupPresheaf R A).obj (op T)) (f : T ⟶ representingObject b) :
    (comparison b).app (op T) q = ULift.up f ↔
      ScalarQuotientPresheaf.quotientPoint b q.down = pointAlgHom b f := by
  constructor
  · intro h
    have hd := congrArg ULift.down h
    have hp := congrArg (pointAlgHom b) hd
    rw [pointAlgHom_comparison_app] at hp
    exact hp
  · intro h
    apply ULift.ext
    apply (affinePointEquiv
      (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) T).symm.injective
    exact (pointAlgHom_comparison_app b T q).trans h

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
