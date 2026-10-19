/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.Units
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The determinant open of the units of a finite free algebra

A finite basis gives a polynomial multiplication matrix. Its determinant is
homogeneous of degree the rank and detects units after every scalar extension.
Localizing the polynomial ring at this determinant constructs an affine open;
its homomorphisms to every test algebra classify actual units of the tensor
product. This construction permits nilpotents in both algebras.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct BigOperators

universe u v

namespace SchemeTheory.Affine.UnitNormPolynomial

variable {R A : Type (max u v)} [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type v} [Fintype ι] [DecidableEq ι] (b : Basis ι R A)

/-- The multiplication matrix of the generic element in the chosen basis. -/
def multiplicationMatrix : Matrix ι ι (MvPolynomial ι R) :=
  fun i j => ∑ k, MvPolynomial.C (b.repr (b k * b j) i) * MvPolynomial.X k

/-- The norm polynomial of the finite free algebra in the chosen basis. -/
def normPolynomial : MvPolynomial ι R := (multiplicationMatrix b).det

omit [DecidableEq ι] in
theorem multiplicationMatrix_homogeneous (i j : ι) :
    (multiplicationMatrix b i j).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- The norm polynomial has degree equal to the size of the basis, in the
homogeneous sense; no domain or reducedness hypothesis is used. -/
theorem normPolynomial_homogeneous :
    (normPolynomial b).IsHomogeneous (Fintype.card ι) := by
  rw [normPolynomial, Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ _
  have hp : (∏ i, multiplicationMatrix b (σ i) i).IsHomogeneous (Fintype.card ι) := by
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
      MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i => multiplicationMatrix b (σ i) i) (fun _ => 1)
      (fun i _ => multiplicationMatrix_homogeneous b (σ i) i)
  simpa only [map_intCast] using hp.C_mul ((Equiv.Perm.sign σ : ℤ) : R)

variable {S T : Type (max u v)} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Reconstruct an element after scalar extension from its coordinates. -/
def element (x : ι → S) : S ⊗[R] A := ∑ i, x i ⊗ₜ[R] b i

/-- Coordinates in the scalar-extended basis. -/
def coordinates (a : S ⊗[R] A) (i : ι) : S :=
  (Algebra.TensorProduct.basis S b).repr a i

omit [DecidableEq ι] in
@[simp]
theorem coordinates_element (x : ι → S) (i : ι) :
    coordinates b (element b x) i = x i := by
  classical
  simp only [coordinates, element, map_sum, Finset.sum_apply',
    Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
    b.repr_self, Finsupp.single_apply, smul_eq_mul, apply_ite, map_one, map_zero,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [DecidableEq ι] in
@[simp]
theorem element_coordinates (a : S ⊗[R] A) : element b (coordinates b a) = a := by
  unfold element coordinates
  calc
    ∑ i, (Algebra.TensorProduct.basis S b).repr a i ⊗ₜ[R] b i =
        ∑ i, (Algebra.TensorProduct.basis S b).repr a i •
          Algebra.TensorProduct.basis S b i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Algebra.TensorProduct.basis_repr_symm_apply' b _ i).symm
    _ = a := (Algebra.TensorProduct.basis S b).sum_repr a

/-- Evaluating the polynomial matrix gives the actual multiplication matrix
over every test algebra. -/
theorem aeval_multiplicationMatrix (x : ι → S) :
    (MvPolynomial.aeval x).mapMatrix (multiplicationMatrix b) =
      Algebra.leftMulMatrix (Algebra.TensorProduct.basis S b) (element b x) := by
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, multiplicationMatrix,
    Algebra.leftMulMatrix_eq_repr_mul, element,
    Algebra.TensorProduct.basis_apply, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, map_sum,
    Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
    Finsupp.mapRange_apply, Finset.sum_apply', map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, mul_one, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- Evaluation of the polynomial norm agrees with the norm of the actual
element in the scalar-extended algebra. -/
theorem aeval_normPolynomial (x : ι → S) :
    MvPolynomial.aeval x (normPolynomial b) = Algebra.norm S (element b x) := by
  rw [normPolynomial, AlgHom.map_det, aeval_multiplicationMatrix,
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis S b)]

/-- The norm polynomial takes the value one at the coordinates of the
identity, even when the algebra has nilpotents. -/
theorem aeval_normPolynomial_one :
    MvPolynomial.aeval (coordinates b (1 : S ⊗[R] A)) (normPolynomial b) = 1 := by
  rw [aeval_normPolynomial, element_coordinates, map_one]

/-- The determinant open classifies units over arbitrary test algebras. -/
theorem isUnit_aeval_normPolynomial_iff (x : ι → S) :
    IsUnit (MvPolynomial.aeval x (normPolynomial b)) ↔ IsUnit (element b x) := by
  have : Module.Free S (S ⊗[R] A) := Module.Free.of_basis (Algebra.TensorProduct.basis S b)
  have : Module.Finite S (S ⊗[R] A) := Module.Finite.of_basis (Algebra.TensorProduct.basis S b)
  rw [aeval_normPolynomial, WeilRestrictionUnits.isUnit_norm_iff]

/-- The explicit coordinate algebra of the principal open where the norm
polynomial is invertible. -/
abbrev CoordinateRing := Localization.Away (normPolynomial b)

/-- The affine unit open in the affine space of the underlying algebra. -/
abbrev unitOpen : Scheme := Spec (CommRingCat.of (CoordinateRing b))

/-- The inclusion of the unit open into the affine coordinate space. -/
def unitOpenι : unitOpen b ⟶ Spec (CommRingCat.of (MvPolynomial ι R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial ι R) (CoordinateRing b)))

instance : IsOpenImmersion (unitOpenι b) := by
  dsimp [unitOpenι]
  infer_instance

/-- The structural map of the affine unit open to the base. -/
def unitOpenToBase : unitOpen b ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing b)))

/-- The units of a finite free algebra form a smooth affine scheme; the
proof uses only polynomial smoothness and localization. -/
theorem smooth_unitOpenToBase : Smooth (unitOpenToBase b) := by
  unfold unitOpenToBase
  rw [HasRingHomProperty.Spec_iff
    (P := fun {X Y : Scheme.{max u v}} (f : X ⟶ Y) => Smooth f)
    (φ := CommRingCat.ofHom (algebraMap R (CoordinateRing b)))]
  change (algebraMap R (CoordinateRing b)).Smooth
  rw [RingHom.smooth_algebraMap]
  have : Algebra.Smooth R (MvPolynomial ι R) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth (MvPolynomial ι R) (CoordinateRing b) :=
    Algebra.Smooth.of_isLocalization_Away (normPolynomial b)
  exact Algebra.Smooth.comp R (MvPolynomial ι R) (CoordinateRing b)

/-- The coordinates supplied by a point of the determinant open. -/
def homCoordinates (f : CoordinateRing b →ₐ[R] S) (i : ι) : S :=
  f (algebraMap (MvPolynomial ι R) (CoordinateRing b) (MvPolynomial.X i))

theorem aeval_homCoordinates (f : CoordinateRing b →ₐ[R] S) (p : MvPolynomial ι R) :
    MvPolynomial.aeval (homCoordinates b f) p =
      f (algebraMap (MvPolynomial ι R) (CoordinateRing b) p) := by
  have h : MvPolynomial.aeval (homCoordinates b f) =
      f.comp (Algebra.algHom R (MvPolynomial ι R) (CoordinateRing b)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, homCoordinates, AlgHom.comp_apply]
    rfl
  exact AlgHom.congr_fun h p

/-- A point of the norm open determines a unit of the scalar-extended
algebra. -/
def homToUnit (f : CoordinateRing b →ₐ[R] S) : (S ⊗[R] A)ˣ :=
  ((isUnit_aeval_normPolynomial_iff b (homCoordinates b f)).mp (by
    rw [aeval_homCoordinates]
    exact (IsLocalization.Away.algebraMap_isUnit (S := CoordinateRing b)
      (normPolynomial b)).map f)).unit

@[simp]
theorem homToUnit_val (f : CoordinateRing b →ₐ[R] S) :
    (homToUnit b f : S ⊗[R] A) = element b (homCoordinates b f) :=
  IsUnit.unit_spec _

/-- The evaluation map defined by a unit of the scalar-extended algebra. -/
def unitToHom (a : (S ⊗[R] A)ˣ) : CoordinateRing b →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (normPolynomial b)
    (f := MvPolynomial.aeval (coordinates b (a : S ⊗[R] A))) (by
      apply (isUnit_aeval_normPolynomial_iff b _).mpr
      rw [element_coordinates]
      exact a.isUnit)

@[simp]
theorem unitToHom_algebraMap (a : (S ⊗[R] A)ˣ) (p : MvPolynomial ι R) :
    unitToHom b a (algebraMap (MvPolynomial ι R) (CoordinateRing b) p) =
      MvPolynomial.aeval (coordinates b (a : S ⊗[R] A)) p :=
  IsLocalization.Away.lift_eq (normPolynomial b)
    (g := (MvPolynomial.aeval (coordinates b (a : S ⊗[R] A))).toRingHom)
    (by
      apply (isUnit_aeval_normPolynomial_iff b _).mpr
      rw [element_coordinates]
      exact a.isUnit) p

@[simp]
theorem homToUnit_unitToHom (a : (S ⊗[R] A)ˣ) :
    homToUnit b (unitToHom b a) = a := by
  apply Units.ext
  have hc : homCoordinates b (unitToHom b a) = coordinates b (a : S ⊗[R] A) := by
    funext i
    unfold homCoordinates
    rw [unitToHom_algebraMap, MvPolynomial.aeval_X]
  rw [homToUnit_val, hc, element_coordinates]

@[simp]
theorem unitToHom_homToUnit (f : CoordinateRing b →ₐ[R] S) :
    unitToHom b (homToUnit b f) = f := by
  apply IsLocalization.algHom_ext (Submonoid.powers (normPolynomial b))
  apply MvPolynomial.algHom_ext
  intro i
  change unitToHom b (homToUnit b f)
      (algebraMap (MvPolynomial ι R) (CoordinateRing b) (MvPolynomial.X i)) = _
  rw [unitToHom_algebraMap, MvPolynomial.aeval_X, homToUnit_val, coordinates_element]
  rfl

/-- The principal norm open represents the units of the finite free algebra
on every commutative test algebra. -/
def homEquivUnits : (CoordinateRing b →ₐ[R] S) ≃ (S ⊗[R] A)ˣ where
  toFun := homToUnit b
  invFun := unitToHom b
  left_inv := unitToHom_homToUnit b
  right_inv := homToUnit_unitToHom b

/-- The affine-open classification is natural in the test algebra. -/
theorem homEquivUnits_comp (f : CoordinateRing b →ₐ[R] S) (g : S →ₐ[R] T) :
    homEquivUnits b (g.comp f) =
      Units.map (Algebra.TensorProduct.map g (AlgHom.id R A)).toRingHom.toMonoidHom
        (homEquivUnits b f) := by
  apply Units.ext
  change (homToUnit b (g.comp f) : T ⊗[R] A) =
    Algebra.TensorProduct.map g (AlgHom.id R A) (homToUnit b f : S ⊗[R] A)
  rw [homToUnit_val, homToUnit_val]
  simp only [element, homCoordinates, map_sum, Algebra.TensorProduct.map_tmul,
    AlgHom.comp_apply, AlgHom.coe_id, id_eq]

/-- The explicit norm-localization algebra corepresents the units functor,
with the classification and naturality above as its universal property. -/
def tensorUnitsCorepresentable :
    (WeilRestrictionUnits.tensorUnitsFunctor R A).CorepresentableBy
      (CommAlgCat.of R (CoordinateRing b)) where
  homEquiv {_} :=
    { toFun := fun f => homEquivUnits b f.hom
      invFun := fun a => CommAlgCat.ofHom (unitToHom b a)
      left_inv := fun f => CommAlgCat.hom_ext (unitToHom_homToUnit b f.hom)
      right_inv := homToUnit_unitToHom b }
  homEquiv_comp g f := homEquivUnits_comp b f.hom g.hom

/-- The concrete determinant-open algebra and the general Weil-restriction
algebra are isomorphic through their classification of the same units functor.
The freeness and finiteness instances can be supplied by the displayed basis. -/
def representingAlgebraIso [Module.Free R A] [Module.Finite R A] :
    CommAlgCat.of R (CoordinateRing b) ≅ WeilRestrictionUnits.unitsRepresentingAlgebra R A :=
  (tensorUnitsCorepresentable b).uniqueUpToIso
    (WeilRestrictionUnits.tensorUnitsCorepresentable R A)

end SchemeTheory.Affine.UnitNormPolynomial
