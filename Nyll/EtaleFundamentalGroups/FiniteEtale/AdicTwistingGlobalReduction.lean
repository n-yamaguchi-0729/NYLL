/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPresentation
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedPullbackSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.SchemeTheory.Cohomology.Cech.IntersectionCechVanishing
public import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafGlobalLifting
public import Nyll.SchemeTheory.Cohomology.Sheaves.ReesClosedProjectiveSerre
public import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
public import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorRestrictions
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
public import Nyll.SchemeTheory.Modules.Quasicoherent.DirectImageAlgebraQuasicoherent
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentKernelGlobal
public import Nyll.SchemeTheory.Modules.Sections.KernelSections
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.Modules.Tensor.FiniteFreeSections
public import Nyll.SchemeTheory.ProjectiveSpace.ClosedProjectiveTwistingFrames
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FlatAssociatedGraded
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Uniform global reduction of the actual positive twisting powers

The kernel of the original quotient unit is the actual ideal multiple on
every affine open. For a line bundle the scalar tensor map identifies this
kernel with the original ideal tensor, and the identification commutes
with restriction. Uniform Rees vanishing therefore makes every original
global reduction map surjective after a single twist bound.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- An actual frame makes its section module flat over the original
section ring. No ambient affine presentation is chosen. -/
theorem IsFrameOn.sections_flat {X : Scheme.{u}} {M : X.Modules}
    {U : X.Opens} {t : Γ(M, U)} (ht : IsFrameOn t U) :
    Module.Flat Γ(X, U) Γ(M, U) := by
  let s : Γ(M, U) := M.presheaf.map (homOfLE (le_refl U)).op t
  let a : Γ(X, U) →ₗ[Γ(X, U)] Γ(M, U) := (LinearMap.lsmul Γ(X, U) Γ(M, U)).flip s
  let e : Γ(X, U) ≃ₗ[Γ(X, U)] Γ(M, U) :=
    LinearEquiv.ofBijective a (ht.bijective le_rfl le_rfl)
  exact Module.Flat.of_linearEquiv e.symm

/-- Finite free sums of an actually framed line retain flatness of
the original section module, through the native biproduct comparison. -/
theorem IsFrameOn.finiteFreeTensor_sections_flat
    {X : Scheme.{u}} {L : X.Modules} {U : X.Opens} {t : Γ(L, U)}
    (ht : IsFrameOn t U) (J : Type u) [Finite J] :
    Module.Flat Γ(X, U)
      Γ(tensor (show X.Modules from SheafOfModules.free J) L, U) := by
  have : Fintype J := Fintype.ofFinite J
  let R : CommRingCat.{u} := Γ(X, U)
  let s : Γ(L, U) := L.presheaf.map (homOfLE (le_refl U)).op t
  let a : R →ₗ[R] Γ(L, U) := (LinearMap.lsmul R Γ(L, U)).flip s
  let e : R ≃ₗ[R] Γ(L, U) := LinearEquiv.ofBijective a (ht.bijective le_rfl le_rfl)
  let e₀ := ((moduleSectionsFunctor U).mapIso (finiteFreeTensorIsoBiproduct J L)).toLinearEquiv
  let e₁ := e₀.trans (biproductSectionsEquiv J (fun _ : J => L) U)
  have : Module.Free R (J → R) := Module.Free.of_basis (Pi.basisFun R J)
  exact Module.Flat.of_linearEquiv
    (e₁.trans (LinearEquiv.piCongrRight (fun _ : J => e.symm)))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A) (M : X.Modules) [M.IsQuasicoherent]

/-- The original affine ideal tensor is the kernel of the original
closed-level quotient map whenever the original sections are flat. -/
def levelUnitKernelIdealTensorEquiv (n : ℕ) (U : X.affineOpens)
    [Module.Flat Γ(X, U) Γ(M, U)] :
    (↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] Γ(M, U)) ≃ₗ[Γ(X, U)]
      Γ(kernel (levelPullbackUnit f I M n), U) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let J : Ideal R := (sectionsIdeal f I U) ^ (n + 1)
  let q : M ⟶ levelPullbackModule f I M n := levelPullbackUnit f I M n
  let a : Γ(M, U) →ₗ[R] Γ(levelPullbackModule f I M n, U) :=
    ((moduleSectionsFunctor U).map q).hom
  have hker : a.ker = J • (⊤ : Submodule R Γ(M, U)) := by
    ext x
    exact levelPullbackUnit_app_eq_zero_iff f I M n U x
  let θ : (↥J ⊗[R] Γ(M, U)) →ₗ[R] a.ker :=
    (AdicFlatLayers.idealTensorMap Γ(M, U) J).codRestrict a.ker (fun z => by
      rw [hker]
      exact (AdicFlatLayers.range_idealTensorMap Γ(M, U) J) ▸
        (show AdicFlatLayers.idealTensorMap Γ(M, U) J z ∈
          (AdicFlatLayers.idealTensorMap Γ(M, U) J).range from ⟨z, rfl⟩))
  have hθ : Function.Bijective θ := by
    constructor
    · intro x y h
      exact AdicFlatLayers.idealTensorMap_injective Γ(M, U) J (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ J • (⊤ : Submodule R Γ(M, U)) := hker ▸ x.property
      obtain ⟨z, hz⟩ := (AdicFlatLayers.idealTensorEquiv Γ(M, U) J).surjective ⟨x.val, hx⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change AdicFlatLayers.idealTensorMap Γ(M, U) J z = x.val
      exact congrArg Subtype.val hz
  exact (LinearEquiv.ofBijective θ hθ).trans (kernelSectionsEquiv q U).symm

/-- The comparison uses literal scalar multiplication followed by the
original kernel inclusion. -/
theorem levelUnitKernelIdealTensorEquiv_tmul (n : ℕ) (U : X.affineOpens)
    [Module.Flat Γ(X, U) Γ(M, U)]
    (a : ↥((sectionsIdeal f I U) ^ (n + 1))) (x : Γ(M, U)) :
    (kernel.ι (levelPullbackUnit f I M n)).app U
      (levelUnitKernelIdealTensorEquiv f I M n U (a ⊗ₜ[Γ(X, U)] x)) = a.val • x := by
  exact kernelSectionsEquiv_symm_apply (levelPullbackUnit f I M n) U _

/-- The original ideal tensor comparison respects the native sheaf
restriction, independently of any frames proving flatness. -/
theorem levelUnitKernelIdealTensorEquiv_restriction (n : ℕ)
    (U W : X.affineOpens) (h : (W : X.Opens) ≤ U)
    [Module.Flat Γ(X, U) Γ(M, U)] [Module.Flat Γ(X, W) Γ(M, W)]
    (z : ↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] Γ(M, U)) :
    (kernel (levelPullbackUnit f I M n)).presheaf.map (homOfLE h).op
        (levelUnitKernelIdealTensorEquiv f I M n U z) =
      levelUnitKernelIdealTensorEquiv f I M n W
        (ReesTensor.idealTensorRestriction f I M h (n + 1) z) := by
  let q := levelPullbackUnit f I M n
  let eU := levelUnitKernelIdealTensorEquiv f I M n U
  let eW := levelUnitKernelIdealTensorEquiv f I M n W
  let r : Γ(M, U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(M, W) :=
    M.val.restrictₛₗ (homOfLE h).op
  let rK : Γ(kernel q, U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
      Γ(kernel q, W) :=
    (kernel q).val.restrictₛₗ (homOfLE h).op
  let rT :
      ↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] Γ(M, U)
        →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
      ↥((sectionsIdeal f I W) ^ (n + 1)) ⊗[Γ(X, W)] Γ(M, W) :=
    ReesTensor.idealTensorRestriction f I M h (n + 1)
  change rK (eU z) = eW (rT z)
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    let sectionU : Γ(kernel q, U) :=
      (eU (a ⊗ₜ[Γ(X, U)] x))
    apply (kernelSectionsEquiv q W).injective
    apply Subtype.ext
    have hv := kernelSectionsEquiv_apply q W (rK (eU (a ⊗ₜ[Γ(X, U)] x)))
    have hw := kernelSectionsEquiv_apply q W (eW (rT (a ⊗ₜ[Γ(X, U)] x)))
    have hn := congrArg
      (fun b : Γ(kernel q, U) ⟶ Γ(M, W) =>
        b sectionU)
      ((kernel.ι q).mapPresheaf.naturality (homOfLE h).op)
    apply hv.trans
    apply Eq.trans ?_ hw.symm
    calc
      (kernel.ι q).app W
          ((kernel q).presheaf.map (homOfLE h).op
            sectionU) =
          r ((kernel.ι q).app U
            sectionU) := hn
      _ = r (a.val • x) := congrArg r (levelUnitKernelIdealTensorEquiv_tmul f I M n U a x)
      _ = (X.presheaf.map (homOfLE h).op).hom a.val • r x := r.map_smulₛₗ a.val x
      _ = (kernel.ι q).app W
          (levelUnitKernelIdealTensorEquiv f I M n W
            (ReesTensor.idealTensorRestriction f I M h (n + 1)
              (a ⊗ₜ[Γ(X, U)] x))) := by
        change _ = (kernel.ι q).app W
          (levelUnitKernelIdealTensorEquiv f I M n W
            ((ReesTensor.idealPowerRestriction f I h (n + 1) a) ⊗ₜ[Γ(X, W)] r x))
        exact (levelUnitKernelIdealTensorEquiv_tmul f I M n W
          (ReesTensor.idealPowerRestriction f I h (n + 1) a) (r x)).symm
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, map_add]

variable [IsSeparated f] (C : X.OrderedAffineCover)

/-- Vanishing for the actual ideal tensor and actual intersection
frames gives global surjectivity of the original closed-level unit. -/
theorem levelPullbackUnit_globalSections_surjective_of_idealTensor_H1
    (hflat : ∀ (r : ℕ) (s : C.Idx r), Module.Flat Γ(X, C.inter s) Γ(M, C.inter s))
    (n : ℕ)
    [Subsingleton ((ReesTensor.idealTensorPresheaf f I M (n + 1)).HSucc C 0)] :
    Function.Surjective ((levelPullbackUnit f I M n).app ⊤) := by
  let q := levelPullbackUnit f I M n
  let e (r : ℕ) (s : C.Idx r) :
      (ReesTensor.idealTensorPresheaf f I M (n + 1)).obj (C.inter s) ≃+
        (toOModulePresheaf f (kernel q)).obj (C.inter s) := by
    have : Module.Flat Γ(X, C.inter s) Γ(M, C.inter s) := hflat r s
    exact (levelUnitKernelIdealTensorEquiv f I M n (C.affineInter f s)).toAddEquiv
  have hH : Subsingleton ((toOModulePresheaf f (kernel q)).HSucc C 0) := by
    apply OModulePresheaf.subsingleton_HSucc_of_intersectionEquiv C
      (ReesTensor.idealTensorPresheaf f I M (n + 1))
      (toOModulePresheaf f (kernel q)) e
    intro r s i z
    have : Module.Flat Γ(X, C.inter s) Γ(M, C.inter s) := hflat (r + 1) s
    have : Module.Flat Γ(X, C.inter (C.face s i)) Γ(M, C.inter (C.face s i)) :=
      hflat r (C.face s i)
    exact (levelUnitKernelIdealTensorEquiv_restriction f I M n
      (C.affineInter f (C.face s i))
      (C.affineInter f s) (C.inter_le_inter_face s i) z).symm
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel q
      mono_f := inferInstance
      epi_g := levelPullbackUnit_epi f I M n }
  exact globalSections_surjective_of_shortExact_of_subsingleton_H1 f C S hS

end AlgebraicGeometry.FiniteEtale.AdicCoverTower

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules FiniteEtale.AdicCoverTower
open AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

attribute [local instance] MvPolynomial.gradedAlgebra

/-- After a single twist bound, sections of the original twisting line
reduce surjectively to every original closed level. The displayed tensor
unit retains exactly the coefficient sheaf used in the Rees theorem. -/
theorem exists_closedProjective_twisting_bound_globalReduction_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j] :
    let f := j ≫ π R n
    let L := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Function.Surjective
        ((levelPullbackUnit f I ((𝟙_ Y.Modules) ⊗ L.tensorPow d) k).app ⊤) := by
  intro f L
  let U : Y.Modules := 𝟙_ Y.Modules
  have : U.IsQuasicoherent := isQuasicoherent_unit Y
  have : U.IsFiniteType := by
    apply isFiniteType_of_finite_affine_sections U
    intro W _hW
    change Module.Finite Γ(Y, W) Γ(Y, W)
    infer_instance
  obtain ⟨c, hc⟩ :=
    exists_closedImmersion_idealTensor_coefficient_twisting_bound_subsingleton_HSucc R I n j U
  refine ⟨c, ?_⟩
  intro d hd k
  let M : Y.Modules := U ⊗ L.tensorPow d
  let C := stdCoverPullback (A := R) (n := n) j
  have : M.IsQuasicoherent :=
    IsInvertible.isQuasicoherent_tensorPow U
      (IsInvertible.pullback j (isInvertible_twistingSheaf R n)) d
  have : Subsingleton ((ReesTensor.idealTensorPresheaf f I M (k + 1)).HSucc C 0) :=
    hc d hd (k + 1) 0
  apply levelPullbackUnit_globalSections_surjective_of_idealTensor_H1 f I M C
  intro r s
  obtain ⟨t, ht⟩ := exists_twistingPow_frame_stdCoverPullback_inter R n j d r s
  exact (ht.map_iso (λ_ (L.tensorPow d)).symm).sections_flat

/-- For every fixed finite rank, one bound makes global sections of
the original free twist surject onto every actual adic reduction. -/
theorem exists_closedProjective_freeTwist_bound_globalReduction_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j] (J : Type u) [Finite J] :
    let f := j ≫ π R n
    let L := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
    let P : Y.Modules := SheafOfModules.free J
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Function.Surjective ((levelPullbackUnit f I (P ⊗ L.tensorPow d) k).app ⊤) := by
  intro f L P
  have : P.IsQuasicoherent := inferInstance
  have : P.IsFiniteType := finiteType_free (X := Y) J
  obtain ⟨c, hc⟩ :=
    exists_closedImmersion_idealTensor_coefficient_twisting_bound_subsingleton_HSucc R I n j P
  refine ⟨c, ?_⟩
  intro d hd k
  let M : Y.Modules := P ⊗ L.tensorPow d
  let C := stdCoverPullback (A := R) (n := n) j
  have : M.IsQuasicoherent :=
    IsInvertible.isQuasicoherent_tensorPow P
      (IsInvertible.pullback j (isInvertible_twistingSheaf R n)) d
  have : Subsingleton ((ReesTensor.idealTensorPresheaf f I M (k + 1)).HSucc C 0) :=
    hc d hd (k + 1) 0
  apply levelPullbackUnit_globalSections_surjective_of_idealTensor_H1 f I M C
  intro r s
  obtain ⟨t, ht⟩ := exists_twistingPow_frame_stdCoverPullback_inter R n j d r s
  exact ht.finiteFreeTensor_sections_flat J

end AlgebraicGeometry.ProjSpace
