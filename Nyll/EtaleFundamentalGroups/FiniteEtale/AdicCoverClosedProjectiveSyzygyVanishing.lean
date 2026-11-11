/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPresentation
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverNativeSyzygyCech
public import Nyll.SchemeTheory.Cohomology.Sheaves.ReesClosedProjectiveSerre
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.ProjectiveSpace.ClosedProjectiveTwistingFrames
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Uniform vanishing for actual closed-projective syzygy layers

The first native syzygy is a finite-type quasicoherent subsheaf of the
actual finite free closed-level source. Apply the existing Rees uniform
vanishing theorem to this actual sheaf. Coordinate frames supply the
native comparison on every original Čech intersection, so the same
bound kills every actual syzygy-transition kernel after further twisting.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every tensor power of the actual pulled-back twisting sheaf is
quasicoherent, using the unit sheaf and its original tensor unitor. -/
theorem closedProjectiveTwistingPow_isQuasicoherent
    (R : Type u) [CommRing R] (n : ℕ) {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (d : ℕ) :
    (((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d).IsQuasicoherent := by
  let U : Y.Modules := 𝟙_ Y.Modules
  let T : Y.Modules := ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d
  have : U.IsQuasicoherent := isQuasicoherent_unit Y
  have hL : IsInvertible ((Scheme.Modules.pullback j).obj (twistingSheaf R n)) :=
    IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  have ht : (tensor U T).IsQuasicoherent := IsInvertible.isQuasicoherent_tensorPow U hL d
  let E : Y.Modules ≌ SheafOfModules.{u} Y.ringCatSheaf := sheafOfModulesEquivalence Y
  exact (SheafOfModules.isQuasicoherent (C := Y.Opens) Y.ringCatSheaf).prop_of_iso
    (E.functor.mapIso (λ_ T)) ht

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace
open AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j]
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level (j ≫ π R n) I 0))
  (d : ℕ) (K : Type u) [Finite K]
  (α : ∀ a : ℕ, (show Y.Modules from SheafOfModules.free K) ⟶
    moduleSheaf (j ≫ π R n) I V a ⊗
      ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d)
  (hα : ∀ a : ℕ, α (a + 1) ≫
    (moduleTransition (j ≫ π R n) I V a ▷
      ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d) = α a)
  (hgen : ∀ a : ℕ, Epi (α a))

include hgen in
/-- One bound kills every positive Čech cohomology group of every
actual native syzygy-transition kernel after a further pullback twist. -/
theorem exists_closedProjective_syzygy_twisting_bound_kernel_HSucc :
    let L : Y.Modules := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
    let _ : (L.tensorPow d).IsQuasicoherent := closedProjectiveTwistingPow_isQuasicoherent R n j d
    let M : ℕ → Y.Modules := fun a => levelPresentationKernel (j ≫ π R n) I V (L.tensorPow d)
      (show Y.Modules from SheafOfModules.free K) a (α a)
    let q : ∀ a : ℕ, M (a + 1) ⟶ M a := fun a =>
      levelPresentationKernelTransition (j ≫ π R n) I V (L.tensorPow d)
        (show Y.Modules from SheafOfModules.free K) α hα a
    ∃ c : ℕ, ∀ e : ℕ, c ≤ e → ∀ a k : ℕ,
      Subsingleton ((toOModulePresheaf (j ≫ π R n)
        (kernel (q a) ⊗ L.tensorPow e)).HSucc (stdCoverPullback (A := R) (n := n) j) k) := by
  intro L hLd M q
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (j ≫ π R n)
  have : (SheafOfModules.free (R := Y.ringCatSheaf) K).IsFiniteType := finiteType_free K
  have : (M 0).IsFiniteType :=
    levelPresentationKernel_isFiniteType (j ≫ π R n) I V (L.tensorPow d)
      (show Y.Modules from SheafOfModules.free K) 0 (α 0)
  have hL : IsInvertible L := IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  obtain ⟨c, hc⟩ :=
    exists_closedImmersion_idealTensor_coefficient_twisting_bound_subsingleton_HSucc
      R I n j (M 0)
  let C : Y.OrderedAffineCover := stdCoverPullback (A := R) (n := n) j
  let t (r : ℕ) (s : C.Idx r) : Γ(L.tensorPow d, C.inter s) :=
    (exists_twistingPow_frame_stdCoverPullback_inter R n j d r s).choose
  have ht (r : ℕ) (s : C.Idx r) : IsFrameOn (t r s) (C.inter s) :=
    (exists_twistingPow_frame_stdCoverPullback_inter R n j d r s).choose_spec
  refine ⟨c, ?_⟩
  intro e he a k
  have : (L.tensorPow e).IsQuasicoherent := closedProjectiveTwistingPow_isQuasicoherent R n j e
  exact nativeSyzygyTensorHSucc_subsingleton_of_idealTensor
    (j ≫ π R n) I V L d K α hα hL hgen (L.tensorPow e) C t ht a k (hc e he (a + 1) k)

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
