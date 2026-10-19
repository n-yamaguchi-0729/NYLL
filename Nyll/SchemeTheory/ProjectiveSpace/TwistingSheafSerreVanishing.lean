/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCechComparison
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafGlobalGeneration
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPositiveVanishing
import Nyll.SchemeTheory.Cohomology.Cech.FiniteFreeTensorVanishing
import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteUnitClosedImmersionProj
import Nyll.SchemeTheory.Cohomology.Sheaves.AffineExactSequenceSections
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafAffSES
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeKernel
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentImage
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Tensor.InvertibleExactness
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Sites.LeftExact
import Lean.Elab.Tactic.Omega

/-!
# Serre vanishing for actual coherent module sheaves on projective space

Choose finite global generators after a twist and take the actual native
kernel. It is quasicoherent and finite type over a Noetherian scheme.
Tensoring this kernel sequence with a twisting power preserves its
short exactness by the coordinate frames. The original affine Čech
connecting maps then reduce vanishing to the next cohomological degree.

The coordinate cover bounds the cohomological degrees. Descending
induction and a finite sum of twist bounds give a single bound for
all positive cohomology groups. Every input in this induction is supplied
by the native twisting sheaf and its constructed sections; no graded
presentation or comparison is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules ProjSpaceCech
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem mono_native_kernel {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf} (φ : M ⟶ N) :
    Mono (kernel.ι φ) := inferInstance

private theorem finiteType_kernel_of_finite_generators
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (A : SheafOfModules.{u} X.ringCatSheaf) [A.IsQuasicoherent]
    (G : A.GeneratingSections) [G.IsFiniteType] :
    (kernel G.π).IsQuasicoherent ∧ (kernel G.π).IsFiniteType := by
  have : Finite G.I := SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := G)
  let P : SheafOfModules.{u} X.ringCatSheaf := SheafOfModules.free G.I
  have : P.IsQuasicoherent := inferInstance
  have : P.IsFiniteType := by
    let H : P.GeneratingSections :=
      SheafOfModules.free.generatingSections (R := X.ringCatSheaf) G.I
    let q : P.LocalGeneratorsData := H.localGeneratorsData
    have hq : q.IsFiniteType := by
      constructor
      intro U
      refine { finite := ?_ }
      exact (show Finite G.I from inferInstance)
    exact q.isFiniteType hq
  exact ⟨SheafOfModules.isQuasicoherent_kernel_native (X := X) G.π,
    SheafOfModules.isFiniteType_kernel_on_locallyNoetherian (X := X) G.π⟩

private theorem eventualTwistedVanishing_step
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of R)) [IsSeparated f] (K : X.OrderedAffineCover) (L : X.Modules)
    (hgen : ∀ M : X.Modules,
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M →
      SheafOfModules.IsFiniteType (R := X.ringCatSheaf) M →
      ∃ a : ℕ, ∀ d : ℕ, a ≤ d →
        ∃ G : (M ⊗ L.tensorPow d).GeneratingSections, G.IsFiniteType)
    (hqc : ∀ M : X.Modules,
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M → ∀ d : ℕ,
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        (Scheme.Modules.tensor (X := X) M (L.tensorPow d)))
    (hexact : ∀ d : ℕ, PreservesFiniteLimits (tensorRight (L.tensorPow d)))
    (q : ℕ)
    (hfree : ∀ (J : Type u) (_ : Finite J) (d : ℕ),
      Subsingleton ((toOModulePresheaf f
        (Scheme.Modules.tensor (X := X) (show X.Modules from SheafOfModules.free J)
          (L.tensorPow d))).HSucc K q))
    (hnext : ∀ M : X.Modules,
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M →
      SheafOfModules.IsFiniteType (R := X.ringCatSheaf) M →
      ∃ b : ℕ, ∀ d : ℕ, b ≤ d →
        Subsingleton ((toOModulePresheaf f (M ⊗ L.tensorPow d)).HSucc K (q + 1)))
    (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := X.ringCatSheaf) F] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d →
      Subsingleton ((toOModulePresheaf f (F ⊗ L.tensorPow d)).HSucc K q) := by
  obtain ⟨a, ha⟩ := hgen F inferInstance inferInstance
  obtain ⟨G, hG⟩ := ha a le_rfl
  have : G.IsFiniteType := hG
  have hGI : Finite G.I := SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := G)
  let A : X.Modules := F ⊗ L.tensorPow a
  have hAqc : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) A :=
    hqc F inferInstance a
  let Q : SheafOfModules.{u} X.ringCatSheaf := kernel G.π
  obtain ⟨hQqc, hQft⟩ := finiteType_kernel_of_finite_generators (X := X) A G
  obtain ⟨b, hb⟩ := hnext (show X.Modules from Q) hQqc hQft
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf := sheafOfModulesEquivalence X
  let S₀ : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
    ShortComplex.mk (kernel.ι G.π) G.π (kernel.condition G.π)
  have : Epi G.π := G.epi
  have hS₀ : S₀.ShortExact := {
    exact := ShortComplex.exact_kernel G.π
    mono_f := mono_native_kernel (X := X) G.π
    epi_g := G.epi }
  have : E.inverse.IsLeftAdjoint := E.symm.toAdjunction.isLeftAdjoint
  have : E.inverse.IsRightAdjoint := E.toAdjunction.isRightAdjoint
  let S : ShortComplex X.Modules := S₀.map E.inverse
  have hS : S.ShortExact := hS₀.map_of_exact E.inverse
  refine ⟨a + b, ?_⟩
  intro d hd
  let t : ℕ := d - a
  have hbt : b ≤ t := by
    dsimp only [t]
    omega
  have hat : a + t = d := by
    dsimp only [t]
    omega
  have : (tensorRight (L.tensorPow t)).IsLeftAdjoint := inferInstance
  have : PreservesFiniteLimits (tensorRight (L.tensorPow t)) := hexact t
  let T : ShortComplex X.Modules := S.map (tensorRight (L.tensorPow t))
  have hT : T.ShortExact := hS.map_of_exact (tensorRight (L.tensorPow t))
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) T.X₂ :=
    hqc (show X.Modules from SheafOfModules.free G.I) inferInstance t
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) T.X₃ := hqc A hAqc t
  have hQcoh : Subsingleton ((toOModulePresheaf f T.X₁).HSucc K (q + 1)) := hb t hbt
  have hPcoh : Subsingleton ((toOModulePresheaf f T.X₂).HSucc K q) := hfree G.I hGI t
  let seq := toOModulePresheafAffSES f T hT
  have hsurj : Function.Surjective (seq.proj.HSuccMap K q) :=
    seq.HSuccMap_proj_surjective_of_subsingleton K q
  have : Subsingleton ((toOModulePresheaf f (A ⊗ L.tensorPow t)).HSucc K q) := by
    constructor
    intro x y
    obtain ⟨x', rfl⟩ := hsurj x
    obtain ⟨y', rfl⟩ := hsurj y
    exact congrArg (seq.proj.HSuccMap K q) (hPcoh.elim x' y')
  let ePow : L.tensorPow a ⊗ L.tensorPow t ≅ L.tensorPow d :=
    tensorPowAdd L a t ≪≫ eqToIso (congrArg L.tensorPow hat)
  let e : A ⊗ L.tensorPow t ≅ F ⊗ L.tensorPow d :=
    (α_ F (L.tensorPow a) (L.tensorPow t)) ≪≫ whiskerLeftIso F ePow
  exact subsingleton_HSucc_of_iso f K e q

private theorem eventualTwistedVanishing_of_generation
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of R)) [IsSeparated f] (K : X.OrderedAffineCover)
    (L : X.Modules) (n : ℕ)
    (hgen : ∀ M : X.Modules,
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M →
      SheafOfModules.IsFiniteType (R := X.ringCatSheaf) M →
      ∃ a : ℕ, ∀ d : ℕ, a ≤ d →
        ∃ G : (M ⊗ L.tensorPow d).GeneratingSections, G.IsFiniteType)
    (hqc : ∀ M : X.Modules,
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M → ∀ d : ℕ,
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        (Scheme.Modules.tensor (X := X) M (L.tensorPow d)))
    (hexact : ∀ d : ℕ, PreservesFiniteLimits (tensorRight (L.tensorPow d)))
    (hfree : ∀ (J : Type u) (_ : Finite J) (d q : ℕ),
      Subsingleton ((toOModulePresheaf f
        (Scheme.Modules.tensor (X := X) (show X.Modules from SheafOfModules.free J)
          (L.tensorPow d))).HSucc K q))
    (hbound : ∀ (M : X.Modules) (q : ℕ), n ≤ q →
      Subsingleton ((toOModulePresheaf f M).HSucc K q))
    (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := X.ringCatSheaf) F] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ q : ℕ,
      Subsingleton ((toOModulePresheaf f (F ⊗ L.tensorPow d)).HSucc K q) := by
  classical
  have h : ∀ r q : ℕ, n ≤ q + r → ∀ M : X.Modules,
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M →
      SheafOfModules.IsFiniteType (R := X.ringCatSheaf) M →
      ∃ c : ℕ, ∀ d : ℕ, c ≤ d →
        Subsingleton ((toOModulePresheaf f (M ⊗ L.tensorPow d)).HSucc K q) := by
    intro r
    induction r with
    | zero =>
      intro q hq M _ _
      exact ⟨0, fun d _ => hbound (M ⊗ L.tensorPow d) q (by omega)⟩
    | succ r ih =>
      intro q hq M hMqc hMft
      have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M := hMqc
      have : SheafOfModules.IsFiniteType (R := X.ringCatSheaf) M := hMft
      exact eventualTwistedVanishing_step f K L hgen hqc hexact q
        (fun J hJ d => hfree J hJ d q) (ih (q + 1) (by omega)) M
  let B : Fin n → ℕ := fun q =>
    (h n q.val (by omega) F inferInstance inferInstance).choose
  refine ⟨∑ q : Fin n, B q, ?_⟩
  intro d hd q
  by_cases hq : q < n
  · have hB : B ⟨q, hq⟩ ≤ ∑ j : Fin n, B j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (B j))
        (Finset.mem_univ (⟨q, hq⟩ : Fin n))
    exact (h n q (by omega) F inferInstance inferInstance).choose_spec d (hB.trans hd)
  · exact hbound (F ⊗ L.tensorPow d) q (Nat.le_of_not_gt hq)

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

private theorem subsingleton_HSucc_above_dimension (M : (Proj 𝒜).Modules)
    (q : ℕ) (hq : n ≤ q) :
    Subsingleton ((toOModulePresheaf ((𝟙 (Proj 𝒜)) ≫ π R n) M).HSucc
      (stdCoverPullback (𝟙 (Proj 𝒜))) q) := by
  have hcoh : Subsingleton ((toOModulePresheaf ((𝟙 (Proj 𝒜)) ≫ π R n) M).cochain
      (stdCoverPullback (𝟙 (Proj 𝒜))) (q + 1)) := by
    have hempty := Idx.isEmpty_of_lt n (Nat.lt_succ_of_le hq)
    exact ⟨fun x y => funext fun s =>
      (hempty.false (ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) (q + 1) s)).elim⟩
  exact ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    congrArg _ (Subtype.ext (hcoh.elim a.val b.val))⟩

/-- Serre vanishing for the actual native coherent sheaf on projective
space: one nonnegative twist bound kills every positive Čech cohomology
group for all larger twists. The section presheaf is the original one. -/
theorem exists_twisting_bound_subsingleton_HSucc [IsNoetherianRing R]
    (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := (Proj 𝒜).ringCatSheaf) F] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ q : ℕ,
      Subsingleton ((toOModulePresheaf ((𝟙 (Proj 𝒜)) ≫ π R n)
        (F ⊗ (twistingSheaf R n).tensorPow d)).HSucc
          (stdCoverPullback (𝟙 (Proj 𝒜))) q) := by
  have : IsLocallyNoetherian (Proj 𝒜) :=
    LocallyOfFiniteType.isLocallyNoetherian (π R n)
  exact eventualTwistedVanishing_of_generation ((𝟙 (Proj 𝒜)) ≫ π R n)
    (stdCoverPullback (𝟙 (Proj 𝒜))) (twistingSheaf R n) n
    (fun M hMqc hMft => by
      have : SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) M := hMqc
      have : SheafOfModules.IsFiniteType (R := (Proj 𝒜).ringCatSheaf) M := hMft
      exact exists_twisting_bound_generatingSections R n M)
    (fun M hMqc d => by
      have : SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) M := hMqc
      exact isQuasicoherent_tensor_twistingSheaf R n M d)
    ((isInvertible_twistingSheaf R n).tensorRight_tensorPow_preservesFiniteLimits)
    (fun J hJ d q => by
      have : Finite J := hJ
      have : Subsingleton ((twistingSectionPresheaf R n d).HSucc
          (stdCoverPullback (𝟙 (Proj 𝒜))) q) :=
        twistingSectionPresheaf_subsingleton_HSucc R n d q
      exact finiteFreeTensor_subsingleton_HSucc ((𝟙 (Proj 𝒜)) ≫ π R n)
        ((twistingSheaf R n).tensorPow d) J (stdCoverPullback (𝟙 (Proj 𝒜))) q)
    (subsingleton_HSucc_above_dimension R n) F

end AlgebraicGeometry.ProjSpace
