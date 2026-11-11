/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedProjectiveHomLift
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveCokernelPresentations
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelPresentations
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentCokernel
public import Nyll.SchemeTheory.Modules.Sections.PullbackQuotientCokernel
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.ProjectiveSpace.AdicFreeTwistCokernel
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Algebraizing the actual twisted cover presentations

The compatible relation maps constructed from the native syzygies lift
to a relation map on the original closed projective family. Its actual
cokernel is quasicoherent and finite type. The existing closed-quotient
cokernel comparison recovers every original cover stage after the two
specified twists. Its projection equation also proves compatibility
with all the original transitions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j]
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (level (j ≫ π R n) (IsLocalRing.maximalIdeal R) 0))
  (d : ℕ) (K : Type u) [Finite K]
  (α : ∀ a : ℕ, (show Y.Modules from SheafOfModules.free K) ⟶
    moduleSheaf (j ≫ π R n) (IsLocalRing.maximalIdeal R) V a ⊗
      ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d)
  (hα : ∀ a : ℕ, α (a + 1) ≫
    (moduleTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) V a ▷
      ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d) = α a)
  (hgen : ∀ a : ℕ, Epi (α a))

include hα hgen in
/-- The actual compatible cover presentations algebraize to a finite
quasicoherent cokernel. Its original quotient maps recover every stage
after pullback and commute with every original cover transition. -/
theorem exists_closedProjective_twisting_bound_cokernel_algebraization :
    let f := j ≫ π R n
    let I := IsLocalRing.maximalIdeal R
    let L : Y.Modules := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
    let P : Y.Modules := SheafOfModules.free K
    let _ : (L.tensorPow d).IsQuasicoherent :=
      closedProjectiveTwistingPow_isQuasicoherent R n j d
    ∃ c : ℕ, ∀ e : ℕ, c ≤ e → ∃ J : Type u, Finite J ∧
      ∃ φ : (show Y.Modules from SheafOfModules.free J) ⟶ P ⊗ L.tensorPow e,
        (cokernel φ).IsQuasicoherent ∧ (cokernel φ).IsFiniteType ∧
        ∃ r : ∀ a : ℕ, cokernel φ ⟶
            (moduleSheaf f I V a ⊗ L.tensorPow d) ⊗ L.tensorPow e,
          (∀ a : ℕ, IsIso
            ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I a))).map (r a))) ∧
          (∀ a : ℕ, r (a + 1) ≫
            ((moduleTransition f I V a ▷ L.tensorPow d) ▷ L.tensorPow e) = r a) ∧
          (∀ a : ℕ, cokernel.π φ ≫ r a = α a ▷ L.tensorPow e) := by
  intro f I L P hLd
  obtain ⟨c₀, hc₀⟩ :=
    exists_closedProjective_twisting_bound_compatible_cokernel_presentations
      R I n j V d K α hα hgen
  obtain ⟨c₁, hc₁⟩ :=
    exists_closedProjective_freeTwist_bound_compatibleHom_lift R n j K
  refine ⟨max c₀ c₁, ?_⟩
  intro e he
  obtain ⟨J, hJ, θ, hθ, hE⟩ := hc₀ e (le_trans (le_max_left _ _) he)
  have : Finite J := hJ
  obtain ⟨φ, hφ⟩ := hc₁ e (le_trans (le_max_right _ _) he) J θ hθ
  choose E hE using hE
  let N : Y.Modules := L.tensorPow e
  have hL : IsInvertible L := IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  have : P.IsQuasicoherent := inferInstance
  have : P.IsFiniteType := ProjSpace.finiteType_free K
  have : (P ⊗ N).IsQuasicoherent := IsInvertible.isQuasicoherent_tensorPow P hL e
  have : (P ⊗ N).IsFiniteType := IsInvertible.isFiniteType_tensorPow P hL e
  have hCqc : (cokernel φ).IsQuasicoherent := isQuasicoherent_cokernel φ
  have hCft : (cokernel φ).IsFiniteType := ProjSpace.finiteType_cokernel φ
  let i (a : ℕ) : level f I a ⟶ Y := Limits.pullback.fst f (baseInclusion I a)
  let q (a : ℕ) : cokernel φ ⟶ cokernel (θ a) :=
    pullbackQuotientCokernelMap (i a) N φ (θ a) (hφ a)
  let r (a : ℕ) : cokernel φ ⟶ (moduleSheaf f I V a ⊗ L.tensorPow d) ⊗ N :=
    q a ≫ (E a).hom
  have hr (a : ℕ) : cokernel.π φ ≫ r a = α a ▷ N := by
    have hq : cokernel.π φ ≫ q a =
        (levelPullbackUnit f I P a ▷ N) ≫ cokernel.π (θ a) :=
      cokernel_π_pullbackQuotientCokernelMap (i a) N φ (θ a) (hφ a)
    calc
      cokernel.π φ ≫ r a = (cokernel.π φ ≫ q a) ≫ (E a).hom :=
        (Category.assoc _ _ _).symm
      _ = ((levelPullbackUnit f I P a ▷ N) ≫ cokernel.π (θ a)) ≫ (E a).hom :=
        congrArg (fun b => b ≫ (E a).hom) hq
      _ = (levelPullbackUnit f I P a ▷ N) ≫
          (cokernel.π (θ a) ≫ (E a).hom) := Category.assoc _ _ _
      _ = (levelPullbackUnit f I P a ▷ N) ≫
          (levelPresentation f I V (L.tensorPow d) P a (α a) ▷ N) :=
        congrArg (fun b => (levelPullbackUnit f I P a ▷ N) ≫ b) (hE a)
      _ = (levelPullbackUnit f I P a ≫
          levelPresentation f I V (L.tensorPow d) P a (α a)) ▷ N :=
        (comp_whiskerRight _ _ _).symm
      _ = α a ▷ N := congrArg (fun b => b ▷ N)
        (levelUnit_levelPresentation f I V (L.tensorPow d) P a (α a))
  refine ⟨J, hJ, φ, hCqc, hCft, r, ?_, ?_, hr⟩
  · intro a
    have : IsIso ((Scheme.Modules.pullback (i a)).map (q a)) :=
      isIso_pullback_map_pullbackQuotientCokernelMap (i a) N φ (θ a) (hφ a)
    change IsIso ((Scheme.Modules.pullback (i a)).map (q a ≫ (E a).hom))
    rw [Functor.map_comp]
    infer_instance
  · intro a
    apply (cancel_epi (cokernel.π φ)).mp
    calc
      cokernel.π φ ≫
          (r (a + 1) ≫ ((moduleTransition f I V a ▷ L.tensorPow d) ▷ N)) =
          (cokernel.π φ ≫ r (a + 1)) ≫
            ((moduleTransition f I V a ▷ L.tensorPow d) ▷ N) :=
        (Category.assoc _ _ _).symm
      _ = (α (a + 1) ▷ N) ≫
          ((moduleTransition f I V a ▷ L.tensorPow d) ▷ N) :=
        congrArg (fun b => b ≫ ((moduleTransition f I V a ▷ L.tensorPow d) ▷ N)) (hr (a + 1))
      _ = (α (a + 1) ≫ (moduleTransition f I V a ▷ L.tensorPow d)) ▷ N :=
        (comp_whiskerRight _ _ _).symm
      _ = α a ▷ N := congrArg (fun b => b ▷ N) (hα a)
      _ = cokernel.π φ ≫ r a := (hr a).symm

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
