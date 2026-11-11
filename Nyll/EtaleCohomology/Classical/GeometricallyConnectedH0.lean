/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomologySections
public import Nyll.EtaleCohomology.Frobenius.Cohomology
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleCohomology.Sites.GeometricallyConnectedSections
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Native H⁰ descent along geometrically connected morphisms

The original fpqc descent theorem for sections identifies the actual native
H⁰ pullback as a bijection. Forgetting constant module coefficients gives the
same result for constant abelian coefficients. The original structural roots
comparison then descends sections of the actual Kummer kernel.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.Cohomology

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (q : X ⟶ Y)
  [Flat q] [QuasiCompact q] [GeometricallyConnected q]

/-- Flat quasi-compact geometrically connected pullback is bijective on
the original module H⁰, through its actual section map. -/
theorem etaleCohomologyPullbackMap_zero_bijective
    (R : Type u) [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    Function.Bijective (etaleCohomologyPullbackMap q R F 0) := by
  let hX := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let hY := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y
  let eX := Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u}
    ((etalePullback q R).obj F) hX
  let eY := Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F hY
  have hb := etalePullbackGlobalSectionsMap_bijective_of_geometricallyConnected q R F
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply eY.injective
    apply hb.1
    rw [← etaleCohomologyPullbackMap_zero_globalSections,
      ← etaleCohomologyPullbackMap_zero_globalSections, hab]
  · intro b
    obtain ⟨a, ha⟩ := hb.2 (eX b)
    refine ⟨eY.symm a, eX.injective ?_⟩
    exact (etaleCohomologyPullbackMap_zero_globalSections q R F (eY.symm a)).trans
      ((congrArg (etalePullbackGlobalSectionsMap q R F)
        (eY.apply_symm_apply a)).trans ha)

/-- The canonical constant-module comparison preserves the bijection on
native H⁰ supplied by geometrically connected descent. -/
theorem etaleConstantCohomologyPullbackMap_zero_bijective
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    Function.Bijective (etaleConstantCohomologyPullbackMap q R M 0) := by
  let e := (Sheaf.functorH X.smallEtaleTopology 0).mapIso
    (Classical.forgetCoefficients.{u + 1, u, u, u}.mapIso
      ((etalePullbackConstantIso q R).app M))
  exact e.addCommGroupIsoToAddEquiv.bijective.comp
    (etaleCohomologyPullbackMap_zero_bijective q R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M))

/-- Actual constant abelian H⁰ descends uniquely along a flat
quasi-compact geometrically connected morphism. -/
theorem constantCohomologyPullback_zero_bijective (A : AddCommGrpCat.{u}) :
    Function.Bijective (constantCohomologyPullback q A 0) := by
  let R := ULift.{u} ℤ
  let : Module R A := Module.compHom A
    (ULift.ringEquiv : R ≃+* ℤ).toRingHom
  let M : ModuleCat.{u} R := ModuleCat.of R A
  let eX := etaleConstantCohomologyForgetEquiv R (X := X) M 0
  let eY := etaleConstantCohomologyForgetEquiv R (X := Y) M 0
  have hb := etaleConstantCohomologyPullbackMap_zero_bijective q R M
  have hn (a : etaleCohomology Y R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M) 0) :
      eX (etaleConstantCohomologyPullbackMap q R M 0 a) =
      constantCohomologyPullback q A 0 (eY a) :=
    etaleConstantCohomologyPullbackMap_forget R q M 0 a
  refine ⟨?_, ?_⟩
  · intro a b hab
    have he : etaleConstantCohomologyPullbackMap q R M 0 (eY.symm a) =
        etaleConstantCohomologyPullbackMap q R M 0 (eY.symm b) := by
      apply eX.injective
      rw [hn, hn, eY.apply_symm_apply, eY.apply_symm_apply, hab]
    exact eY.symm.injective (hb.1 he)
  · intro b
    obtain ⟨a, ha⟩ := hb.2 (eX.symm b)
    refine ⟨eY a, ?_⟩
    rw [← hn, ha, eX.apply_symm_apply]

/-- The actual Kummer-kernel H⁰ descends uniquely. The coefficient
comparison is the original structural map from roots in the base field. -/
theorem etaleRootsOfUnityCohomologyPullback_zero_bijective
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : Y ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K)) :
    Function.Bijective (etaleRootsOfUnityCohomologyPullback q n 0) := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let eX :
      Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 0 ≃+
        Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 0 :=
    ((Sheaf.functorH X.smallEtaleTopology 0).mapIso
      (constantRootsOfUnityKummerKernelIso (q ≫ c) hn hnK)).addCommGroupIsoToAddEquiv
  let eY :
      Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) 0 ≃+
        Sheaf.H.{u} (etaleRootsOfUnitySheaf Y n) 0 :=
    ((Sheaf.functorH Y.smallEtaleTopology 0).mapIso
      (constantRootsOfUnityKummerKernelIso c hn hnK)).addCommGroupIsoToAddEquiv
  have hb := constantCohomologyPullback_zero_bijective q A
  have hnaturality (a : Sheaf.H.{u}
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) 0) :
      eX (constantCohomologyPullback q A 0 a) =
      etaleRootsOfUnityCohomologyPullback q n 0 (eY a) :=
    constantRootsOfUnityToKummerKernel_cohomologyPullback q c hn hnK 0 a
  refine ⟨?_, ?_⟩
  · intro a b hab
    have he : constantCohomologyPullback q A 0 (eY.symm a) =
        constantCohomologyPullback q A 0 (eY.symm b) := by
      apply eX.injective
      rw [hnaturality, hnaturality, eY.apply_symm_apply, eY.apply_symm_apply, hab]
    exact eY.symm.injective (hb.1 he)
  · intro b
    obtain ⟨a, ha⟩ := hb.2 (eX.symm b)
    refine ⟨eY a, ?_⟩
    rw [← hnaturality, ha, eX.apply_symm_apply]

end EtaleCohomology
