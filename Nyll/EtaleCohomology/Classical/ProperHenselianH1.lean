/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
import Nyll.EtaleCohomology.Classical.ClosedPushforward
import Nyll.EtaleCohomology.Classical.Localization
import Nyll.EtaleCohomology.Classical.ModuleCohomology
import Nyll.EtaleCohomology.Classical.PullbackCoefficients
import Nyll.EtaleCohomology.Sites.ProperHenselianH0
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
import Mathlib.RingTheory.Henselian

/-!
# Injectivity of henselian proper base change in degree one

The actual degree-zero proper base-change theorem, applied to an injective
presentation and its quotient, makes restriction injective in degree one.
The injective presentation belongs to abelian sheaves. No preservation of
injectivity by forgetting a general coefficient ring is assumed.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem cohomology_one_map_injective_of_zero_bijective
    (X : Scheme.{u})
    (T : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (η : 𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⟶ T)
    (hzero : ∀ F, Function.Bijective (Sheaf.H.map (η.app F) 0))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Injective (Sheaf.H.map (η.app F) 1) := by
  have hker (a : Sheaf.H.{u} F 1) (ha : Sheaf.H.map (η.app F) 1 a = 0) :
      a = 0 := by
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition (Injective.ι F))
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
    have hTS : (S.map T).ShortExact := hS.map_of_exact T
    let ηS : S ⟶ S.map T :=
      { τ₁ := η.app S.X₁
        τ₂ := η.app S.X₂
        τ₃ := η.app S.X₃
        comm₁₂ := (η.naturality S.f).symm
        comm₂₃ := (η.naturality S.g).symm }
    obtain ⟨z, hz⟩ := Sheaf.H.longSequence_exact₁ hS a (Subsingleton.elim _ _) rfl
    have hδ : Sheaf.H.δ hTS 0 1 rfl (Sheaf.H.map (η.app S.X₃) 0 z) = 0 := by
      exact (Sheaf.H.δ_naturality 0 1 rfl hS hTS ηS z).trans
        ((congrArg (Sheaf.H.map (η.app F) 1) hz).trans ha)
    obtain ⟨w, hw⟩ := Sheaf.H.longSequence_exact₃ hTS
      (Sheaf.H.map (η.app S.X₃) 0 z) rfl hδ
    obtain ⟨v, hv⟩ := (hzero S.X₂).surjective w
    have hvz : Sheaf.H.map S.g 0 v = z := by
      apply (hzero S.X₃).injective
      have hn : S.g ≫ η.app S.X₃ = η.app S.X₂ ≫ T.map S.g :=
        η.naturality S.g
      rw [← Sheaf.H.map_comp_apply, hn,
        Sheaf.H.map_comp_apply, hv]
      exact hw
    have hvδ : Sheaf.H.δ hS 0 1 rfl (Sheaf.H.map S.g 0 v) = 0 := by
      change (v.comp (Abelian.Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0
      rw [Abelian.Ext.comp_assoc_of_second_deg_zero,
        ShortComplex.ShortExact.comp_extClass, Abelian.Ext.comp_zero]
    exact hz.symm.trans ((congrArg (Sheaf.H.δ hS 0 1 rfl) hvz).symm.trans hvδ)
  intro a b hab
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hab, sub_self]

private theorem closedFiber_abelianUnit_globalSections_bijective
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    Function.Bijective (((etaleAbelianPullbackPushforwardAdjunction i).unit.app F).hom.app
      (op (Scheme.Etale.mk (𝟙 X)))) := by
  intro r i
  let E := Classical.integerSheafEquivalence X.smallEtaleTopology
  let M := E.inverse.obj F
  let A := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := ULift.{u} ℤ)
  let T := etaleAbelianPullback i ⋙ etaleAbelianPushforward i
  let η : 𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⟶ T :=
    (etaleAbelianPullbackPushforwardAdjunction i).unit
  let e : A.obj M ≅ F := E.counitIso.app F
  let U := op (Scheme.Etale.mk (𝟙 X))
  have hM : Function.Bijective ((η.app (A.obj M)).hom.app U) := by
    change Function.Bijective
      (((etaleAbelianPullbackPushforwardAdjunction i).unit.app (A.obj M)).hom.app U)
    rw [← etalePullbackForgetCoefficientsIso_unit i (ULift.{u} ℤ) M]
    exact (ConcreteCategory.bijective_of_isIso
      (((etaleAbelianPushforward i).map
        ((etalePullbackForgetCoefficientsIso i (ULift.{u} ℤ)).hom.app M)).hom.app U)).comp
      (etaleClosedFiber_unit_globalSections_bijective R f (ULift.{u} ℤ) M)
  have hn : e.hom ≫ η.app F = η.app (A.obj M) ≫ T.map e.hom := η.naturality e.hom
  have he : η.app F = e.inv ≫ η.app (A.obj M) ≫ T.map e.hom := by
    calc
      η.app F = e.inv ≫ (e.hom ≫ η.app F) := by
        rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
      _ = e.inv ≫ η.app (A.obj M) ≫ T.map e.hom := congrArg (fun k => e.inv ≫ k) hn
  change Function.Bijective ((η.app F).hom.app U)
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso ((T.map e.hom).hom.app U)).comp
    (hM.comp (ConcreteCategory.bijective_of_isIso (e.inv.hom.app U)))

/-- The actual closed-fiber adjunction unit is injective on classical H¹
for every abelian sheaf on a proper scheme over a henselian local ring. -/
theorem etaleClosedFiber_abelianUnit_cohomology_one_injective
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    Function.Injective
      (Sheaf.H.map ((etaleAbelianPullbackPushforwardAdjunction i).unit.app F) 1) := by
  intro r i
  have : IsClosedImmersion r := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (IsLocalRing.residue R)) IsLocalRing.residue_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst f r))
  let T := etaleAbelianPullback i ⋙ etaleAbelianPushforward i
  let η : 𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⟶ T :=
    (etaleAbelianPullbackPushforwardAdjunction i).unit
  apply cohomology_one_map_injective_of_zero_bijective X T η ?_ F
  intro G
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
    MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) X
  have hG := closedFiber_abelianUnit_globalSections_bijective R f G
  have hn (a : Sheaf.H.{u} G 0) :
      (η.app G).hom.app (op (Scheme.Etale.mk (𝟙 X))) (Sheaf.H.equiv₀ G hT a) =
        Sheaf.H.equiv₀ (T.obj G) hT (Sheaf.H.map (η.app G) 0 a) :=
    Sheaf.H.equiv₀_naturality hT (η.app G) a
  constructor
  · intro a b hab
    apply (Sheaf.H.equiv₀ G hT).injective
    apply hG.injective
    exact (hn a).trans ((congrArg (Sheaf.H.equiv₀ (T.obj G) hT) hab).trans (hn b).symm)
  · intro b
    obtain ⟨a, ha⟩ := hG.surjective (Sheaf.H.equiv₀ (T.obj G) hT b)
    refine ⟨(Sheaf.H.equiv₀ G hT).symm a, ?_⟩
    apply (Sheaf.H.equiv₀ (T.obj G) hT).injective
    exact (hn ((Sheaf.H.equiv₀ G hT).symm a)).symm.trans
      ((congrArg ((η.app G).hom.app (op (Scheme.Etale.mk (𝟙 X))))
        ((Sheaf.H.equiv₀ G hT).apply_symm_apply a)).trans ha)

/-- Restriction to the actual closed fiber is injective on classical H¹
with any commutative coefficient ring. No torsion or noetherian hypothesis
is used. -/
theorem etaleClosedFiber_cohomology_one_injective
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    let _ : IsClosedImmersion r := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (IsLocalRing.residue R)) IsLocalRing.residue_surjective
    let _ : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst f r))
    Function.Injective (etaleClosedRestrictionCohomologyMap i Λ F 1) := by
  intro r i hr hi
  let A := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := Λ)
  have hη : Function.Injective (Classical.cohomologyMap.{u + 1, u, u, u, u}
      ((etalePullbackPushforwardAdjunction i Λ).unit.app F) 1) := by
    intro a b hab
    apply etaleClosedFiber_abelianUnit_cohomology_one_injective R f (A.obj F)
    rw [← etalePullbackForgetCoefficientsIso_unit i Λ F]
    let μ := A.map ((etalePullbackPushforwardAdjunction i Λ).unit.app F)
    let γ := (etaleAbelianPushforward i).map
      ((etalePullbackForgetCoefficientsIso i Λ).hom.app F)
    exact (Sheaf.H.map_comp_apply μ γ a).trans
      ((congrArg (Sheaf.H.map γ 1) hab).trans (Sheaf.H.map_comp_apply μ γ b).symm)
  exact (etaleCohomologyClosedPushforwardEquiv i Λ ((etalePullback i Λ).obj F) 1).injective.comp hη

end EtaleCohomology
