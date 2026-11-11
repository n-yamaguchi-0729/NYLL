/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Util.WithWeakNamespace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Algebra.Group.Defs
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModule
public import Nyll.AlgebraicCurves.Geometry.Picard.Theta.ThetaBundle
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModuleMaps
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.PullbackOfPoint
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPow
public import Nyll.SchemeTheory.Sheaves.IdealSheafComap
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealIsoPullbackModuleComparison
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealComapSupportSubsetRange
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.SectionIdeal

/-!
# Powers of the section ideal under base change on the smooth locus

The section ideal is invertible when the section lies in the relative smooth curve
locus. Its powers commute with base change, and the invertible-ideal comparison
identifies the associated pulled-back modules.
-/

@[expose] public section

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.SmoothSectionPower

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Hom.ker_comp_of_isIso
  IsOpenImmersion.lift
  SmoothOfRelativeDimension
  Scheme.Modules.pullback
  Scheme.Opens.range_ι
  Scheme.Hom
  Scheme.Hom.support_ker
  Spec
  Scheme
  Scheme.IdealSheafData.comap_top
  IsOpenImmersion
  Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
  Scheme.Pullback.range_snd
  isIso_of_isOpenImmersion_of_opensRange_eq_top
  IsClosedImmersion
  IsSeparated
  smoothOfRelativeDimension_isStableUnderBaseChange
  Scheme.Modules
  Scheme.Opens
  IsOpenImmersion.lift_fac
  Scheme.Hom.comp_apply
  Scheme.IdealSheafData
  Scheme.Hom.coe_opensRange
  RelPicard.baseChangeSnd
  RelPicard.rigSection
  RelEffCartierDiv
  RelEffCartierDiv.I
  RelPicard.sectionIdeal
  Scheme.IdealSheafData.IsInvertible
  RelEffCartierDiv.ofPoint
  RelEffCartierDiv.pullbackAlong_ofPoint
  Scheme.Hom.isInvertible_ker_of_comp_eq_id
  Scheme.IdealSheafData.comap_mul
  Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
  Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd rigSection sectionIdeal)

namespace IdealBC

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


theorem comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem sectionIdeal_comap (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    (RelPicard.sectionIdeal c ε t).comap (RelPicard.baseChangeSnd c ψ) =
      RelPicard.sectionIdeal c ε t' :=
  _root_.AlgebraicGeometry.RelPicard.sectionIdeal_comap c ε ψ

theorem isInvertible_sectionIdeal (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (RelPicard.sectionIdeal c ε t).IsInvertible := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  set j := pullback.map (U.ι ≫ c) t c t U.ι (𝟙 T) (𝟙 _)
    (by rw [Category.comp_id])
    (by rw [Category.id_comp, Category.comp_id]) with hj
  have : SmoothOfRelativeDimension 1 (pullback.snd (U.ι ≫ c) t) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      (IsPullback.of_hasPullback (U.ι ≫ c) t) inferInstance
  let εU : Spec (CommRingCat.of R) ⟶ (U : Scheme.{u}) :=
    IsOpenImmersion.lift U.ι ε.1 (by rwa [Scheme.Opens.range_ι])
  have hεU' : εU ≫ U.ι = ε.1 := IsOpenImmersion.lift_fac _ _ _
  set σU : T ⟶ pullback (U.ι ≫ c) t := pullback.lift (t ≫ εU) (𝟙 T)
    (by
      rw [Category.assoc, ← Category.assoc εU, hεU', ε.2,
        Category.comp_id, Category.id_comp]) with hσUdef
  have hσU : σU ≫ pullback.snd (U.ι ≫ c) t = 𝟙 T := by rw [hσUdef, pullback.lift_snd]
  have hσj : σU ≫ j = RelPicard.rigSection c t ε := by
    apply pullback.hom_ext
    · simp only [RelPicard.rigSection, hj, Category.assoc, pullback.lift_fst]
      rw [hσUdef, pullback.lift_fst_assoc, Category.assoc, hεU']
    · simp only [RelPicard.rigSection, hj, Category.assoc, pullback.lift_snd, Category.comp_id]
      exact hσU
  have hinvU : σU.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id σU hσU
  have : IsClosedImmersion (RelPicard.rigSection c t ε) := by
    have : IsClosedImmersion (RelPicard.rigSection c t ε ≫ pullback.snd c t) := by
      rw [RelPicard.rigSection, pullback.lift_snd]; infer_instance
    exact .of_comp (RelPicard.rigSection c t ε) (pullback.snd c t)
  have hcomap : (RelPicard.sectionIdeal c ε t).comap j = σU.ker := by
    change (RelPicard.rigSection c t ε).ker.comap j = σU.ker
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have hsurj : IsIso (pullback.snd j (RelPicard.rigSection c t ε)) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      ext z
      simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rw [Scheme.Pullback.range_snd, ← hσj]
      exact ⟨σU z, (Scheme.Hom.comp_apply _ _ z).symm⟩
    have hfst : pullback.fst j (RelPicard.rigSection c t ε) =
        pullback.snd j (RelPicard.rigSection c t ε) ≫ σU := by
      rw [← cancel_mono j, Category.assoc, hσj]
      exact pullback.condition
    rw [hfst, Scheme.Hom.ker_comp_of_isIso]
  refine Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range j _ ?_ (hcomap ▸ hinvU)
  change ((RelPicard.rigSection c t ε).ker.support : Set ↥(pullback c t)) ⊆ Set.range ⇑j
  rw [Scheme.Hom.support_ker,
    (RelPicard.rigSection c t ε).isClosedEmbedding.isClosed_range.closure_eq, ← hσj]
  rintro _ ⟨z, rfl⟩
  exact ⟨σU z, (Scheme.Hom.comp_apply _ _ z).symm⟩

end AlgebraicGeometry.RelPicard.IdealBC

open AlgebraicGeometry.RelPicard.IdealBC in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (r : ℕ) :
    Nonempty
      ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (((sectionIdeal c ε t) ^ r).module) ≅
      ((sectionIdeal c ε t') ^ r).module) := by
  have hJ : (sectionIdeal c ε t).IsInvertible := isInvertible_sectionIdeal c U ε hεU t
  have hJ' : (sectionIdeal c ε t').IsInvertible := isInvertible_sectionIdeal c U ε hεU t'
  have hcomap : ((sectionIdeal c ε t) ^ r).comap (baseChangeSnd c ψ) =
      (sectionIdeal c ε t') ^ r := by
    rw [comap_pow]
    exact congrArg (· ^ r) (sectionIdeal_comap c ε ψ)
  have := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
    (hJ.pow r) (hcomap ▸ hJ'.pow r)
  exact ⟨asIso (((sectionIdeal c ε t) ^ r).pullbackModuleComparison (baseChangeSnd c ψ)) ≪≫
    eqToIso (by rw [hcomap])⟩
end JacobianVarieties.Picard.Proofs.SmoothSectionPower
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
