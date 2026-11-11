/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Set
public import Mathlib.Util.WithWeakNamespace
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.RingTheory.IntegralClosure.Normalization
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.Transcendence
public import Nyll.SchemeTheory.ProjectiveSpace.AwayRatio
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.Morphisms.ProperBirationalIntegral
public import Nyll.SchemeTheory.RingTheory.Dimension.IdealHeightAddKrullDimensionQuotientEqKrullDimension
public import Nyll.SchemeTheory.RingTheory.IntegralClosure.IntegralHeights

/-!
# Affine compactification and normalization

Finite affine charts give a proper birational cover and a compactification. Graph closures
extend maps to proper targets, and normalization gives finite integral models with normal
stalks while preserving the locus where the original model is already normal.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open scoped AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint
open scoped AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData

universe u

noncomputable section

private theorem reduced_image {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [QuasiCompact f] : IsReduced f.image := by
  have hcov : ∀ U : Y.affineOpens, IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    have : _root_.IsReduced (Γ(Y, (U : Y.Opens)) ⧸ f.ker.ideal U) := by
      have : _root_.IsReduced (Γ(Y, (U : Y.Opens)) ⧸ RingHom.ker (f.app U).hom) :=
        isReduced_of_injective (RingHom.kerLift (f.app U).hom) (RingHom.kerLift_injective _)
      exact isReduced_of_injective (Ideal.quotEquivOfEq (f.ker_apply U))
        (Ideal.quotEquivOfEq (f.ker_apply U)).injective
    change IsReduced (Spec (.of (Γ(Y, (U : Y.Opens)) ⧸ f.ker.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover f.image f.ker.subschemeCover.openCover hcov

namespace ChartData

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

/-- The inverse image of the common affine open under the proper cover. -/
abbrev Vu : D.X'.Opens := D.π ⁻¹ᵁ D.Uo

omit [IsNoetherianRing A] [IsIntegral X] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] in
lemma range_ψ'_subset_Vu : Set.range D.ψ' ⊆ Set.range D.Vu.ι := by
  rintro _ ⟨u, rfl⟩
  rw [Scheme.Opens.range_ι]
  change D.π.base (D.ψ'.base u) ∈ D.Uo
  rw [← Scheme.Hom.comp_apply, D.ψ'_π]
  exact u.2

/-- The chart morphism restricted to the inverse image of the common affine open. -/
def ψu : (D.Uo : Scheme.{u}) ⟶ (D.Vu : Scheme.{u}) :=
  IsOpenImmersion.lift D.Vu.ι D.ψ' D.range_ψ'_subset_Vu

omit [IsNoetherianRing A] [IsIntegral X] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] in
@[scoped simp] lemma ψu_ι : D.ψu ≫ D.Vu.ι = D.ψ' := IsOpenImmersion.lift_fac ..

scoped instance : IsOpenImmersion D.ψu := by
  have : IsOpenImmersion (D.ψu ≫ D.Vu.ι) := by rw [ψu_ι]; infer_instance
  exact IsOpenImmersion.of_comp D.ψu D.Vu.ι

omit [IsNoetherianRing A] [IsIntegral X] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] in
lemma ψu_restrict : D.ψu ≫ (D.π ∣_ D.Uo) = 𝟙 _ := by
  rw [← cancel_mono D.Uo.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, ψu_ι, ψ'_π,
    Category.id_comp]

scoped instance : IsClosedImmersion D.ψu := by
  have : IsClosedImmersion (D.ψu ≫ (D.π ∣_ D.Uo)) := by rw [ψu_restrict]; infer_instance
  exact IsClosedImmersion.of_comp (f := D.ψu) (g := D.π ∣_ D.Uo)

scoped instance nonempty_Vu : Nonempty (D.Vu : Scheme.{u}) := ⟨D.ψu.base (Classical.arbitrary _)⟩

scoped instance isIso_ψu : IsIso D.ψu := by
  have : IsIntegral (D.Vu : Scheme.{u}) := isIntegral_of_isOpenImmersion D.Vu.ι
  have hclopen : IsClopen (Set.range D.ψu.base) :=
    ⟨D.ψu.isClosedEmbedding.isClosed_range, D.ψu.isOpenEmbedding.isOpen_range⟩
  have huniv : Set.range D.ψu.base = Set.univ := hclopen.eq_univ (Set.range_nonempty _)
  have : Epi D.ψu.base := (TopCat.epi_iff_surjective _).mpr (Set.range_eq_univ.mp huniv)
  exact (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨inferInstance, ‹_›⟩

omit [IsSeparated f] in
theorem isIso_restrict_Uo : IsIso (D.π ∣_ D.Uo) := by
  rw [IsIso.eq_inv_of_hom_inv_id D.ψu_restrict]
  infer_instance

omit [IsNoetherianRing A] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
lemma Uo_ne_bot : D.Uo ≠ ⊥ := by
  intro h
  obtain ⟨x, hx⟩ := D.Uo_nonempty
  rw [h] at hx
  exact hx

scoped instance isReduced_P : IsReduced D.ιι.image :=
  reduced_image D.ιι

scoped instance irreducibleSpace_P : IrreducibleSpace D.ιι.image := by
  have h : IsIrreducible (D.ιι.ker.support : Set D.PiS) := by
    rw [Scheme.Hom.support_ker, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image _ D.ιι.continuous.continuousOn).closure
  exact Subtype.irreducibleSpace h

scoped instance isIntegral_P : IsIntegral D.ιι.image :=
  isIntegral_of_irreducibleSpace_of_isReduced _

include D in
theorem chow_bir :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
    IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f ∧
    IsIntegral X' ∧ IsIntegral P ∧ ∃ U : X.Opens, U ≠ ⊥ ∧ IsIso (π ∣_ U) := by
  have : IsProper D.prπ := ProjSpace.isProper_prodOverπ A D.e
  exact ⟨D.X', D.ιι.image, D.π, D.ιι.toImage, D.ιι.imageι ≫ D.prπ, inferInstance, inferInstance,
    inferInstance, inferInstance, by rw [← Category.assoc, Scheme.Hom.toImage_imageι, π_comp_f],
    inferInstance, inferInstance, D.Uo, D.Uo_ne_bot, D.isIso_restrict_Uo⟩

end ChartData

theorem main_bir {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f ∧
      IsIntegral X' ∧ IsIntegral P ∧ ∃ U : X.Opens, U ≠ ⊥ ∧ IsIso (π ∣_ U) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨D⟩ := nonempty_chartData f
  exact D.chow_bir

end

with_weak_namespace _root_.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f ∧
      IsIntegral X' ∧ IsIntegral P ∧ ∃ U : X.Opens, U ≠ ⊥ ∧ IsIso (π ∣_ U) :=
  AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.main_bir f

end AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.GraphCompactification

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Topology

universe u

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace GraphClosure
open _root_.AlgebraicGeometry

variable {P Y S : Scheme.{u}} (p : P ⟶ S) (q : Y ⟶ S) (U : P.Opens) (g : (U : Scheme.{u}) ⟶ Y)
  (hg : g ≫ q = U.ι ≫ p)

/-- The pullback of the target along the structural morphism. -/
abbrev Yp : Scheme.{u} := pullback p q

/-- The graph morphism into the pullback. -/
def Γ : (U : Scheme.{u}) ⟶ Yp p q := pullback.lift U.ι g hg.symm

@[scoped simp] lemma Γ_fst : Γ p q U g hg ≫ pullback.fst p q = U.ι := pullback.lift_fst ..
@[scoped simp] lemma Γ_snd : Γ p q U g hg ≫ pullback.snd p q = g := pullback.lift_snd ..

scoped instance isImmersion_Γ : IsImmersion (Γ p q U g hg) := by
  have : IsImmersion (Γ p q U g hg ≫ pullback.fst p q) := by rw [Γ_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst p q)

scoped instance quasiCompact_Γ [IsSeparated q] [QuasiCompact U.ι] :
    QuasiCompact (Γ p q U g hg) := by
  have : QuasiCompact (Γ p q U g hg ≫ pullback.fst p q) := by rw [Γ_fst]; infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst p q)

/-- The scheme-theoretic closure of the graph. -/
abbrev P' : Scheme.{u} := (Γ p q U g hg).image

/-- The closed immersion of the graph closure into the pullback. -/
abbrev α : P' p q U g hg ⟶ Yp p q := (Γ p q U g hg).imageι

/-- The canonical factorization of the graph through its closure. -/
abbrev s : (U : Scheme.{u}) ⟶ P' p q U g hg := (Γ p q U g hg).toImage

/-- The projection of the graph closure to the source. -/
def β : P' p q U g hg ⟶ P := α p q U g hg ≫ pullback.fst p q

/-- The extension of the original morphism to the graph closure. -/
def g' : P' p q U g hg ⟶ Y := α p q U g hg ≫ pullback.snd p q

lemma s_α : s p q U g hg ≫ α p q U g hg = Γ p q U g hg := (Γ p q U g hg).toImage_imageι

@[scoped simp] lemma s_β : s p q U g hg ≫ β p q U g hg = U.ι := by
  rw [β, ← Category.assoc, s_α, Γ_fst]

@[scoped simp] lemma s_g' : s p q U g hg ≫ g' p q U g hg = g := by
  rw [g', ← Category.assoc, s_α, Γ_snd]

lemma g'_q : g' p q U g hg ≫ q = β p q U g hg ≫ p := by
  simp only [g', β, Category.assoc, pullback.condition]

scoped instance isProper_β [IsProper q] : IsProper (β p q U g hg) := by unfold β; infer_instance

scoped instance isReduced_P' [IsReduced P] [IsSeparated q] [QuasiCompact U.ι] :
    IsReduced (P' p q U g hg) :=
  AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.reduced_image
    (Γ p q U g hg)

scoped instance irreducibleSpace_P' [IrreducibleSpace P] [IsSeparated q] [QuasiCompact U.ι]
    [Nonempty (U : Scheme.{u})] : IrreducibleSpace (P' p q U g hg) := by
  have : IrreducibleSpace (U : Scheme.{u}) := by
    have : IsPreirreducible ((U : Set P)) :=
      (IrreducibleSpace.isIrreducible_univ P).2.open_subset U.2
      (Set.subset_univ _)
    have : PreirreducibleSpace U := (isPreirreducible_iff_preirreducibleSpace).mp this
    exact ⟨inferInstance⟩
  have h : IsIrreducible ((Γ p q U g hg).ker.support : Set (Yp p q)) := by
    rw [Scheme.Hom.support_ker, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image _
      (Γ p q U g hg).continuous.continuousOn).closure
  exact Subtype.irreducibleSpace h

scoped instance isIntegral_P' [IsIntegral P] [IsSeparated q] [QuasiCompact U.ι]
    [Nonempty (U : Scheme.{u})] :
    IsIntegral (P' p q U g hg) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The part of the pullback lying over the original open subscheme. -/
abbrev W : (Yp p q).Opens := pullback.fst p q ⁻¹ᵁ U

lemma range_Γ_subset : Set.range (Γ p q U g hg) ⊆ (W p q U : Set (Yp p q)) := by
  rintro _ ⟨x, rfl⟩
  change (pullback.fst p q) (Γ p q U g hg x) ∈ U
  rw [← Scheme.Hom.comp_apply, Γ_fst]
  exact x.2

/-- The graph morphism restricted over the original open subscheme. -/
def ΓW : (U : Scheme.{u}) ⟶ (W p q U : Scheme.{u}) :=
  IsOpenImmersion.lift (W p q U).ι (Γ p q U g hg) (by
    rw [Scheme.Opens.range_ι]; exact range_Γ_subset p q U g hg)

@[scoped simp] lemma ΓW_ι : ΓW p q U g hg ≫ (W p q U).ι = Γ p q U g hg :=
  IsOpenImmersion.lift_fac _ _ _

lemma ΓW_fstRes : ΓW p q U g hg ≫ (pullback.fst p q ∣_ U) = 𝟙 _ := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, ΓW_ι, Γ_fst,
    Category.id_comp]

scoped instance isClosedImmersion_ΓW [IsSeparated q] : IsClosedImmersion (ΓW p q U g hg) := by
  have : IsClosedImmersion (ΓW p q U g hg ≫ (pullback.fst p q ∣_ U)) := by
    rw [ΓW_fstRes]; infer_instance
  exact IsClosedImmersion.of_comp (ΓW p q U g hg) (pullback.fst p q ∣_ U)

lemma closure_range_Γ_inter_subset [IsSeparated q] :
    closure (Set.range (Γ p q U g hg)) ∩ (W p q U : Set (Yp p q)) ⊆ Set.range (Γ p q U g hg) := by
  rintro y ⟨hy, hyW⟩
  have hcl : IsClosed (Set.range (ΓW p q U g hg)) :=
    (ΓW p q U g hg).isClosedEmbedding.isClosed_range
  have hemb := (W p q U).ι.isOpenEmbedding
  obtain ⟨w, rfl⟩ : y ∈ Set.range (W p q U).ι := by rw [Scheme.Opens.range_ι]; exact hyW
  have hw : w ∈ closure (Set.range (ΓW p q U g hg)) := by
    have : Set.range (Γ p q U g hg) = (W p q U).ι '' Set.range (ΓW p q U g hg) := by
      rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, ΓW_ι]
    rw [hemb.isEmbedding.closure_eq_preimage_closure_image, ← this]
    exact hy
  rw [hcl.closure_eq] at hw
  obtain ⟨x, rfl⟩ := hw
  exact ⟨x, by rw [← Scheme.Hom.comp_apply, ΓW_ι]⟩

lemma range_s_eq [IsSeparated q] [QuasiCompact U.ι] :
    Set.range (s p q U g hg) = (β p q U g hg) ⁻¹' (U : Set P) := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    change (β p q U g hg) (s p q U g hg x) ∈ U
    rw [← Scheme.Hom.comp_apply, s_β]
    exact x.2
  · intro z hz
    have h1 : (α p q U g hg) z ∈ closure (Set.range (Γ p q U g hg)) := by
      rw [← Scheme.Hom.support_ker (Γ p q U g hg),
        ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    have h2 : (α p q U g hg) z ∈ (W p q U : Set (Yp p q)) := hz
    obtain ⟨x, hx⟩ := closure_range_Γ_inter_subset p q U g hg ⟨h1, h2⟩
    refine ⟨x, (α p q U g hg).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, s_α, hx]

end AlgebraicGeometry.GraphClosure

end

with_weak_namespace _root_.AlgebraicGeometry
open AbelianVarieties.NOSProofs.GraphCompactification.AlgebraicGeometry.GraphClosure in
theorem exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper
    {P Y S : Scheme.{u}} (p : P ⟶ S) (q : Y ⟶ S) [IsProper q] [IsIntegral P]
    (U : P.Opens) [QuasiCompact U.ι] (hU : (U : Set P).Nonempty)
    (g : (U : Scheme.{u}) ⟶ Y) (hg : g ≫ q = U.ι ≫ p) :
    ∃ (P' : Scheme.{u}) (β : P' ⟶ P) (s : (U : Scheme.{u}) ⟶ P') (g' : P' ⟶ Y),
      IsIntegral P' ∧ IsProper β ∧ IsOpenImmersion s ∧ s ≫ β = U.ι ∧
      Set.range s.base = β.base ⁻¹' (U : Set P) ∧ s ≫ g' = g ∧ g' ≫ q = β ≫ p := by
  have : Nonempty (U : Scheme.{u}) := by
    obtain ⟨x, hx⟩ := hU
    exact ⟨(⟨x, hx⟩ : U)⟩
  exact ⟨P' p q U g hg, β p q U g hg, s p q U g hg, g' p q U g hg, inferInstance, inferInstance,
    inferInstance, s_β p q U g hg, range_s_eq p q U g hg, s_g' p q U g hg, g'_q p q U g hg⟩

end AbelianVarieties.NOSProofs.GraphCompactification
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.VarietyNormalization

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace NormalizationOfVariety
open _root_.AlgebraicGeometry

section Algebra

theorem exists_ringKrullDim_eq_natCast (k : Type u) [Field k] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) := by
  have h := Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := k) (S := A))
  refine ⟨n, ?_⟩
  rw [h, hn, Cardinal.toENat_nat]
  exact WithBot.coe_natCast n

theorem enat_eq_of_add_natCast_eq {a b : ℕ∞} {m : ℕ}
    (h : (a : WithBot ℕ∞) + (m : WithBot ℕ∞) = (b : WithBot ℕ∞) + (m : WithBot ℕ∞)) : a = b := by
  rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
  exact (ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top m)) h

theorem height_eq_height_comap (k : Type u) [Field k] {A B : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra k B]
    [IsScalarTower k A B] [Module.Finite A B] [FaithfulSMul A B] (Q : Ideal B) [Q.IsPrime] :
    Q.height = (Q.comap (algebraMap A B)).height := by
  have : Algebra.FiniteType A B := inferInstance
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Algebra.IsIntegral A B := inferInstance
  have : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  set P : Ideal A := Q.comap (algebraMap A B) with hP
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hdim : ringKrullDim B = ringKrullDim A := by
    have h1 := trdeg_add_eq k A (A := B)
    rw [trdeg_eq_zero (R := A) (A := B), add_zero] at h1
    rw [Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k B,
      Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A, h1]
  have hquot : ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ P) := by
    have : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := Algebra.IsIntegral.quotient
    have hinj : Function.Injective (algebraMap (A ⧸ P) (B ⧸ Q)) :=
      Ideal.quotientMap_injective
    have h1 : ringKrullDim (A ⧸ P) ≤ ringKrullDim (B ⧸ Q) :=
      Algebra.IsIntegral.ringKrullDim_le_of_injective hinj
    have h2 : ringKrullDim (B ⧸ Q) ≤ ringKrullDim (A ⧸ P) :=
      ringKrullDim_le_of_ringHom_isIntegral (algebraMap (A ⧸ P) (B ⧸ Q))
        (algebraMap_isIntegral_iff.mpr inferInstance)
    exact le_antisymm h2 h1
  have hB := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k Q
  have hA := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k P
  have : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast k (A ⧸ P)
  rw [hquot, hm, hdim, ← hA, hm] at hB
  exact enat_eq_of_add_natCast_eq hB

theorem integralClosure_transport {A K L : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing L] [Algebra A L] (e : K ≃ₐ[A] L)
    (hfin : Module.Finite A (integralClosure A K)) :
    IsFractionRing A L ∧ Module.Finite A (integralClosure A L) ∧
      IsDomain (integralClosure A L) ∧ IsIntegrallyClosed (integralClosure A L) := by
  have : IsFractionRing A L := IsLocalization.isLocalization_of_algEquiv _ e
  let Φ : integralClosure A K ≃ₐ[A] integralClosure A L :=
    (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))
  have h1 : Module.Finite A (integralClosure A L) := Module.Finite.equiv Φ.toLinearEquiv
  have : IsDomain (integralClosure A K) := inferInstance
  have h2 : IsDomain (integralClosure A L) :=
    Function.Injective.isDomain Φ.symm.toAlgHom.toRingHom Φ.symm.injective
  have h3 : IsIntegrallyClosed (integralClosure A K) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  have h4 : IsIntegrallyClosed (integralClosure A L) := IsIntegrallyClosed.of_equiv Φ.toRingEquiv
  exact ⟨inferInstance, h1, h2, h4⟩

theorem bijective_algebraMap_integralClosure {A L : Type u} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing L] [Algebra A L] [IsFractionRing A L] :
    Function.Bijective (algebraMap A (integralClosure A L)) := by
  have hbot : integralClosure A L = ⊥ :=
    (IsIntegrallyClosedIn.integralClosure_eq_bot_iff L (IsFractionRing.injective A L)).mpr
      ((isIntegrallyClosed_iff_isIntegrallyClosedIn L).mp inferInstance)
  refine ⟨fun a b hab => IsFractionRing.injective A L
    (congrArg (fun x : integralClosure A L => (x : L)) hab), fun x => ?_⟩
  have hx : (x : L) ∈ (⊥ : Subalgebra A L) := hbot ▸ x.2
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx
  exact ⟨a, Subtype.ext ha⟩

end Algebra

theorem subsingleton_sections_of_eq_bot (X : Scheme.{u}) {U : X.Opens} (h : U = ⊥) :
    Subsingleton Γ(X, U) :=
  CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty h)

theorem primeIdealOf_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (p : Spec Γ(X, U)) (h : hU.fromSpec.base p ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec.base p, h⟩ = p := by
  apply hU.fromSpec.isOpenEmbedding.injective
  exact hU.fromSpec_primeIdealOf ⟨_, h⟩

theorem ringKrullDim_stalk_eq_height {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) = (hU.primeIdealOf ⟨x, hx⟩).asIdeal.height := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (X.presheaf.stalk x)

theorem isIntegrallyClosed_localization_of_stalk {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U)) (h : hU.fromSpec.base p ∈ U)
    (hn : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec.base p))) :
    IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base p)) :=
    (X.presheaf.germ U _ h).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec.base p))
      (hU.primeIdealOf ⟨_, h⟩).asIdeal := hU.isLocalization_stalk ⟨_, h⟩
  rw [primeIdealOf_fromSpec hU p h] at hloc
  let e : Localization.AtPrime p.asIdeal ≃ₐ[Γ(X, U)] X.presheaf.stalk (hU.fromSpec.base p) :=
    IsLocalization.algEquiv p.asIdeal.primeCompl _ _
  exact IsIntegrallyClosed.of_equiv e.symm.toRingEquiv

theorem ringKrullDim_stalk_Spec (R : CommRingCat.{u}) (t : PrimeSpectrum R) :
    ringKrullDim ((Spec R).presheaf.stalk t) = t.asIdeal.height := by
  let : Algebra R ((Spec R).presheaf.stalk t) := StructureSheaf.stalkAlgebra R t
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk t) t.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R t
  exact IsLocalization.AtPrime.ringKrullDim_eq_height t.asIdeal _

theorem isIntegrallyClosed_stalk_Spec (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (t : PrimeSpectrum R) : IsIntegrallyClosed ((Spec R).presheaf.stalk t) := by
  let : Algebra R ((Spec R).presheaf.stalk t) := StructureSheaf.stalkAlgebra R t
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk t) t.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R t
  exact isIntegrallyClosed_of_isLocalization ((Spec R).presheaf.stalk t) t.asIdeal.primeCompl
    t.asIdeal.primeCompl_le_nonZeroDivisors

theorem isIso_morphismRestrict_of_chart {X Y : Scheme.{u}} (g : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) {R : CommRingCat.{u}} (c : Spec R ⟶ X) [IsOpenImmersion c]
    (hrange : (g ⁻¹ᵁ U : Set X) = Set.range c.base) (φ : Γ(Y, U) ⟶ R) [IsIso φ]
    (hc : c ≫ g = Spec.map φ ≫ hU.fromSpec) : IsIso (g ∣_ U) := by
  let e : Spec R ≅ (g ⁻¹ᵁ U : Scheme.{u}) :=
    IsOpenImmersion.isoOfRangeEq c (g ⁻¹ᵁ U).ι (by rw [Scheme.Opens.range_ι]; exact hrange.symm)
  have he : e.hom ≫ (g ⁻¹ᵁ U).ι = c := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h1 : e.hom ≫ (g ∣_ U) = Spec.map φ ≫ hU.isoSpec.inv := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc]
    rw [morphismRestrict_ι, ← Category.assoc, he, hc, IsAffineOpen.isoSpec_inv_ι]
  have h2 : g ∣_ U = e.inv ≫ Spec.map φ ≫ hU.isoSpec.inv := by
    rw [← h1, Iso.inv_hom_id_assoc]
  rw [h2]
  infer_instance

section Chart

variable {k : Type u} [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k))

theorem chart_finiteType [LocallyOfFiniteType q] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI : Algebra k Γ(Y, U) := q.sectionsAlgebra U
    Algebra.FiniteType k Γ(Y, U) := by
  have h1 : (q.appLE ⊤ U le_top).hom.FiniteType :=
    q.finiteType_appLE (isAffineOpen_top _) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

theorem preimage_fromSpecStalk_genericPoint_eq_top [IsIntegral Y] (U : Y.Opens)
    (hUne : (U : Set Y).Nonempty) :
    (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U = ⊤ := by
  have hη : genericPoint Y ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.2).mpr
    (by obtain ⟨y, hy⟩ := hUne; exact ⟨y, Set.mem_univ _, hy⟩)
  refine eq_top_iff.mpr fun pt _ => ?_
  have hsub : Subsingleton (PrimeSpectrum Y.functionField) := inferInstance
  have hpt : pt = IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)) :=
    Subsingleton.elim (α := PrimeSpectrum Y.functionField) pt _
  change (Y.fromSpecStalk (genericPoint Y)).base pt ∈ U
  rw [hpt, Scheme.fromSpecStalk_closedPoint]
  exact hη

include q in
theorem chart_facts [IsIntegral Y] [LocallyOfFiniteType q] (U : Y.Opens) (hU : IsAffineOpen U)
    (hUne : (U : Set Y).Nonempty) :
    let : Algebra Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
      ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    IsFractionRing Γ(Y, U) Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
        (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) ∧
      Module.Finite Γ(Y, U) (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) ∧
      IsDomain (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) ∧
      IsIntegrallyClosed (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) := by
  intro algL
  have : Nonempty U := by obtain ⟨y, hy⟩ := hUne; exact ⟨⟨y, hy⟩⟩
  have hη : genericPoint Y ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.2).mpr
    (by obtain ⟨y, hy⟩ := hUne; exact ⟨y, Set.mem_univ _, hy⟩)
  have htop : (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U = ⊤ :=
    preimage_fromSpecStalk_genericPoint_eq_top U hUne
  let eKL : Y.functionField ≅
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso (Y.presheaf.stalk (genericPoint Y))).symm ≪≫
      (Spec (Y.presheaf.stalk (genericPoint Y))).presheaf.mapIso (eqToIso htop).op
  have happ : (Y.fromSpecStalk (genericPoint Y)).app U =
      Y.presheaf.germ U (genericPoint Y) hη ≫ eKL.hom := by
    rw [Scheme.fromSpecStalk_app hη]
    simp only [eKL, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
    rw [show (homOfLE le_top : (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U ⟶ ⊤) = eqToHom htop from
      Subsingleton.elim _ _]
  have : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  let eA : Y.functionField ≃ₐ[Γ(Y, U)]
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
    AlgEquiv.ofRingEquiv (f := eKL.commRingCatIsoToRingEquiv) (fun a => by
      change eKL.hom (Y.germToFunctionField U a) = ((Y.fromSpecStalk (genericPoint Y)).app U) a
      rw [happ]
      rfl)
  let : Algebra k Γ(Y, U) := q.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(Y, U) := chart_finiteType q hU
  have hfin : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Y.functionField) :=
    IsIntegralClosure.finite_of_finiteType k Γ(Y, U) Y.functionField Y.functionField
      (integralClosure Γ(Y, U) Y.functionField)
  exact integralClosure_transport eA hfin

end Chart

section Main

variable {k : Type u} [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k))
  [IsIntegral Y] [LocallyOfFiniteType q]

theorem chart (U : Y.Opens) (hU : IsAffineOpen U) :
    let : Algebra Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
      ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    ∃ cU : Spec (CommRingCat.of (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))) ⟶
        (Y.fromSpecStalk (genericPoint Y)).normalization,
      IsOpenImmersion cU ∧
      ((Y.fromSpecStalk (genericPoint Y)).fromNormalization ⁻¹ᵁ U :
          Set (Y.fromSpecStalk (genericPoint Y)).normalization) = Set.range cU.base ∧
      cU ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
          Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)))) ≫
          hU.fromSpec := by
  intro sectionAlgebra
  refine ⟨(Y.fromSpecStalk (genericPoint Y)).normalizationOpenCover.f ⟨U, hU⟩,
    by exact (Y.fromSpecStalk (genericPoint Y)).normalizationOpenCover.map_prop ⟨U, hU⟩, ?_, ?_⟩
  · have h := (Y.fromSpecStalk (genericPoint Y)).fromNormalization_preimage ⟨U, hU⟩
    change (Y.fromSpecStalk (genericPoint Y)).fromNormalization ⁻¹ᵁ U = _ at h
    rw [h]
    rfl
  · exact (Y.fromSpecStalk (genericPoint Y)).ι_fromNormalization ⟨U, hU⟩

omit [LocallyOfFiniteType q] in
theorem exists_affine_mem (z : (Y.fromSpecStalk (genericPoint Y)).normalization) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U), (U : Set Y).Nonempty ∧
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base z ∈ U := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y)
    (x := (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base z) (U := ⊤) trivial
  exact ⟨U, hU, ⟨_, hzU⟩, hzU⟩

include q in
theorem isIntegrallyClosed_stalk (z : (Y.fromSpecStalk (genericPoint Y)).normalization) :
    IsIntegrallyClosed ((Y.fromSpecStalk (genericPoint Y)).normalization.presheaf.stalk z) := by
  obtain ⟨U, hU, hUne, hzU⟩ := exists_affine_mem (Y := Y) z
  obtain ⟨cU, hcUopen, hrange, -⟩ := chart (Y := Y) U hU
  have hfacts := chart_facts q U hU hUne
  obtain ⟨-, -, hdom, hic⟩ := hfacts
  let : Algebra Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
        (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
    ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  have hz : z ∈ Set.range cU.base := by rw [← hrange]; exact hzU
  obtain ⟨t, rfl⟩ := hz
  let e := asIso (cU.stalkMap t)
  have h1 := isIntegrallyClosed_stalk_Spec _ t
  exact IsIntegrallyClosed.of_equiv e.symm.commRingCatIsoToRingEquiv

include q in
theorem finite_algebraMap_chart (U : Y.Opens) (hU : IsAffineOpen U) :
    let : Algebra Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
      ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    (algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))).Finite := by
  intro sectionAlgebra
  by_cases hUne : (U : Set Y).Nonempty
  · have hfacts := chart_facts q U hU hUne
    obtain ⟨-, hfin, -, -⟩ := hfacts
    rw [RingHom.Finite]
    convert hfin
  · have hbot : U = ⊥ := by
      ext1
      exact Set.not_nonempty_iff_eq_empty.mp hUne
    have : Subsingleton Γ(Y, U) := subsingleton_sections_of_eq_bot Y hbot
    rw [RingHom.Finite]
    have : Subsingleton (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) := Module.subsingleton Γ(Y, U) _
    exact Module.Finite.of_finite

include q in
theorem isFinite_fromNormalization :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  let : Algebra Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
        (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
    ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  rw [(Y.fromSpecStalk (genericPoint Y)).fromNormalization_app hU]
  have hfin := finite_algebraMap_chart q U hU
  have hiso : ((Y.fromSpecStalk (genericPoint Y)).normalizationObjIso hU).inv.hom.Finite :=
    RingHom.Finite.of_surjective _
      ((Y.fromSpecStalk (genericPoint Y)).normalizationObjIso
        hU).symm.commRingCatIsoToRingEquiv.surjective
  exact hiso.comp hfin

omit [LocallyOfFiniteType q] in
theorem surjective_fromNormalization :
    Function.Surjective (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base := by
  intro y
  have hcl : IsClosed (Set.range (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base) :=
    (Y.fromSpecStalk (genericPoint Y)).fromNormalization.isClosedMap.isClosed_range
  have hη : genericPoint Y ∈
      Set.range (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base := by
    let η : Spec (Y.presheaf.stalk (genericPoint Y)) := IsLocalRing.closedPoint _
    refine ⟨(Y.fromSpecStalk (genericPoint Y)).toNormalization η, ?_⟩
    change ((Y.fromSpecStalk (genericPoint Y)).toNormalization ≫
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization) η = genericPoint Y
    rw [Scheme.Hom.toNormalization_fromNormalization]
    exact Scheme.fromSpecStalk_closedPoint
  have hgen : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
  have hdense : Dense (Set.range (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base) := by
    rw [dense_iff_closure_eq, ← Set.univ_subset_iff, ← hgen]
    exact closure_mono (Set.singleton_subset_iff.mpr hη)
  have : Set.range (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base = Set.univ := by
    rw [← hcl.closure_eq, hdense.closure_eq]
  obtain ⟨z, hz⟩ := (Set.eq_univ_iff_forall.mp this) y
  exact ⟨z, hz⟩

include q in
theorem height_comap_chart (U : Y.Opens) (hU : IsAffineOpen U) (hUne : (U : Set Y).Nonempty)
    (t : letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
      Spec (CommRingCat.of (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)))) :
    let : Algebra Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
      ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    t.asIdeal.height = (t.asIdeal.comap (algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)))).height := by
  intro algL
  have hfacts := chart_facts q U hU hUne
  obtain ⟨hfr, hfin, hdom, -⟩ := hfacts
  have : Nonempty U := by obtain ⟨y, hy⟩ := hUne; exact ⟨⟨y, hy⟩⟩
  let : Algebra k Γ(Y, U) := q.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(Y, U) := chart_finiteType q hU
  let algAbar : Algebra k (integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) :=
    ((algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))).comp
        (algebraMap k Γ(Y, U))).toAlgebra
  have : IsScalarTower k Γ(Y, U) (integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul Γ(Y, U) (integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b hab => ?_
    have := congrArg (fun x : integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) =>
        (x : Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)))
      hab
    exact @IsFractionRing.injective _ _ _ _ _ hfr a b this
  have : t.asIdeal.IsPrime := t.2
  exact height_eq_height_comap k _

include q in
theorem ringKrullDim_stalk_eq (z : (Y.fromSpecStalk (genericPoint Y)).normalization) :
    ringKrullDim ((Y.fromSpecStalk (genericPoint Y)).normalization.presheaf.stalk z) =
      ringKrullDim
        (Y.presheaf.stalk ((Y.fromSpecStalk (genericPoint Y)).fromNormalization.base z)) := by
  obtain ⟨U, hU, hUne, hzU⟩ := exists_affine_mem (Y := Y) z
  obtain ⟨cU, hcUopen, hrange, hcomp⟩ := chart (Y := Y) U hU
  let : Algebra Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
        (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
    ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  have hz : z ∈ Set.range cU.base := by rw [← hrange]; exact hzU
  obtain ⟨t, rfl⟩ := hz
  let e := asIso (cU.stalkMap t)
  rw [ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv]
  refine (ringKrullDim_stalk_Spec _ t).trans ?_
  have hνt : (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base (cU.base t) =
      hU.fromSpec.base ((Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))))).base t) := by
    rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
  have hmem := hνt ▸ hzU
  have hstep : ringKrullDim (Y.presheaf.stalk
      ((Y.fromSpecStalk (genericPoint Y)).fromNormalization.base (cU.base t))) =
      ringKrullDim (Y.presheaf.stalk (hU.fromSpec.base ((Spec.map (CommRingCat.ofHom (algebraMap
        Γ(Y, U) (integralClosure Γ(Y, U) Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))))).base t))) := by
    rw [hνt]
  rw [hstep, ringKrullDim_stalk_eq_height hU _ hmem,
    primeIdealOf_fromSpec hU _ hmem, Spec.map_apply,
    height_comap_chart q U hU hUne t]
  rfl

include q in
theorem isIso_morphismRestrict_fromNormalization (W : Y.Opens)
    (hW : ∀ z ∈ W, IsIntegrallyClosed (Y.presheaf.stalk z)) :
    IsIso ((Y.fromSpecStalk (genericPoint Y)).fromNormalization ∣_ W) := by
  suffices h : ∀ V : (W : Scheme.{u}).affineOpens,
      IsIso (((Y.fromSpecStalk (genericPoint Y)).fromNormalization ∣_ W) ∣_
        (V : (W : Scheme.{u}).Opens)) by
    have := (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (f := (Y.fromSpecStalk (genericPoint Y)).fromNormalization ∣_ W)
      (fun V : (W : Scheme.{u}).affineOpens => (V : (W : Scheme.{u}).Opens))
      (iSup_affineOpens_eq_top _)).mpr (fun V => (MorphismProperty.isomorphisms.iff _).mpr (h V))
    exact (MorphismProperty.isomorphisms.iff _).mp this
  intro V
  rw [← MorphismProperty.isomorphisms.iff,
    (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict (Y.fromSpecStalk (genericPoint Y)).fromNormalization W V),
    MorphismProperty.isomorphisms.iff]
  have hU' : IsAffineOpen (W.ι ''ᵁ (V : (W : Scheme.{u}).Opens)) := V.2.image_of_isOpenImmersion W.ι
  have hU'W : W.ι ''ᵁ (V : (W : Scheme.{u}).Opens) ≤ W := Scheme.Opens.ι_image_le _ _
  generalize W.ι ''ᵁ (V : (W : Scheme.{u}).Opens) = U' at hU' hU'W
  by_cases hU'ne : (U' : Set Y).Nonempty
  · obtain ⟨cU, hcUopen, hrange, hcomp⟩ := chart (Y := Y) U' hU'
    have hfacts := chart_facts q U' hU' hU'ne
    obtain ⟨hfr, -, -, -⟩ := hfacts
    let : Algebra Γ(Y, U')
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U') :=
      ((Y.fromSpecStalk (genericPoint Y)).app U').hom.toAlgebra
    have : Nonempty U' := by obtain ⟨y, hy⟩ := hU'ne; exact ⟨⟨y, hy⟩⟩
    have : IsIntegrallyClosed Γ(Y, U') := by
      refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
      let P : Spec Γ(Y, U') := ⟨p, hp.isPrime⟩
      have hmem : hU'.fromSpec.base P ∈ U' := by
        have : hU'.fromSpec.base P ∈ Set.range hU'.fromSpec.base := ⟨P, rfl⟩
        rwa [IsAffineOpen.range_fromSpec] at this
      exact isIntegrallyClosed_localization_of_stalk hU' P hmem (hW _ (hU'W hmem))
    have hbij : Function.Bijective (algebraMap Γ(Y, U') (integralClosure Γ(Y, U')
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U'))) :=
      bijective_algebraMap_integralClosure
    have : IsIso (CommRingCat.ofHom (algebraMap Γ(Y, U') (integralClosure Γ(Y, U')
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U')))) :=
      (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
    exact isIso_morphismRestrict_of_chart _ hU' cU hrange (CommRingCat.ofHom _) hcomp
  · have hempty : (U' : Set Y) = ∅ := Set.not_nonempty_iff_eq_empty.mp hU'ne
    have : IsEmpty (U' : Scheme.{u}) := ⟨fun x => by
      have hx : (x.1 : Y) ∈ (U' : Set Y) := x.2
      rw [hempty] at hx
      exact hx⟩
    infer_instance

include q in
theorem main :
    ∃ (Y' : Scheme.{u}) (ν : Y' ⟶ Y), IsIntegral Y' ∧
      (∀ z : Y', IsIntegrallyClosed (Y'.presheaf.stalk z)) ∧ IsFinite ν ∧
      Function.Surjective ν.base ∧
      (∀ z : Y', ringKrullDim (Y'.presheaf.stalk z) =
        ringKrullDim (Y.presheaf.stalk (ν.base z))) ∧
      ∀ U : Y.Opens, (∀ z ∈ U, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsIso (ν ∣_ U) :=
  ⟨(Y.fromSpecStalk (genericPoint Y)).normalization,
    (Y.fromSpecStalk (genericPoint Y)).fromNormalization,
    inferInstance, isIntegrallyClosed_stalk q, isFinite_fromNormalization q,
    surjective_fromNormalization (Y := Y), ringKrullDim_stalk_eq q,
    isIso_morphismRestrict_fromNormalization q⟩

end Main

end AlgebraicGeometry.NormalizationOfVariety

with_weak_namespace _root_.AlgebraicGeometry
theorem exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
    (k : Type u) [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k))
    [IsIntegral Y] [LocallyOfFiniteType q] :
    ∃ (Y' : Scheme.{u}) (ν : Y' ⟶ Y), IsIntegral Y' ∧
      (∀ z : Y', IsIntegrallyClosed (Y'.presheaf.stalk z)) ∧ IsFinite ν ∧
      Function.Surjective ν.base ∧
      (∀ z : Y', ringKrullDim (Y'.presheaf.stalk z) =
        ringKrullDim (Y.presheaf.stalk (ν.base z))) ∧
      ∀ U : Y.Opens, (∀ z ∈ U, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsIso (ν ∣_ U) :=
  AbelianVarieties.NOSProofs.VarietyNormalization.AlgebraicGeometry.NormalizationOfVariety.main q

end AbelianVarieties.NOSProofs.VarietyNormalization
end
