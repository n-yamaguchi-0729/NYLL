/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Util.WithWeakNamespace
public import Nyll.SchemeTheory.Pi1.Affine.Over
public import Nyll.SchemeTheory.RingTheory.Flat.Descent
public import Nyll.SchemeTheory.Morphisms.SeparatedQuasiCompactDescent
public import Nyll.SchemeTheory.RingTheory.Descent.FinitePresentation

/-!
# Faithfully flat descent of morphism properties
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace FpqcAffineness
universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MorphismProperty
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace

private theorem sourceLocal_of_ringHomProperty (P : MorphismProperty Scheme.{u})
    (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    [HasRingHomProperty P Q] : IsZariskiLocalAtSource P := inferInstance

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace AffineDescent
open _root_.AlgebraicGeometry

theorem compactSpace_of_surjective_of_isAffine {P Y : Scheme.{u}} (p : P ⟶ Y) [IsAffine P]
    [Surjective p] : CompactSpace Y := by
  refine ⟨?_⟩
  rw [← p.surjective.range_eq]
  exact isCompact_range p.continuous

theorem quasiSeparatedSpace_of_surjective_of_isAffineHom {P Y : Scheme.{u}} (p : P ⟶ Y)
    [IsAffine P] [IsAffineHom p] [Surjective p] : QuasiSeparatedSpace Y := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  have hU : IsAffineOpen (p ⁻¹ᵁ (U : Y.Opens)) := U.2.preimage p
  have hV : IsAffineOpen (p ⁻¹ᵁ (V : Y.Opens)) := V.2.preimage p
  have hc : IsCompact ((p ⁻¹ᵁ (U : Y.Opens) : Set P) ∩ (p ⁻¹ᵁ (V : Y.Opens) : Set P)) :=
    QuasiSeparatedSpace.inter_isCompact _ _ (p ⁻¹ᵁ (U : Y.Opens)).2 hU.isCompact
      (p ⁻¹ᵁ (V : Y.Opens)).2 hV.isCompact
  have himg : p.base '' ((p ⁻¹ᵁ (U : Y.Opens) : Set P) ∩ (p ⁻¹ᵁ (V : Y.Opens) : Set P)) =
      (U : Set Y) ∩ (V : Set Y) := by
    change p.base '' (p.base ⁻¹' (U : Set Y) ∩ p.base ⁻¹' (V : Set Y)) = _
    rw [← Set.preimage_inter, Set.image_preimage_eq _ p.surjective]
  rw [← himg]
  exact hc.image p.continuous

theorem isPullback_specMap_appTop {R S : CommRingCat.{u}} {Y P : Scheme.{u}} (φ : R ⟶ S)
    (g : Y ⟶ Spec R) (p₁ : P ⟶ Spec S) (p₂ : P ⟶ Y) (H : IsPullback p₁ p₂ (Spec.map φ) g)
    [Flat (Spec.map φ)] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsPullback (Spec.map p₁.appTop) (Spec.map p₂.appTop) (Spec.map (Spec.map φ).appTop)
      (Spec.map g.appTop) := by
  have hUST : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ (⊤ : (Spec R).Opens) := le_rfl
  have hUSX : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ (⊤ : (Spec R).Opens) := le_rfl
  have hUY : (⊤ : P.Opens) = p₂ ⁻¹ᵁ (⊤ : Y.Opens) ⊓ p₁ ⁻¹ᵁ (⊤ : (Spec S).Opens) := by
    change (⊤ : P.Opens) = ⊤ ⊓ ⊤
    exact (inf_idem _).symm
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H.flip hUST hUSX hUY
    (isAffineOpen_top (Spec R)) (isAffineOpen_top (Spec S)) (isCompact_univ)
    (isQuasiSeparated_univ)
  have hpo := (isIso_pushoutSection_iff H.flip hUST hUSX hUY).mp hiso
  have htop {X Z : Scheme.{u}} (f : X ⟶ Z) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) :
      f.appLE ⊤ ⊤ e = f.appTop := f.appLE_eq_app
  simp only [htop] at hpo
  exact hpo.op.map Scheme.Spec

theorem isAffine_of_isPullback {R S : CommRingCat.{u}} {Y P : Scheme.{u}} (φ : R ⟶ S)
    (g : Y ⟶ Spec R) (p₁ : P ⟶ Spec S) (p₂ : P ⟶ Y) (H : IsPullback p₁ p₂ (Spec.map φ) g)
    [Surjective (Spec.map φ)] [Flat (Spec.map φ)] [IsAffine P] : IsAffine Y := by
  have hp₂a : IsAffineHom p₂ := MorphismProperty.of_isPullback (P := @IsAffineHom) H inferInstance
  have hp₂s : Surjective p₂ := MorphismProperty.of_isPullback (P := @Surjective) H inferInstance
  have : CompactSpace Y := compactSpace_of_surjective_of_isAffine p₂
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_surjective_of_isAffineHom p₂
  have SQ1 := isPullback_specMap_appTop φ g p₁ p₂ H
  have SQiso : IsPullback (Spec S).toSpecΓ (Spec.map φ) (Spec.map (Spec.map φ).appTop)
      (Spec R).toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality (Spec.map φ)).symm⟩
  have s := H.paste_horiz SQiso
  rw [Scheme.toSpecΓ_naturality p₁, Scheme.toSpecΓ_naturality g] at s
  have SQ2 : IsPullback P.toSpecΓ p₂ (Spec.map p₂.appTop) Y.toSpecΓ :=
    s.of_right (Scheme.toSpecΓ_naturality p₂).symm SQ1
  have e : Spec.map (Spec.map φ).appTop = inv (Spec S).toSpecΓ ≫ Spec.map φ ≫ (Spec R).toSpecΓ := by
    rw [IsIso.eq_inv_comp, ← Scheme.toSpecΓ_naturality]
  have h1 : Surjective (Spec.map (Spec.map φ).appTop) := by rw [e]; infer_instance
  have h2 : Flat (Spec.map (Spec.map φ).appTop) := by rw [e]; infer_instance
  have hcov : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map p₂.appTop) :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) SQ1 h1,
      MorphismProperty.of_isPullback (P := (@Flat : MorphismProperty Scheme.{u})) SQ1 h2⟩,
          inferInstance⟩
  have hiso : (isomorphisms Scheme.{u}) P.toSpecΓ := (isomorphisms.iff _).mpr inferInstance
  have : IsIso Y.toSpecΓ := (isomorphisms.iff _).mp
    (MorphismProperty.of_isPullback_of_descendsAlong (P := isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) SQ2 hcov hiso)
  exact ⟨this⟩

theorem isAffineHom_descendsAlong :
    DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : IsStableUnderBaseChange (@Surjective : MorphismProperty Scheme.{u}) := inferInstance
  have : IsStableUnderBaseChange (@Flat : MorphismProperty Scheme.{u}) :=
    _root_.AlgebraicGeometry.Flat.isStableUnderBaseChange
  have : IsStableUnderBaseChange (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) :=
    IsStableUnderBaseChange.inf (P := @Surjective) (Q := @Flat)
  have hsurj : IsMultiplicative (@Surjective : MorphismProperty Scheme.{u}) := inferInstance
  have hflat : IsMultiplicative (@Flat : MorphismProperty Scheme.{u}) := inferInstance
  have : IsStableUnderComposition (@Surjective : MorphismProperty Scheme.{u}) :=
    hsurj.toIsStableUnderComposition
  have : IsStableUnderComposition (@Flat : MorphismProperty Scheme.{u}) :=
    hflat.toIsStableUnderComposition
  have : IsStableUnderComposition (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) :=
    IsStableUnderComposition.inf (P := @Surjective) (Q := @Flat)
  have : ContainsIdentities (@Flat : MorphismProperty Scheme.{u}) :=
    hflat.toContainsIdentities
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    sourceLocal_of_ringHomProperty _ RingHom.Flat
  have : IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    _root_.AlgebraicGeometry.Affine.affineHomIsZariskiLocalAtTarget
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
    (@IsAffineHom : MorphismProperty Scheme.{u})
    ((@Surjective : MorphismProperty Scheme.{u}) ⊓ (@Flat : MorphismProperty Scheme.{u}))
  · intro X Y f hf
    exact ⟨hf.2, (MorphismProperty.le_def (P := @IsLocalIso) (Q := @Flat)).mp
      (IsLocalIso.le_of_isZariskiLocalAtSource @Flat) f hf.1⟩
  · intro R S Y φ g hφ h
    have : Surjective (Spec.map φ) := hφ.1
    have : Flat (Spec.map φ) := hφ.2
    have : IsAffineHom (pullback.fst (Spec.map φ) g) := h
    have : IsAffine (pullback (Spec.map φ) g) := isAffine_of_isAffineHom (pullback.fst (Spec.map φ)
        g)
    have : IsAffine Y :=
      isAffine_of_isPullback φ g (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _
          _)
    infer_instance

end AffineDescent
end AlgebraicGeometry

open AlgebraicGeometry.AffineDescent in
with_weak_namespace _root_.AlgebraicGeometry.IsAffineHom
theorem descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  isAffineHom_descendsAlong

end FpqcAffineness
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace SeparatedDescent
universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MorphismProperty
open _root_.AlgebraicGeometry

with_weak_namespace _root_.AlgebraicGeometry.IsSeparated
theorem descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  _root_.AlgebraicGeometry.IsSeparated.descendsAlong_fpqc

end SeparatedDescent
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace FinitePresentationDescent
universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace LFPSrcDescent

theorem exists_affine_cover (W : Scheme.{u}) [CompactSpace W] :
    ∃ (T : Scheme.{u}) (p : T ⟶ W), Surjective p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧
        IsAffine T := by
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    FpqcAffineness.sourceLocal_of_ringHomProperty _ RingHom.Flat
  have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    FpqcAffineness.sourceLocal_of_ringHomProperty _ RingHom.FinitePresentation
  let 𝒰 := W.affineCover.finiteSubcover
  let p : ∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ W := Sigma.desc (fun i ↦ 𝒰.f i)
  refine ⟨_, p, ⟨fun x ↦ ?_⟩, ?_, ?_, inferInstance⟩
  · obtain ⟨i, x, rfl⟩ := W.affineCover.finiteSubcover.exists_eq x
    use Sigma.ι W.affineCover.finiteSubcover.X i x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @Flat) (f := fun i => 𝒰.f i)
      (fun _ => inferInstance)
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation)
      (f := fun i => 𝒰.f i) (fun _ => inferInstance)

end LFPSrcDescent

open LFPSrcDescent in
theorem _root_.AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [LocallyOfFinitePresentation f]
        [Surjective f]
    [QuasiCompact f] [LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation g := by
  rw [HasRingHomProperty.iff_appLE (P := (@LocallyOfFinitePresentation : MorphismProperty
      Scheme.{u}))]
  intro U V e
  have hU : IsAffineOpen (U : Z.Opens) := U.2
  have hV : IsAffineOpen (V : Y.Opens) := V.2
  set W : X.Opens := f ⁻¹ᵁ (V : Y.Opens) with hWdef
  have hWc : IsCompact (W : Set X) :=
    QuasiCompact.isCompact_preimage (f := f) _ (V : Y.Opens).isOpen hV.isCompact
  have : CompactSpace (W : X.Opens) := isCompact_iff_compactSpace.mp hWc
  obtain ⟨T, p, hp, hpflat, hplfp, hT⟩ := exists_affine_cover (W : X.Opens)
  let q : T ⟶ Y := p ≫ W.ι ≫ f
  have hT' : IsAffineOpen (⊤ : T.Opens) := isAffineOpen_top T
  have hqapp : ∀ t : T, q t = f (p t).val := fun _ ↦ rfl
  have eq : (⊤ : T.Opens) ≤ q ⁻¹ᵁ (V : Y.Opens) := by
    rintro t -
    rw [Scheme.Hom.mem_preimage, hqapp]
    exact (p t).2
  have eqU : (⊤ : T.Opens) ≤ (q ≫ g) ⁻¹ᵁ (U : Z.Opens) := by
    rw [Scheme.Hom.comp_preimage]; exact eq.trans (Scheme.Hom.preimage_mono q e)
  let Tt : T.affineOpens := ⟨⊤, hT'⟩
  set φRA : (Γ(Z, U) : Type u) →+* Γ(Y, V) := (g.appLE U V e).hom with hφRA
  set φAB : (Γ(Y, V) : Type u) →+* Γ(T, ⊤) := (q.appLE V ⊤ eq).hom with hφAB
  have hcomp : φAB.comp φRA = ((q ≫ g).appLE U ⊤ eqU).hom := by
    rw [hφRA, hφAB, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  have : Flat q := by simp only [q]; infer_instance
  have : LocallyOfFinitePresentation q := by simp only [q]; infer_instance
  have : LocallyOfFinitePresentation (q ≫ g) := by
    have : q ≫ g = p ≫ W.ι ≫ (f ≫ g) := by simp only [q, Category.assoc]
    rw [this]; infer_instance
  have hflat : φAB.Flat := by
    rw [hφAB]; exact HasRingHomProperty.appLE (P := (@Flat : MorphismProperty Scheme.{u})) (f := q)
        inferInstance V Tt eq
  have hfpAB : φAB.FinitePresentation := by
    rw [hφAB]; exact HasRingHomProperty.appLE (P := (@LocallyOfFinitePresentation :
        MorphismProperty Scheme.{u})) (f := q)
        inferInstance V Tt eq
  have hfpRB : (φAB.comp φRA).FinitePresentation := by
    rw [hcomp]; exact HasRingHomProperty.appLE (P := (@LocallyOfFinitePresentation :
        MorphismProperty Scheme.{u})) (f := q ≫ g)
        inferInstance U Tt eqU
  have hsurj : Function.Surjective (PrimeSpectrum.comap φAB) := by
    intro 𝔭
    have hy : hV.fromSpec 𝔭 ∈ (V : Y.Opens) := by
      have : hV.fromSpec 𝔭 ∈ Set.range hV.fromSpec := ⟨𝔭, rfl⟩
      rwa [hV.range_fromSpec] at this
    obtain ⟨x, hx⟩ := f.surjective (hV.fromSpec 𝔭)
    have hxW : x ∈ W := by rw [hWdef, Scheme.Hom.mem_preimage, hx]; exact hy
    obtain ⟨t, ht⟩ := hp.surj ⟨x, hxW⟩
    have hqt : q t = hV.fromSpec 𝔭 := by rw [hqapp, ht, ← hx]
    have htr : t ∈ Set.range hT'.fromSpec := by rw [hT'.range_fromSpec]; trivial
    obtain ⟨𝔮, rfl⟩ := htr
    refine ⟨𝔮, ?_⟩
    apply hV.fromSpec.isOpenEmbedding.injective
    have hnat := IsAffineOpen.SpecMap_appLE_fromSpec q hV hT' eq
    have h1 : hV.fromSpec ((Spec.map (q.appLE V ⊤ eq)) 𝔮) = q (hT'.fromSpec 𝔮) := by
      rw [← Scheme.Hom.comp_apply, hnat, Scheme.Hom.comp_apply]
    rw [← hqt, ← h1, hφAB]
    rfl
  algebraize [φRA, φAB, φAB.comp φRA]
  have : Module.FaithfullyFlat (Γ(Y, V) : Type u) (Γ(T, ⊤) : Type u) :=
    Module.FaithfullyFlat.of_comap_surjective hsurj
  exact Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation (Γ(Z, U) : Type u) (Γ(Y,
      V) : Type u) (Γ(T, ⊤) : Type u)

end FinitePresentationDescent
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace NoetherianDescent
universe u

open CategoryTheory AlgebraicGeometry

namespace NoethDesc

theorem isNoetherianRing_of_faithfullyFlat (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [IsNoetherianRing B] : IsNoetherianRing A := by
  have hmono : StrictMono (Ideal.map (algebraMap A B)) :=
    Monotone.strictMono_of_injective (fun I J h => Ideal.map_mono h)
        Ideal.map_injective_of_faithfullyFlat
  have : WellFoundedGT (Ideal B) := _root_.isNoetherian_iff.mp (isNoetherianRing_iff.mp
      inferInstance)
  have : WellFoundedGT (Ideal A) := hmono.wellFoundedGT
  exact isNoetherianRing_iff.mpr (_root_.isNoetherian_iff.mpr inferInstance)

theorem flat_pi {R : Type*} [CommRing R] {ι : Type*} [Finite ι] (S : ι → Type*) [∀ i, CommRing (S
    i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Flat R (S i)] : Module.Flat R (Π i, S i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have : Module.Flat R (DirectSum ι S) := Module.Flat.directSum_iff.mpr inferInstance
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι S).symm

end NoethDesc

theorem _root_.AlgebraicGeometry.isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f] [IsLocallyNoetherian X]
        :
    IsLocallyNoetherian Y := by
  classical
  refine ⟨fun V => ?_⟩
  have hV : IsAffineOpen (V : Y.Opens) := V.2
  have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage
      V.2.isCompact
  obtain ⟨s, hs, hsU⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hc
  have : Finite s := hs.to_subtype
  have hle : ∀ i : s, ((i : X.affineOpens) : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens) := by
    intro i
    rw [hsU]
    exact le_iSup₂ (f := fun (j : X.affineOpens) (_ : j ∈ s) => (j : X.Opens)) i.1 i.2
  let R := Γ(Y, (V : Y.Opens))
  let S : s → Type _ := fun i => Γ(X, ((i : X.affineOpens) : X.Opens))
  let φ : ∀ i : s, R →+* S i := fun i => (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens)
      (hle i)).hom
  let : ∀ i : s, Algebra R (S i) := fun i => (φ i).toAlgebra
  have : ∀ i : s, Module.Flat R (S i) := fun i => by
    have hflat : (φ i).Flat :=
      HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) f (inferInstance :
          AlgebraicGeometry.Flat f) V i.1 (hle i)
    exact hflat
  have : ∀ i : s, IsNoetherianRing (S i) := fun i => IsLocallyNoetherian.component_noetherian (i :
      X.affineOpens)
  have : Module.Flat R (Π i : s, S i) := NoethDesc.flat_pi S
  have : IsNoetherianRing (Π i : s, S i) := inferInstance
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R (Π i : s, S i))) := by
    intro 𝔭
    let y : Y := hV.fromSpec.base 𝔭
    obtain ⟨x, hx⟩ := (‹Surjective f›).surj y
    have hxV : x ∈ (f ⁻¹ᵁ (V : Y.Opens) : X.Opens) := by
      change f.base x ∈ (V : Y.Opens)
      rw [hx]
      have hy : y ∈ Set.range hV.fromSpec.base := ⟨𝔭, rfl⟩
      rw [hV.range_fromSpec] at hy
      exact hy
    rw [hsU] at hxV
    obtain ⟨i, hi, hxi⟩ : ∃ i ∈ s, x ∈ ((i : X.affineOpens) : X.Opens) := by
      simpa only [TopologicalSpace.Opens.mem_iSup, exists_prop] using hxV
    obtain ⟨𝔮, h𝔮⟩ : ∃ 𝔮 : PrimeSpectrum (S ⟨i, hi⟩),
        (i : X.affineOpens).2.fromSpec.base 𝔮 = x := by
      have : x ∈ Set.range (i : X.affineOpens).2.fromSpec.base := by
        rw [(i : X.affineOpens).2.range_fromSpec]
        exact hxi
      exact this
    have hcomap : PrimeSpectrum.comap (φ ⟨i, hi⟩) 𝔮 = 𝔭 := by
      have hnat := IsAffineOpen.SpecMap_appLE_fromSpec f V.2 (i : X.affineOpens).2 (hle ⟨i, hi⟩)
      have h1 : hV.fromSpec.base ((Spec.map (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens)
          (hle ⟨i, hi⟩))).base 𝔮) = hV.fromSpec.base 𝔭 := by
        have h2 := congrArg (fun k : Spec Γ(X, ((i : X.affineOpens) : X.Opens)) ⟶ Y =>
          k.base 𝔮) hnat
        change hV.fromSpec.base ((Spec.map (f.appLE (V : Y.Opens)
          ((i : X.affineOpens) : X.Opens) (hle ⟨i, hi⟩))).base 𝔮) =
            f.base ((i : X.affineOpens).2.fromSpec.base 𝔮) at h2
        exact h2.trans ((congrArg f.base h𝔮).trans hx)
      exact hV.fromSpec.isOpenEmbedding.injective h1
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun i : s => S i) ⟨i, hi⟩) 𝔮, ?_⟩
    rw [← hcomap, ← PrimeSpectrum.comap_comp_apply]
    rfl
  have : Module.FaithfullyFlat R (Π i : s, S i) := Module.FaithfullyFlat.of_comap_surjective hsurj
  exact NoethDesc.isNoetherianRing_of_faithfullyFlat R (Π i : s, S i)

end NoetherianDescent
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace NoetherianFinitePresentation
open AlgebraicGeometry CategoryTheory

universe u

with_weak_namespace _root_.AlgebraicGeometry
theorem locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : X ⟶ Y) (w : h ≫ g = f)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation h := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : LocallyOfFiniteType (h ≫ g) := by rw [w]; infer_instance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h g
  infer_instance

end NoetherianFinitePresentation
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace AffineFlatDescent
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TensorProduct
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Flat
open _root_.AlgebraicGeometry.Flat
end Flat
theorem Flat.of_comp_aux {X Y S : Scheme.{u}} (σ : X ⟶ Y) (y : Y ⟶ S)
    [hc : Flat (σ ≫ y)] [IsAffineHom σ] [Flat σ] [Surjective σ] : Flat y := by
  rw [HasRingHomProperty.iff_appLE (P := (@Flat : MorphismProperty Scheme.{u}))]
  intro W V e
  let U : X.affineOpens := ⟨σ ⁻¹ᵁ (V : Y.Opens), V.2.preimage σ⟩
  have eU : (U : X.Opens) ≤ σ ⁻¹ᵁ (V : Y.Opens) := le_rfl
  have eWU : (U : X.Opens) ≤ (σ ≫ y) ⁻¹ᵁ (W : S.Opens) := fun x hx => e hx
  let φ := y.appLE W V e
  let ψ := σ.appLE V U eU
  have hcomp : φ ≫ ψ = (σ ≫ y).appLE W U eWU := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have hAC : ((σ ≫ y).appLE W U eWU).hom.Flat := HasRingHomProperty.appLE @Flat (σ ≫ y) hc W U eWU
  have hψflat : ψ.hom.Flat := HasRingHomProperty.appLE @Flat σ inferInstance V U eU
  have hψsurj : Function.Surjective (PrimeSpectrum.comap ψ.hom) := by
    intro p
    obtain ⟨x, hx⟩ := σ.surjective (V.2.fromSpec p)
    have hxU : x ∈ (U : X.Opens) := by
      change σ x ∈ (V : Y.Opens)
      rw [hx]
      exact V.2.range_fromSpec.le ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := U.2.range_fromSpec.ge hxU
    refine ⟨q, V.2.isOpenImmersion_fromSpec.base_open.injective ?_⟩
    change V.2.fromSpec (Spec.map ψ q) = V.2.fromSpec p
    rw [← hx, ← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec σ V.2 U.2 eU,
      Scheme.Hom.comp_apply]
  have hψ : ψ.hom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hψflat, hψsurj⟩
  rw [← hcomp, CommRingCat.hom_comp] at hAC
  algebraize [φ.hom, ψ.hom, ψ.hom.comp φ.hom]
  exact Module.Flat.of_flat_of_faithfullyFlat_right Γ(S, W) Γ(Y, V) Γ(X, U)
end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Flat.of_comp_of_isAffineHom_of_flat_of_surjective {X Y S :
    Scheme.{u}}
    (σ : X ⟶ Y) (y : Y ⟶ S) [Flat (σ ≫ y)] [IsAffineHom σ] [Flat σ] [Surjective σ] : Flat y :=
  AlgebraicGeometry.Flat.of_comp_aux σ y

end AffineFlatDescent
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Flat_of_comp_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace FlatDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace EAlpha

theorem surjective_specMap_stalkMap {X U : Scheme.{u}} (c : X ⟶ U) [Flat c] (x : ↥X) :
    Surjective (Spec.map (c.stalkMap x)) := by
  let : Algebra (U.presheaf.stalk (c.base x)) (X.presheaf.stalk x) := (c.stalkMap x).hom.toAlgebra
  have : Module.Flat (U.presheaf.stalk (c.base x)) (X.presheaf.stalk x) := Flat.stalkMap c x
  have : IsLocalHom (algebraMap (U.presheaf.stalk (c.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (c.stalkMap x).hom)
  have : Module.FaithfullyFlat (U.presheaf.stalk (c.base x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (surjective_iff (Spec.map (c.stalkMap x))).mpr
      PrimeSpectrum.comap_surjective_of_faithfullyFlat

theorem main {X U Y : Scheme.{u}} (c : X ⟶ U) [Flat c] [Surjective c] (p : U ⟶ Y) [Flat (c ≫ p)] :
    Flat p := by
  refine Flat.of_stalkMap p fun u => ?_
  obtain ⟨x, rfl⟩ := c.surjective u
  have hcomp : ((c ≫ p).stalkMap x).hom.Flat := Flat.stalkMap (c ≫ p) x
  rw [Scheme.Hom.stalkMap_comp] at hcomp
  have h1 : Flat (Spec.map (c.stalkMap x)) := Flat.SpecMap_iff.2 (Flat.stalkMap c x)
  have h2 : Surjective (Spec.map (c.stalkMap x)) := surjective_specMap_stalkMap c x
  have h3 : Flat (Spec.map (c.stalkMap x) ≫ Spec.map (p.stalkMap (c.base x))) := by
    rw [← Spec.map_comp]; exact Flat.SpecMap_iff.2 hcomp
  exact Flat.SpecMap_iff.1
    (AlgebraicGeometry.Flat.of_comp_of_isAffineHom_of_flat_of_surjective (Spec.map (c.stalkMap x))
      (Spec.map (p.stalkMap (c.base x))))

end EAlpha

theorem _root_.AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective {X U Y : Scheme.{u}} (c : X ⟶
    U) [Flat c]
    [Surjective c] (p : U ⟶ Y) [Flat (c ≫ p)] : Flat p :=
  EAlpha.main c p

end FlatDescent
end NOSProofs
end AbelianVarieties
end
