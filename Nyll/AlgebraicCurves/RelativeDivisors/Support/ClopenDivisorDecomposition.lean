/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Support.HenselianRegularDivisorBlock
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.IdealProductDivisor
import Mathlib.RingTheory.Ideal.Operations

/-!
# Complementary finite-flat divisor blocks

An actual clopen decomposition of the divisor scheme produces two relative
divisors over the original local base. Their full ideals are coprime and
multiply to the original ideal. The existing construction of products of
relative divisors then proves additivity of their actual finite-flat ranks.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RelEffCartierDiv

/-- A clopen part of a relative divisor over a local ring is an actual
relative divisor, of the rank computed at the closed point. -/
theorem exists_clopenBlock
    {R : Type u} [CommRing R] [IsLocalRing R]
    {C S : Scheme.{u}} {c : C ⟶ S} {n : ℕ}
    {t : Spec (.of R) ⟶ S} (D : RelEffCartierDiv c n t)
    (V : D.I.subscheme.Opens) (hV : IsClosed (V : Set D.I.subscheme)) :
    ∃ (m : ℕ) (D₀ : RelEffCartierDiv c m t),
      D₀.I = (V.ι ≫ D.I.subschemeι).ker := by
  let p := D.I.subschemeι ≫ pullback.snd c t
  have : IsFinite p := D.isFinite
  have : Flat p := D.flat
  have : LocallyOfFinitePresentation p := D.locallyOfFinitePresentation
  have : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV)
  let j : V.toScheme ⟶ pullback c t := V.ι ≫ D.I.subschemeι
  have : IsClosedImmersion j :=
    inferInstanceAs (IsClosedImmersion (V.ι ≫ D.I.subschemeι))
  let e : V.toScheme ≅ j.ker.subscheme := asIso j.toImage
  have hι : j.ker.subschemeι = e.inv ≫ j := by
    apply (cancel_epi e.hom).1
    change j.toImage ≫ j.imageι = e.hom ≫ (e.inv ≫ j)
    rw [Scheme.Hom.toImage_imageι, e.hom_inv_id_assoc]
  have hproj : j.ker.subschemeι ≫ pullback.snd c t = e.inv ≫ (V.ι ≫ p) := by
    rw [hι]
    simp only [j, p, Category.assoc]
  let m : ℕ := (V.ι ≫ p).finrank (IsLocalRing.closedPoint R)
  have hrank (x : Spec (.of R)) : (V.ι ≫ p).finrank x = m := by
    have hlc := (V.ι ≫ p).isLocallyConstant_finrank
    have hx : IsLocalRing.closedPoint R ∈
        (V.ι ≫ p).finrank ⁻¹' {(V.ι ≫ p).finrank x} :=
      (IsLocalRing.specializes_closedPoint x).mem_closed
        (hlc.isClopen_fiber ((V.ι ≫ p).finrank x)).isClosed rfl
    exact hx.symm
  refine ⟨m,
    { I := j.ker
      isFinite := by rw [hproj]; infer_instance
      flat := by rw [hproj]; infer_instance
      locallyOfFinitePresentation := by rw [hproj]; infer_instance
      finrank_eq := fun x => by
        rw [hproj, Scheme.Hom.finrank_comp_left_of_isIso]
        exact hrank x }, rfl⟩

/-- Complementary clopen pieces retain the original full ideal as their
product. This is a scheme-theoretic equality, including all nilpotents. -/
theorem ideal_eq_mul_clopen_complement
    {C S T : Scheme.{u}} {c : C ⟶ S} {n : ℕ} {t : T ⟶ S}
    (D : RelEffCartierDiv c n t) (V : D.I.subscheme.Opens)
    (hV : IsClosed (V : Set D.I.subscheme)) :
    let W : D.I.subscheme.Opens := ⟨(V : Set D.I.subscheme)ᶜ, hV.isOpen_compl⟩
    D.I = (V.ι ≫ D.I.subschemeι).ker * (W.ι ≫ D.I.subschemeι).ker := by
  classical
  intro W
  have : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV)
  have : IsClosedImmersion W.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact V.isOpen.isClosed_compl)
  let j₀ := V.ι ≫ D.I.subschemeι
  let j₁ := W.ι ≫ D.I.subschemeι
  have hs₀ : (j₀.ker.support : Set ↥(pullback c t)) = Set.range j₀ := by
    rw [Scheme.Hom.support_ker, j₀.isClosedEmbedding.isClosed_range.closure_eq]
  have hs₁ : (j₁.ker.support : Set ↥(pullback c t)) = Set.range j₁ := by
    rw [Scheme.Hom.support_ker, j₁.isClosedEmbedding.isClosed_range.closure_eq]
  have hsup : j₀.ker ⊔ j₁.ker = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_sup]
    apply SetLike.coe_injective
    change ((j₀.ker.support : Set ↥(pullback c t)) ∩ j₁.ker.support) = ∅
    rw [hs₀, hs₁]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy : V.ι x = W.ι y := D.I.subschemeι.isClosedEmbedding.injective
      (show D.I.subschemeι (V.ι x) = D.I.subschemeι (W.ι y) from hx.trans hy.symm)
    have hxV : V.ι x ∈ V := x.property
    rw [hxy] at hxV
    exact y.property hxV
  let opens : Bool → D.I.subscheme.Opens := fun b => if b then V else W
  have hopen : IsOpenCover opens := by
    change (⨆ b, opens b) = ⊤
    apply top_le_iff.mp
    intro x _
    by_cases hx : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true, hx⟩
    · exact Opens.mem_iSup.mpr ⟨false, hx⟩
  let cover := D.I.subscheme.openCoverOfIsOpenCover opens hopen
  have hcover : (⨅ b : Bool, ((opens b).ι ≫ D.I.subschemeι).ker) = D.I :=
    (D.I.subschemeι.iInf_ker_openCover_map_comp cover).trans D.I.ker_subschemeι
  have hinf : j₀.ker ⊓ j₁.ker = D.I := by
    rw [iInf_bool_eq] at hcover
    exact hcover
  apply Scheme.IdealSheafData.ext
  funext A
  change D.I.ideal A = j₀.ker.ideal A * j₁.ker.ideal A
  rw [Ideal.mul_eq_inf_of_coprime
    (congrArg (fun I : (pullback c t).IdealSheafData => I.ideal A) hsup)]
  exact congrArg (fun I : (pullback c t).IdealSheafData => I.ideal A) hinf.symm

/-- Every clopen split constructs both finite-flat blocks, their product
ideal, and the equality between the original degree and their degree sum. -/
theorem exists_clopen_decomposition
    {R : Type u} [CommRing R] [IsLocalRing R]
    {C S : Scheme.{u}} {c : C ⟶ S}
    [IsSeparated c] [SmoothOfRelativeDimension 1 c] {n : ℕ}
    {t : Spec (.of R) ⟶ S} (D : RelEffCartierDiv c n t)
    (V : D.I.subscheme.Opens) (hV : IsClosed (V : Set D.I.subscheme)) :
    let W : D.I.subscheme.Opens := ⟨(V : Set D.I.subscheme)ᶜ, hV.isOpen_compl⟩
    ∃ (m k : ℕ) (D₀ : RelEffCartierDiv c m t) (D₁ : RelEffCartierDiv c k t),
      D₀.I = (V.ι ≫ D.I.subschemeι).ker ∧
      D₁.I = (W.ι ≫ D.I.subschemeι).ker ∧
      D.I = D₀.I * D₁.I ∧ n = m + k := by
  intro W
  obtain ⟨m, D₀, hD₀⟩ := exists_clopenBlock D V hV
  obtain ⟨k, D₁, hD₁⟩ := exists_clopenBlock D W V.isOpen.isClosed_compl
  have hmul : D.I = D₀.I * D₁.I := by
    rw [hD₀, hD₁]
    exact ideal_eq_mul_clopen_complement D V hV
  obtain ⟨E, hE⟩ := D₀.exists_I_eq_mul D₁
  have hDE : D.I = E.I := hmul.trans hE.symm
  have hdegree : n = m + k :=
    (D.finrank_eq (IsLocalRing.closedPoint R)).symm.trans
      ((congrArg (fun I : (pullback c t).IdealSheafData =>
        (I.subschemeι ≫ pullback.snd c t).finrank (IsLocalRing.closedPoint R)) hDE).trans
        (E.finrank_eq (IsLocalRing.closedPoint R)))
  exact ⟨m, k, D₀, D₁, hD₀, hD₁, hmul, hdegree⟩

/-- The regular Henselian block has an actual complementary finite-flat
block, with the original full ideal and degree decomposed accordingly. -/
theorem exists_henselian_regularBlock_decomposition
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {C S : Scheme.{u}} {c : C ⟶ S}
    [IsSeparated c] [SmoothOfRelativeDimension 1 c] {n : ℕ}
    {t : Spec (.of R) ⟶ S} (D : RelEffCartierDiv c n t) (U : C.Opens) :
    let p := D.I.subschemeι ≫ pullback.snd c t
    let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    ∃ (V : D.I.subscheme.Opens) (hV : IsClosed (V : Set D.I.subscheme)),
      let W : D.I.subscheme.Opens := ⟨(V : Set D.I.subscheme)ᶜ, hV.isOpen_compl⟩
      (pullback.fst p r ⁻¹' (V : Set D.I.subscheme) =
        (pullback.fst p r ≫ D.I.subschemeι ≫ pullback.fst c t) ⁻¹' (U : Set C)) ∧
      ∃ (m k : ℕ) (D₀ : RelEffCartierDiv c m t) (D₁ : RelEffCartierDiv c k t),
        D₀.I = (V.ι ≫ D.I.subschemeι).ker ∧
        D₁.I = (W.ι ≫ D.I.subschemeι).ker ∧
        D₀.SupportedIn U ∧ D.I = D₀.I * D₁.I ∧ n = m + k := by
  intro p r
  obtain ⟨V, hV, hVr, _m, A, hA, hAU⟩ := D.exists_henselian_regularBlock U
  obtain ⟨m, k, D₀, D₁, hD₀, hD₁, hmul, hdegree⟩ :=
    exists_clopen_decomposition D V hV
  have hD₀U : D₀.SupportedIn U := by
    change (D₀.I.support : Set ↥(pullback c t)) ⊆ _
    rw [hD₀, ← hA]
    exact hAU
  exact ⟨V, hV, hVr, m, k, D₀, D₁, hD₀, hD₁, hD₀U, hmul, hdegree⟩

end AlgebraicGeometry.RelEffCartierDiv
