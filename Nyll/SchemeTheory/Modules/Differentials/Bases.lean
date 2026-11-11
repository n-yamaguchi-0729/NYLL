/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Nyll.SchemeTheory.Modules.Differentials.Frames
public import Nyll.SchemeTheory.Modules.Differentials.Sections
public import Nyll.SchemeTheory.Modules.Invertible.Determinant
public import Nyll.SchemeTheory.Modules.Invertible.RankOne
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.Frames.BasisMapEqIsAffineOpen
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra

/-!
# Local bases of differentials

Standard smooth charts supply bases on stalks and compatible bases on affine
neighborhoods. The top exterior power is consequently an invertible module.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/




universe u

open CategoryTheory AlgebraicGeometry

namespace SchemeTheory.NOSProofs.DifferentialBases

/-- The map from a stalk is determined by the corresponding map on global sections. -/
theorem stalk_comp_formula {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (y : Y) :
    Y.fromSpecStalk y ≫ f =
      Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ Y.presheaf.germ ⊤ y trivial) := by
  calc
    Y.fromSpecStalk y ≫ f =
        Y.fromSpecStalk y ≫ (f ≫ (Spec (CommRingCat.of R)).toSpecΓ) ≫
          Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
      simp only [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = Spec.map (Y.presheaf.germ ⊤ y trivial) ≫ Spec.map f.appTop ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
      rw [Scheme.toSpecΓ_naturality]
      simpa only [Category.assoc] using
        congrArg (fun h : Spec (Y.presheaf.stalk y) ⟶ Spec Γ(Y, ⊤) =>
          h ≫ Spec.map f.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv)
          (Scheme.fromSpecStalk_toSpecΓ Y y)
    _ = _ := by rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc]

end SchemeTheory.NOSProofs.DifferentialBases

namespace AlgebraicGeometry.SmoothOfRelativeDimension

/-- A standard smooth chart supplies a basis of differentials at a compatible stalk. -/
theorem nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (n : ℕ) [SmoothOfRelativeDimension n f] (y : Y)
    [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) :
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])) := by
  classical
  obtain ⟨U, hU, V, hV, hyV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) y
  obtain ⟨r, s, hys, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n).away
    y ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ ⟨V, hV⟩ ⟨V, hV⟩ hyV hyV e hf (by trivial)
  set W : Y.Opens := Y.basicOpen s with hW
  have hWaff : IsAffineOpen W := hV.basicOpen s
  have hyW : y ∈ W := hys
  have eW : W ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := by
    rw [Scheme.Hom.preimage_top]
    exact le_top
  let algA : Algebra R Γ(Y, W) := ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ W eW).hom.toAlgebra
  let algAs : Algebra Γ(Y, W) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyW⟩
  have hpin : CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ Y.presheaf.germ ⊤ y trivial := by
    exact Spec.map_injective
      (halg.symm.trans (SchemeTheory.NOSProofs.DifferentialBases.stalk_comp_formula f y))
  have : IsScalarTower R Γ(Y, W) (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq fun a => by
    change (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))).hom a =
      (Y.presheaf.germ W y hyW).hom (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ W eW).hom a)
    rw [hpin, ← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE, Category.assoc,
      TopCat.Presheaf.germ_res]
    rfl
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n R Γ(Y, W) := by
    have h₁ :=
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
        n).left
      _ r _ hf₁
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at h₁
    have h₂ : (f.appLE ⊤ W eW).hom.IsStandardSmoothOfRelativeDimension n := h₁
    have h₃ := ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso
      (Scheme.ΓSpecIso (.of R)).inv (f.appLE ⊤ W eW)).mpr h₂
    rw [← CommRingCat.hom_comp] at h₃
    exact h₃
  have := hstd
  have : Algebra.IsStandardSmooth R Γ(Y, W) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Nontrivial Γ(Y, W) := (algebraMap Γ(Y, W) (Y.presheaf.stalk y)).domain_nontrivial
  have hrank : Module.rank Γ(Y, W) Ω[Γ(Y, W)⁄R] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  have : Module.Finite Γ(Y, W) Ω[Γ(Y, W)⁄R] := Module.finite_of_rank_eq_nat hrank
  let bA : Module.Basis (Fin n) Γ(Y, W) Ω[Γ(Y, W)⁄R] :=
    Module.finBasisOfFinrankEq _ _ (Module.finrank_eq_of_rank_eq hrank)
  have := hWaff.isLocalization_stalk ⟨y, hyW⟩
  exact ⟨bA.ofIsLocalizedModule (Y.presheaf.stalk y)
    (hWaff.primeIdealOf ⟨y, hyW⟩).asIdeal.primeCompl
    (KaehlerDifferential.map R R Γ(Y, W) (Y.presheaf.stalk y))⟩

end AlgebraicGeometry.SmoothOfRelativeDimension

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/




open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem _root_.AlgebraicGeometry.Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
    {B : Type u} [CommRing B] {X : Scheme.{u}} (gX : X ⟶ Spec (CommRingCat.of B))
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W) {ι : Type v} :
    let := gX.sectionsAlgebra W; let := gX.sectionsAlgebra W'
    let : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    ∀ [IsScalarTower B Γ(X, W) Γ(X, W')] (b : Module.Basis ι Γ(X, W) (Ω[Γ(X, W)⁄B])),
      ∃ b' : Module.Basis ι Γ(X, W') (Ω[Γ(X, W')⁄B]),
        ∀ i, b' i = KaehlerDifferential.map B B Γ(X, W) Γ(X, W') (b i) := by
  intro algW algW' algWW' _inst b
  have hEt : RingHom.Etale (X.presheaf.map (homOfLE hle).op).hom := by
    have h := HasRingHomProperty.appLE (P := @Etale) (Q := @RingHom.Etale) (𝟙 X) inferInstance
      ⟨W, hW⟩ ⟨W', hW'⟩ (by simpa only [Scheme.Hom.id_preimage] using hle)
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app] at h
    exact h
  have : Algebra.FormallyEtale Γ(X, W) Γ(X, W') := hEt.formallyEtale
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale B Γ(X, W) Γ(X, W')
  refine ⟨(Algebra.TensorProduct.basis Γ(X, W') b).map e, fun i => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul]

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/




open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk
    {k : Type u} [Field k] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n p] (y : Y) :
    let : Algebra k (Y.presheaf.stalk y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄k])) := by
  intro algk
  apply SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
    p n y
  exact SchemeTheory.NOSProofs.DifferentialBases.stalk_comp_formula p y

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace SchemeTheory.NOSProofs.DifferentialBases


open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace TensorProduct

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule

universe u

namespace LocalFrames

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- Restrict an algebraic differential along an open inclusion. -/
noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W)
    (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    (f.kaehlerPresheaf.obj (op W') : Type u) :=
  (f.kaehlerPresheaf.map (homOfLE i).op).hom w

/-- Restrict a section of the sheaf of differentials. -/
noncomputable abbrev res {W' W : X.Opens} (i : W' ≤ W) (s : (Γ(f.kaehler, W) : Type u)) :
    (Γ(f.kaehler, W') : Type u) :=
  f.kaehler.val.presheaf.map (homOfLE i).op s

lemma res_toSh {W' W : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    res f i (f.kaehlerToSections W w) = f.kaehlerToSections W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf)).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

lemma algebraMap_sections_eq {U W : X.Opens} (h : W ≤ U) (a : A) :
    let := f.sectionsAlgebra U
    let := f.sectionsAlgebra W
    algebraMap A Γ(X, W) a = (X.presheaf.map (homOfLE h).op).hom (algebraMap A Γ(X, U) a) := by
  have := congrArg (fun φ => φ.hom a) (f.constToPresheaf.naturality (homOfLE h).op)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
    CommRingCat.hom_comp] at this
  exact this

theorem main (d : ℕ) [SmoothOfRelativeDimension d f] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ e : Fin d → Γ(f.kaehler, U),
      ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(f.kaehler, W),
          ∀ i, b i = f.kaehler.presheaf.map (homOfLE hW).op (e i) := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)
      (f.appLE ⊤ V le_top).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, hP⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).mp hloc
  have hcov : V ≤ ⨆ t : (↑s : Set Γ(X, V)), X.basicOpen (t : Γ(X, V)) :=
    hV.self_le_iSup_basicOpen_iff.mpr hs
  obtain ⟨⟨t, hts⟩, hxt⟩ : ∃ t : (↑s : Set Γ(X, V)), x ∈ X.basicOpen (t : Γ(X, V)) :=
    Opens.mem_iSup.mp (hcov hxV)
  have hU : IsAffineOpen (X.basicOpen t) := hV.basicOpen t
  have : IsLocalization.Away t Γ(X, X.basicOpen t) := hV.isLocalization_basicOpen t
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension d
      ((algebraMap Γ(X, V) Γ(X, X.basicOpen t)).comp (f.appLE ⊤ V le_top).hom) :=
    hP t (Finset.mem_coe.mp hts) Γ(X, X.basicOpen t)
  let algU : Algebra A Γ(X, X.basicOpen t) := f.sectionsAlgebra (X.basicOpen t)
  have hstdU : Algebra.IsStandardSmoothOfRelativeDimension d A Γ(X, X.basicOpen t) := by
    have h1 : (algebraMap Γ(X, V) Γ(X, X.basicOpen t)).comp (f.appLE ⊤ V le_top).hom =
        (f.appLE ⊤ (X.basicOpen t) le_top).hom := by
      change (f.appLE ⊤ V le_top ≫ X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom = _
      exact congrArg CommRingCat.Hom.hom
        (f.appLE_map (U := ⊤) (V := V) le_top (homOfLE (X.basicOpen_le t)).op)
    rw [h1] at hstd
    have h2 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2
      (f.appLE ⊤ (X.basicOpen t) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm hstd
    have h3 : (f.appLE ⊤ (X.basicOpen t) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.toRingHom =
          (f.constToPresheaf.app (op (X.basicOpen t))).hom := by
      ext a; rfl
    rw [h3] at h2
    exact h2
  obtain ⟨b₀⟩ : Nonempty (Module.Basis (Fin d) Γ(X, X.basicOpen t) (Ω[Γ(X, X.basicOpen t)⁄A])) := by
    obtain ⟨ι, σ, _, _, P, hP⟩ := hstdU.out
    let := Fintype.ofFinite ι
    let := Fintype.ofFinite σ
    have hcard : Fintype.card ((Set.range P.map)ᶜ : Set ι) = d := by
      rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP,
        Algebra.Presentation.dimension, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact ⟨P.basisKaehler.reindex (Fintype.equivFinOfCardEq hcard)⟩
  refine ⟨X.basicOpen t, hxt, fun i => f.kaehlerToSections (X.basicOpen t)
    (show (f.kaehlerPresheaf.obj (op (X.basicOpen t)) : Type u) from b₀ i), ?_⟩
  intro W hW hWaff
  let algW : Algebra A Γ(X, W) := f.sectionsAlgebra W
  let algUW : Algebra Γ(X, X.basicOpen t) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
  have : IsScalarTower A Γ(X, X.basicOpen t) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun a => algebraMap_sections_eq f hW a
  have : Algebra.FormallyEtale Γ(X, X.basicOpen t) Γ(X, W) := by
    have hE : RingHom.Etale ((𝟙 X : X ⟶ X).appLE (X.basicOpen t) W hW).hom :=
      HasRingHomProperty.appLE (P := @Etale) (𝟙 X) inferInstance ⟨X.basicOpen t, hU⟩ ⟨W, hWaff⟩ hW
    have hE' : RingHom.Etale (X.presheaf.map (homOfLE hW).op).hom := hE
    exact hE'.formallyEtale
  let κ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A Γ(X, X.basicOpen t) Γ(X, W)
  let bW : Module.Basis (Fin d) Γ(X, W) (Ω[Γ(X, W)⁄A]) :=
    (Algebra.TensorProduct.basis Γ(X, W) b₀).map κ
  have hbW : ∀ i, bW i = pmap f hW
      (show (f.kaehlerPresheaf.obj (op (X.basicOpen t)) : Type u) from b₀ i) := by
    intro i
    change κ (Algebra.TensorProduct.basis Γ(X, W) b₀ i) = _
    rw [Algebra.TensorProduct.basis_apply]
    change KaehlerDifferential.mapBaseChange A Γ(X, X.basicOpen t) Γ(X, W) (1 ⊗ₜ b₀ i) = _
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]
    rfl
  have hbij := AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hWaff
  let τ : (Ω[Γ(X, W)⁄A]) ≃ₗ[Γ(X, W)] (Γ(f.kaehler, W) : Type u) :=
    LinearEquiv.ofBijective (f.kaehlerToSectionsₗ W) hbij
  refine ⟨bW.map τ, fun i => ?_⟩
  rw [Module.Basis.map_apply, hbW]
  change f.kaehlerToSections W (pmap f hW _) = _
  rw [← res_toSh]
  rfl

end LocalFrames

end SchemeTheory.NOSProofs.DifferentialBases

namespace AlgebraicGeometry.Scheme.Hom

open SchemeTheory.NOSProofs.DifferentialBases CategoryTheory

universe u

/-- Smoothness supplies compatible bases on all affine subopens of a neighborhood. -/
theorem exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) [SmoothOfRelativeDimension d f] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ e : Fin d → Γ(f.kaehler, U),
      ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(f.kaehler, W),
          ∀ i, b i = f.kaehler.presheaf.map (homOfLE hW).op (e i) :=
  LocalFrames.main f d x

end AlgebraicGeometry.Scheme.Hom
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/




open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Smooth differentials are locally free and their determinant is invertible. -/
theorem isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    Scheme.Modules.IsLocallyFreeOfRank d f.kaehler ∧
      Scheme.Modules.IsLocallyFreeOfRank 1 (f.topDifferentials d) := by
  have h1 : Scheme.Modules.IsLocallyFreeOfRank d f.kaehler := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hxU, e, he⟩ :=
      Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension f d x
    exact ⟨U, hxU, Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis
      f.kaehler U e
        (Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen f.kaehler e he)⟩
  refine ⟨h1, ?_⟩
  unfold AlgebraicGeometry.Scheme.Hom.topDifferentials
  exact (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr
    (AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h1)

end AlgebraicGeometry.Scheme.Hom

end
