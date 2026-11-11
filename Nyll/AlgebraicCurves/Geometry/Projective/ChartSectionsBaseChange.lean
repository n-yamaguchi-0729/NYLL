/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.FinCases
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
public import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.OrderedAffineCoverComap

/-!
# Coordinate sections under coefficient base change

These maps retain the actual homogeneous localization, coordinate ratios and
pullback charts. Section naturality uses a specified commutative square and two
open containments, without a flatness, field or affine-morphism hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjSpace.ChartSectionsBaseChange

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
  (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
  (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
  (e : Z' ⟶ Z)

local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "𝒜B" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B

omit [IsAffineHom ι] [IsAffineHom ι'] in
/-- Coefficient base change preserves the actual pulled-back coordinate chart. -/
theorem preimage_pullbackChart (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (j : Fin (n + 1)) :
    e ⁻¹ᵁ ProjSpace.pullbackChart ι j = ProjSpace.pullbackChart ι' j := by
  rw [ProjSpace.pullbackChart_eq, ProjSpace.pullbackChart_eq, ← Scheme.Hom.comp_preimage, hcomp,
    Scheme.Hom.comp_preimage, ProjSpace.map_preimage_basicOpen_X]

/-- Coefficient base change preserves intersections in the standard affine covers. -/
theorem preimage_inter (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) {i : ℕ} (s :
  (ProjSpace.stdCoverPullback ι).Idx i) :
    e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s = (ProjSpace.stdCoverPullback ι').inter s := by
  change {t : Fin (i + 1) → ULift.{u} (Fin (n + 1)) // StrictMono t} at s
  change e ⁻¹ᵁ (⨅ j, (ProjSpace.stdCoverPullback ι).U (s.1 j)) = ⨅ j, (ProjSpace.stdCoverPullback
    ι').U (s.1 j)
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  congr 1
  funext j
  rw [ProjSpace.stdCoverPullback_U, ProjSpace.stdCoverPullback_U, ProjSpace.stdCover_U,
    ProjSpace.stdCover_U,
    ← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage, ProjSpace.map_preimage_basicOpen_X]

/-- An intersection of standard affine charts lies in each of its factors. -/
theorem inter_le_pullbackChart {W : Scheme.{u}} {R : Type u} [CommRing R]
    (φ : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ]
    {i : ℕ} (s : (ProjSpace.stdCoverPullback φ).Idx i) (t : Fin (i + 1)) :
    (ProjSpace.stdCoverPullback φ).inter s ≤ ProjSpace.pullbackChart φ ((s.1 t).down) := by
  change {t : Fin (i + 1) → ULift.{u} (Fin (n + 1)) // StrictMono t} at s
  refine (Scheme.OrderedAffineCover.inter_le (ProjSpace.stdCoverPullback φ) s t).trans ?_
  rw [ProjSpace.stdCoverPullback_U, ProjSpace.stdCover_U, ProjSpace.pullbackChart_eq]

/-- Finite intersections in the standard pulled-back cover are affine. -/
theorem isAffineOpen_inter {W : Scheme.{u}} {R : Type u} [CommRing R]
    (φ : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ]
    {i : ℕ} (s : (ProjSpace.stdCoverPullback φ).Idx i) :
    IsAffineOpen ((ProjSpace.stdCoverPullback φ).inter s) := by
  change {t : Fin (i + 1) → ULift.{u} (Fin (n + 1)) // StrictMono t} at s
  have : (ProjSpace.stdCoverPullback φ).inter s = φ ⁻¹ᵁ (⨅ j, (ProjSpace.stdCover R n).U (s.1 j))
    := by
    change (⨅ j, (ProjSpace.stdCoverPullback φ).U (s.1 j)) = _
    rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
    rfl
  rw [this]
  refine IsAffineOpen.preimage ?_ φ
  have key : ∀ (m : ℕ) (g : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R),
      (⨅ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (g j))
        = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (∏ j, g j) := by
    intro m
    induction m with
    | zero =>
      intro g
      rw [Fin.prod_univ_one]
      exact le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    | succ m ih =>
      intro g
      rw [Fin.prod_univ_succ, Proj.basicOpen_mul, ← ih (fun j => g j.succ)]
      exact le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  have hdeg : ∀ (m : ℕ) (t : Fin (m + 1) → Fin (n + 1)),
      (∏ j, MvPolynomial.X (t j) : MvPolynomial (Fin (n + 1)) R) ∈
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (m + 1) := by
    intro m t
    have := SetLike.prod_mem_graded (A := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (F := (Finset.univ : Finset (Fin (m + 1)))) (i := fun _ => (1 : ℕ)) (g := fun j =>
        MvPolynomial.X (t j))
      (fun j _ => ProjSpace.X_mem_one R n (t j))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      using this
  simp only [ProjSpace.stdCover_U]
  rw [key]
  exact Proj.isAffineOpen_basicOpen _ _ (hdeg i (fun j => (s.1 j).down)) (Nat.succ_pos _)

/-- A coordinate is the image of the same coordinate over the base ring. -/
theorem X_eq_mvMapGraded_mul_one (i : Fin (n + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) B) = (ProjSpace.mvMapGraded A B n)
      (MvPolynomial.X i) * 1 := by
  rw [ProjSpace.mvMapGraded_X, mul_one]

/-- The unit has homogeneous degree zero over the coefficient ring. -/
theorem one_mem_zero : (1 : MvPolynomial (Fin (n + 1)) B) ∈ (MvPolynomial.homogeneousSubmodule (Fin
  (n + 1)) B) 0 :=
  SetLike.one_mem_graded _

/-- The actual homogeneous-localization homomorphism induced by the coefficient algebra map. -/
noncomputable def toB (i : Fin (n + 1)) : Away 𝒜A (MvPolynomial.X i) →+* Away 𝒜B (MvPolynomial.X i)
  :=
  (awayMap 𝒜B (one_mem_zero (n := n) B) (X_eq_mvMapGraded_mul_one (A := A) B i)).comp
    (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))

/-- The coefficient localization map preserves the coordinate ratios. -/
theorem toB_ratio (i j : Fin (n + 1)) : toB (A := A) B i (ProjSpace.ratio A n i j) =
  ProjSpace.ratio B n i j := by
  apply HomogeneousLocalization.val_injective
  rw [toB, RingHom.comp_apply, ProjSpace.ratio, Away.map_mk]
  rw [Away.mk, val_awayMap_mk, ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp only [ProjSpace.mvMapGraded_X, one_pow, mul_one]⟩

omit [IsAffineHom ι] [IsAffineHom ι'] in
/-- The actual chart-section map commutes with a given coefficient square. -/
theorem restrictFun_app_pullAway (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (i : Fin (n + 1))
    (a : Away 𝒜A (MvPolynomial.X i)) {W' : Z'.Opens}
    (h₁ : W' ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i) (h₂ : W' ≤ ProjSpace.pullbackChart ι' i) :
    ProjSpace.restrictFun h₁ ((e.app (ProjSpace.pullbackChart ι i)).hom
        ((ι.app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom ((Proj.awayToSection 𝒜A (MvPolynomial.X
          i)).hom a)))
      = ProjSpace.restrictFun h₂ ((ι'.app (Proj.basicOpen 𝒜B (MvPolynomial.X i))).hom
          ((Proj.awayToSection 𝒜B (MvPolynomial.X i)).hom (toB (A := A) B i a))) := by
  have s1 : (e.app (ProjSpace.pullbackChart ι i)).hom
      ((ι.app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom ((Proj.awayToSection 𝒜A (MvPolynomial.X
        i)).hom a))
      = ((e ≫ ι).app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom ((Proj.awayToSection 𝒜A
        (MvPolynomial.X i)).hom a) := by
    rfl
  rw [s1]
  have s2 := Scheme.Hom.congr_app hcomp (Proj.basicOpen 𝒜A (MvPolynomial.X i))
  rw [s2]
  change ProjSpace.restrictFun h₁ ((Z'.presheaf.map _).hom
      ((ι'.app ((ProjSpace.map A B n) ⁻¹ᵁ Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom
        (((ProjSpace.map A B n).app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom
          ((Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom a)))) = _
  have s3 : ((ProjSpace.map A B n).app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom
      ((Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom a)
      = (Proj.awayToSection 𝒜B ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))).hom
          (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a) := by
    have := Proj.awayToSection_comp_appLE (ProjSpace.mvMapGraded A B n)
      (ProjSpace.irrelevant_le_map_mvMapGraded A B n)
      (ProjSpace.X_mem_one A n i)
    have h := congrArg (fun ψ => ψ.hom a) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    have h' : ((ProjSpace.map A B n).appLE (Proj.basicOpen 𝒜A (MvPolynomial.X i))
        ((ProjSpace.map A B n) ⁻¹ᵁ Proj.basicOpen 𝒜A (MvPolynomial.X i)) le_rfl).hom
        ((Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom a)
        = (Proj.awayToSection 𝒜B ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))).hom
          (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a) := h
    rw [Scheme.Hom.appLE_eq_app] at h'
    exact h'
  rw [s3]
  have s4 := congrArg (fun ψ => ψ.hom (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a))
    (Proj.awayMap_awayToSection 𝒜B (one_mem_zero (n := n) B) (X_eq_mvMapGraded_mul_one (A := A) B
      i))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at s4
  have s5 : (Proj.awayToSection 𝒜B (MvPolynomial.X i)).hom (toB (A := A) B i a)
      = ((Proj 𝒜B).presheaf.map (homOfLE (Proj.basicOpen_mono 𝒜B _ _
          ⟨_, X_eq_mvMapGraded_mul_one (A := A) B i⟩)).op).hom
        ((Proj.awayToSection 𝒜B ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))).hom
          (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a)) := by
    rw [toB, RingHom.comp_apply]
    exact s4
  rw [s5]
  have s6 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection 𝒜B ((ProjSpace.mvMapGraded A B n)
    (MvPolynomial.X i))).hom
          (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a)))
    (ι'.naturality (homOfLE (Proj.basicOpen_mono 𝒜B _ _ ⟨_, X_eq_mvMapGraded_mul_one (A := A) B
      i⟩)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at s6
  rw [s6]
  let V : Z'.Opens :=
    ι' ⁻¹ᵁ Proj.basicOpen 𝒜B ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))
  let t₁ : e ⁻¹ᵁ ProjSpace.pullbackChart ι i ⟶ V :=
    eqToHom (show e ⁻¹ᵁ ProjSpace.pullbackChart ι i = V from
      congrArg (fun f : Z' ⟶ Proj 𝒜A =>
        f ⁻¹ᵁ Proj.basicOpen 𝒜A (MvPolynomial.X i)) hcomp)
  let t₂ : ProjSpace.pullbackChart ι' i ⟶ V :=
    (TopologicalSpace.Opens.map ι'.base).map (homOfLE
      (Proj.basicOpen_mono 𝒜B _ _ ⟨_, X_eq_mvMapGraded_mul_one (A := A) B i⟩))
  have hres :
      Z'.presheaf.map t₁.op ≫ Z'.presheaf.map (homOfLE h₁).op =
        Z'.presheaf.map t₂.op ≫ Z'.presheaf.map (homOfLE h₂).op := by
    calc
      _ = Z'.presheaf.map (t₁.op ≫ (homOfLE h₁).op) :=
        (Z'.presheaf.map_comp t₁.op (homOfLE h₁).op).symm
      _ = Z'.presheaf.map (t₂.op ≫ (homOfLE h₂).op) :=
        congrArg (fun f : Opposite.op V ⟶ Opposite.op W' => Z'.presheaf.map f)
          (Subsingleton.elim _ _)
      _ = _ := Z'.presheaf.map_comp t₂.op (homOfLE h₂).op
  exact congrArg (fun ψ : Γ(Z', V) ⟶ Γ(Z', W') =>
    ψ.hom ((ι'.app (Proj.basicOpen 𝒜B
      ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i)))).hom
        ((Proj.awayToSection 𝒜B ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))).hom
          (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a)))) hres

omit [IsAffineHom ι] [IsAffineHom ι'] in
/-- The chart-section square preserves the original transition units. -/
theorem restrictFun_app_frameUnit (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (i j : Fin (n + 1))
  {W' : Z'.Opens}
    (h₁ : W' ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i) (h₂ : W' ≤ ProjSpace.pullbackChart ι' i) :
    ProjSpace.restrictFun h₁ ((e.app (ProjSpace.pullbackChart ι i)).hom (ProjSpace.frameUnit ι i j))
      = ProjSpace.restrictFun h₂ (ProjSpace.frameUnit ι' i j) := by
  rw [ProjSpace.frameUnit, ProjSpace.frameUnit, restrictFun_app_pullAway ι B ι' e hcomp i _ h₁ h₂,
    toB_ratio]

/-- Pulling back sections commutes with the two specified restrictions. -/
theorem restrictFun_app_eq {U V : Z.Opens} (hVU : V ≤ U) {W' : Z'.Opens} (h₁ : W' ≤ e ⁻¹ᵁ V) (h₂ :
  W' ≤ e ⁻¹ᵁ U)
    (x : Γ(Z, U)) :
    ProjSpace.restrictFun h₁ ((e.app V).hom (ProjSpace.restrictFun hVU x)) = ProjSpace.restrictFun
      h₂ ((e.app U).hom x) := by
  have := congrArg (fun ψ => ψ.hom x) (e.naturality (homOfLE hVU).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  erw [this]
  change (Z'.presheaf.map _ ≫ Z'.presheaf.map _).hom _ = (Z'.presheaf.map _).hom _
  rw [← Functor.map_comp]
  rfl

/-- The localization map sends a homogeneous numerator to its coefficient image. -/
theorem toB_mk (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ 𝒜A d) :
    toB (A := A) B i (HomogeneousLocalization.mk
      ({ deg := d, num := ⟨F, hF⟩,
         den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
           (MvPolynomial.isHomogeneous_X_pow i d)⟩,
         den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜A (Submonoid.powers (MvPolynomial.X i))))
    = HomogeneousLocalization.mk
      ({ deg := d,
         num := ⟨MvPolynomial.map (algebraMap A B) F,
           ((MvPolynomial.mem_homogeneousSubmodule d F).mp hF).map _⟩,
         den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
           (MvPolynomial.isHomogeneous_X_pow i d)⟩,
         den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜B (Submonoid.powers (MvPolynomial.X i))) := by
  have step : Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) (HomogeneousLocalization.mk
      ({ deg := d, num := ⟨F, hF⟩,
         den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
           (MvPolynomial.isHomogeneous_X_pow i d)⟩,
         den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜A (Submonoid.powers (MvPolynomial.X i))))
      = HomogeneousLocalization.mk
        ({ deg := d, num := ⟨(ProjSpace.mvMapGraded A B n) F, Graded.map_mem _ hF⟩,
           den := ⟨(ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) ^ d, by
             rw [ProjSpace.mvMapGraded_X]
             exact (MvPolynomial.mem_homogeneousSubmodule d _).mpr
               (MvPolynomial.isHomogeneous_X_pow i d)⟩,
           den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜B (Submonoid.powers ((ProjSpace.mvMapGraded A B
             n) (MvPolynomial.X i)))) := by
    apply HomogeneousLocalization.val_injective
    rw [Away.map, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [map_pow]⟩
  apply HomogeneousLocalization.val_injective
  rw [toB, RingHom.comp_apply, step, val_awayMap_mk, HomogeneousLocalization.val_mk]
  simp only [one_pow, mul_one]
  rfl

/-- The numerator formula expressed using an IsHomogeneous proof. -/
theorem toB_mkDeg (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF :
  F.IsHomogeneous d) :
    toB (A := A) B i (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ } : Away 𝒜A (MvPolynomial.X i)) =
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨MvPolynomial.map (algebraMap A B) F,
            (MvPolynomial.mem_homogeneousSubmodule d _).mpr (hF.map (algebraMap A B))⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ } : Away 𝒜B (MvPolynomial.X i)) := by
  exact toB_mk (A := A) B i d F ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF)

end AlgebraicGeometry.ProjSpace.ChartSectionsBaseChange
